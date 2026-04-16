use aes::Aes256;
use anyhow::{Context, Result};
use argon2::{Algorithm, Argon2, Params, Version};
use cbc::cipher::{BlockDecryptMut, BlockEncryptMut, KeyIvInit, block_padding::Pkcs7};
use chrono::Utc;
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode, enable_raw_mode},
};
use rand::{RngCore, rngs::OsRng};
use ratatui::{prelude::*, widgets::*};
use sha3::{Digest as Sha3Digest, Sha3_512};
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;
use std::time::{Duration, Instant};
use walkdir::WalkDir;

const ARGON_MEM_COST: u32 = 128 * 1024;
const ARGON_TIME_COST: u32 = 4;
const ARGON_LANES: u32 = 1;
const SALT_LEN: usize = 16;
const IV_LEN: usize = 16;
const DB_FILENAME: &str = "hashes.db";
const UUID_FILENAME: &str = "uuid.aes";

type Aes256CbcEnc = cbc::Encryptor<Aes256>;
type Aes256CbcDec = cbc::Decryptor<Aes256>;

#[derive(Clone, PartialEq)]
enum AppMode {
    Dashboard,
    Manage,
}

#[derive(Clone, Copy, PartialEq)]
struct ProgressStats {
    percent: f64,
    current_mb: f64,
    total_mb: f64,
    speed_mb_s: f64,
}

#[derive(Clone)]
struct DeviceResult {
    uuid: String,
    status: DeviceStatus,
    hash: String,
    timestamp: String,
}

#[derive(Clone, PartialEq)]
enum DeviceStatus {
    Pending,
    Hashing(ProgressStats),
    Valid,
    Invalid,
    New,
    Error(String),
}

#[derive(Clone, Debug, PartialEq)]
struct SystemBlockDevice {
    name: String,
    uuid: String,
    size: String,
    label: String,
    is_tracked: bool,
    is_plugged: bool,
}

enum WorkerMessage {
    Progress(String, ProgressStats),
    Result(String, String),
    Error(String, String),
    AllFinished,
}

fn main() -> Result<()> {
    run_tui_app()
}

fn run_tui_app() -> Result<()> {
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let mut mode = AppMode::Dashboard;
    let mut password = String::new();
    let mut unlocked = false;
    let mut status_msg: String = String::new();
    let mut status_color = Color::Gray;

    let mut results: Vec<DeviceResult> = Vec::new();
    let mut db_map: HashMap<String, (String, String)> = HashMap::new();

    let mut manage_list: Vec<SystemBlockDevice> = Vec::new();
    let mut manage_state = ListState::default();

    let (tx, rx): (Sender<WorkerMessage>, Receiver<WorkerMessage>) = mpsc::channel();
    let mut is_verifying = false;

    loop {
        terminal.draw(|f| {
            if !unlocked {
                draw_login(f, &password, &status_msg, status_color);
            } else {
                match mode {
                    AppMode::Dashboard => draw_dashboard(f, &results, &status_msg),
                    AppMode::Manage => draw_management(f, &manage_list, &mut manage_state),
                }
            }
        })?;

        while let Ok(msg) = rx.try_recv() {
            match msg {
                WorkerMessage::Progress(uuid, stats) => {
                    if let Some(res) = results.iter_mut().find(|r| r.uuid == uuid) {
                        res.status = DeviceStatus::Hashing(stats);
                    }
                }
                WorkerMessage::Error(uuid, err_str) => {
                    if let Some(res) = results.iter_mut().find(|r| r.uuid == uuid) {
                        res.status = DeviceStatus::Error(err_str);
                    }
                }
                WorkerMessage::Result(uuid, new_hash) => {
                    let now = Utc::now().to_rfc3339();
                    if let Some(res) = results.iter_mut().find(|r| r.uuid == uuid) {
                        if let Some((old_hash, _)) = db_map.get(&uuid) {
                            if *old_hash == new_hash {
                                res.status = DeviceStatus::Valid;
                            } else {
                                res.status = DeviceStatus::Invalid;
                            }
                        } else {
                            res.status = DeviceStatus::New;
                        }
                        res.hash = new_hash.clone();
                        res.timestamp = now.clone();
                        db_map.insert(uuid.clone(), (new_hash, now));
                    }
                }
                WorkerMessage::AllFinished => {
                    is_verifying = false;
                    match save_encrypted_db(&db_map, &password) {
                        Ok(_) => status_msg = "Verification Complete. DB Saved.".to_string(),
                        Err(e) => {
                            status_msg = format!("Error saving DB: {}", e);
                            status_color = Color::Red;
                        }
                    }
                }
            }
        }

        if event::poll(Duration::from_millis(50))? {
            if let Event::Key(key) = event::read()? {
                if !unlocked {
                    match key.code {
                        KeyCode::Enter => {
                            status_msg = "Decrypting...".to_string();
                            status_color = Color::Yellow;
                            terminal
                                .draw(|f| draw_login(f, &password, &status_msg, status_color))?;

                            match perform_unlock_and_load(&password) {
                                Ok((loaded_uuids, loaded_db, warning)) => {
                                    unlocked = true;
                                    db_map = loaded_db;
                                    results = rebuild_results(&loaded_uuids, &db_map);

                                    if let Some(w) = warning {
                                        status_msg = w;
                                        status_color = Color::Yellow;
                                    } else {
                                        if Path::new(UUID_FILENAME).exists() {
                                            status_msg = "Ready.".to_string();
                                        } else {
                                            status_msg =
                                                "New Session. Press 'm' to add UUIDs.".to_string();
                                        }
                                        status_color = Color::Green;
                                    }
                                }
                                Err(e) => {
                                    status_msg = format!("Failed: {}", e);
                                    status_color = Color::Red;
                                    password.clear();
                                }
                            }
                        }
                        KeyCode::Char(c) => password.push(c),
                        KeyCode::Backspace => {
                            password.pop();
                        }
                        KeyCode::Esc => break,
                        _ => {}
                    }
                } else {
                    match mode {
                        AppMode::Dashboard => match key.code {
                            KeyCode::Char('q') | KeyCode::Esc => {
                                if is_verifying {
                                    status_msg = "Hashing in progress...".to_string();
                                    status_color = Color::Red;
                                } else {
                                    break;
                                }
                            }
                            KeyCode::Char('v') => {
                                if !is_verifying {
                                    is_verifying = true;
                                    status_msg = "Starting verification...".to_string();
                                    let tx_clone = tx.clone();
                                    let targets: Vec<String> =
                                        results.iter().map(|r| r.uuid.clone()).collect();
                                    thread::spawn(move || {
                                        run_hashing_worker(targets, tx_clone);
                                    });
                                }
                            }
                            KeyCode::Char('m') => {
                                if !is_verifying {
                                    mode = AppMode::Manage;
                                    let current_uuids: HashSet<String> =
                                        results.iter().map(|r| r.uuid.clone()).collect();
                                    manage_list = fetch_management_list(&current_uuids);
                                    manage_state.select(Some(0));
                                }
                            }
                            _ => {}
                        },
                        AppMode::Manage => match key.code {
                            KeyCode::Esc | KeyCode::Char('q') => {
                                let tracked_uuids: Vec<String> = manage_list
                                    .iter()
                                    .filter(|d| d.is_tracked)
                                    .map(|d| d.uuid.clone())
                                    .collect();

                                db_map.retain(|k, _| tracked_uuids.contains(k));

                                let content = tracked_uuids.join("\n");
                                if let Err(e) = save_to_encrypted_file(
                                    UUID_FILENAME,
                                    content.as_bytes(),
                                    &password,
                                ) {
                                    status_msg = format!("Error saving UUIDs: {}", e);
                                    status_color = Color::Red;
                                } else {
                                    if let Err(e) = save_encrypted_db(&db_map, &password) {
                                        status_msg = format!("Error saving DB: {}", e);
                                        status_color = Color::Red;
                                    } else {
                                        status_msg = "List Updated & DB Pruned.".to_string();
                                        status_color = Color::Green;
                                    }

                                    results = rebuild_results(&tracked_uuids, &db_map);
                                }
                                mode = AppMode::Dashboard;
                            }
                            KeyCode::Down => {
                                let i = match manage_state.selected() {
                                    Some(i) => {
                                        if i >= manage_list.len() - 1 {
                                            0
                                        } else {
                                            i + 1
                                        }
                                    }
                                    None => 0,
                                };
                                manage_state.select(Some(i));
                            }
                            KeyCode::Up => {
                                let i = match manage_state.selected() {
                                    Some(i) => {
                                        if i == 0 {
                                            manage_list.len() - 1
                                        } else {
                                            i - 1
                                        }
                                    }
                                    None => 0,
                                };
                                manage_state.select(Some(i));
                            }
                            KeyCode::Enter | KeyCode::Char(' ') => {
                                if let Some(i) = manage_state.selected() {
                                    if i < manage_list.len() {
                                        manage_list[i].is_tracked = !manage_list[i].is_tracked;
                                    }
                                }
                            }
                            _ => {}
                        },
                    }
                }
            }
        }
    }

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;
    Ok(())
}

fn rebuild_results(
    uuids: &[String],
    db_map: &HashMap<String, (String, String)>,
) -> Vec<DeviceResult> {
    uuids
        .iter()
        .map(|u| {
            let (stored_hash, stored_time) = db_map
                .get(u)
                .cloned()
                .unwrap_or((String::new(), String::new()));

            DeviceResult {
                uuid: u.clone(),
                status: DeviceStatus::Pending,
                hash: stored_hash,
                timestamp: stored_time,
            }
        })
        .collect()
}

fn fetch_management_list(currently_tracked: &HashSet<String>) -> Vec<SystemBlockDevice> {
    let mut list = Vec::new();
    let output = Command::new("lsblk")
        .args(&["-P", "-o", "NAME,UUID,SIZE,LABEL"])
        .output();
    let mut found_uuids = HashSet::new();

    if let Ok(out) = output {
        let stdout = String::from_utf8_lossy(&out.stdout);
        for line in stdout.lines() {
            let props = parse_lsblk_pair(line);
            if let Some(uuid) = props.get("UUID") {
                if !uuid.is_empty() {
                    found_uuids.insert(uuid.clone());
                    list.push(SystemBlockDevice {
                        name: props.get("NAME").cloned().unwrap_or_default(),
                        uuid: uuid.clone(),
                        size: props.get("SIZE").cloned().unwrap_or_default(),
                        label: props.get("LABEL").cloned().unwrap_or_default(),
                        is_tracked: currently_tracked.contains(uuid),
                        is_plugged: true,
                    });
                }
            }
        }
    }

    for tracked in currently_tracked {
        if !found_uuids.contains(tracked) {
            list.push(SystemBlockDevice {
                name: "OFFLINE".to_string(),
                uuid: tracked.clone(),
                size: "-".to_string(),
                label: "-".to_string(),
                is_tracked: true,
                is_plugged: false,
            });
        }
    }
    list.sort_by(|a, b| b.is_plugged.cmp(&a.is_plugged).then(a.name.cmp(&b.name)));
    list
}

fn parse_lsblk_pair(line: &str) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let parts: Vec<&str> = line.split('"').collect();
    for i in (0..parts.len()).step_by(2) {
        if i + 1 < parts.len() {
            let key = parts[i].trim().trim_end_matches('=').trim();
            let val = parts[i + 1];
            if !key.is_empty() {
                map.insert(key.to_string(), val.to_string());
            }
        }
    }
    map
}

fn draw_management(f: &mut Frame, items: &[SystemBlockDevice], state: &mut ListState) {
    let size = f.size();
    let main_block = Block::default()
        .borders(Borders::ALL)
        .title(" MANAGER: [Enter] Toggle Tracking  [Esc] Save & Back ")
        .style(Style::default().fg(Color::Cyan));

    let list_items: Vec<ListItem> = items
        .iter()
        .map(|dev| {
            let checkbox = if dev.is_tracked { "[x]" } else { "[ ]" };
            let status = if dev.is_plugged { "ONLINE" } else { "OFFLINE" };
            let color = if dev.is_tracked {
                Color::Green
            } else {
                Color::White
            };
            let status_style = if dev.is_plugged {
                Style::default().fg(Color::White)
            } else {
                Style::default().fg(Color::Red)
            };

            let line = Line::from(vec![
                Span::styled(format!("{} ", checkbox), Style::default().fg(Color::Yellow)),
                Span::styled(format!("{: <38} ", dev.uuid), Style::default().fg(color)),
                Span::raw(format!("{: <10} ", dev.name)),
                Span::raw(format!("{: <8} ", dev.size)),
                Span::styled(
                    format!("{: <10} ", dev.label),
                    Style::default().fg(Color::Cyan),
                ),
                Span::styled(format!("({})", status), status_style),
            ]);

            ListItem::new(line)
        })
        .collect();

    let list = List::new(list_items)
        .block(main_block)
        .highlight_style(Style::default().add_modifier(Modifier::REVERSED))
        .highlight_symbol("> ");

    f.render_stateful_widget(list, size, state);
}

fn draw_login(f: &mut Frame, password: &str, status: &str, status_color: Color) {
    let size = f.size();
    let block = Block::default()
        .borders(Borders::ALL)
        .title(" LOGIN / SETUP ")
        .border_style(Style::default().fg(Color::Cyan));
    let area = centered_rect(60, 20, size);
    f.render_widget(Clear, area);
    f.render_widget(block, area);

    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([Constraint::Length(3), Constraint::Length(3)].as_ref())
        .split(area);

    let pass_stars: String = "*".repeat(password.len());
    f.render_widget(
        Paragraph::new(pass_stars)
            .style(Style::default().fg(Color::Yellow))
            .block(
                Block::default()
                    .borders(Borders::ALL)
                    .title(" Enter Password "),
            ),
        chunks[0],
    );

    f.render_widget(
        Paragraph::new(status)
            .style(Style::default().fg(status_color))
            .alignment(Alignment::Center),
        chunks[1],
    );
}

fn draw_dashboard(f: &mut Frame, results: &[DeviceResult], status: &str) {
    let size = f.size();
    let main_block = Block::default()
        .borders(Borders::ALL)
        .title(" EFISIGNER DASHBOARD - [V]erify  [M]anage  [Q]uit ")
        .style(Style::default().fg(Color::White));
    f.render_widget(main_block, size);

    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([Constraint::Min(0), Constraint::Length(1)].as_ref())
        .split(size);

    let rows: Vec<Row> = results
        .iter()
        .map(|res| {
            let (status_str, color) = match &res.status {
                DeviceStatus::Pending => ("PENDING".to_string(), Color::DarkGray),
                DeviceStatus::Hashing(_) => ("HASHING".to_string(), Color::Yellow),
                DeviceStatus::Valid => ("MATCH".to_string(), Color::Green),
                DeviceStatus::Invalid => ("NO MATCH".to_string(), Color::Red),
                DeviceStatus::New => ("NEW ENTRY".to_string(), Color::Cyan),
                DeviceStatus::Error(_) => ("ERROR".to_string(), Color::Magenta),
            };

            let info_col = match &res.status {
                DeviceStatus::Hashing(stats) => {
                    format!(
                        "{:.0}%  {:.0}/{:.0} MB  {:.1} MB/s",
                        stats.percent * 100.0,
                        stats.current_mb,
                        stats.total_mb,
                        stats.speed_mb_s
                    )
                }
                DeviceStatus::Error(e) => format!("ERR: {}", e),
                _ => {
                    if res.hash.is_empty() {
                        "---".to_string()
                    } else {
                        res.hash.chars().take(8).collect::<String>() + "..."
                    }
                }
            };

            let time_display = if res.timestamp.is_empty() {
                "---".to_string()
            } else {
                res.timestamp.clone()
            };

            Row::new(vec![
                Cell::from(res.uuid.clone()),
                Cell::from(status_str).style(Style::default().fg(color)),
                Cell::from(info_col),
                Cell::from(time_display),
            ])
        })
        .collect();

    let table = Table::new(
        rows,
        [
            Constraint::Length(38),
            Constraint::Length(12),
            Constraint::Length(45),
            Constraint::Length(30),
        ],
    )
    .header(
        Row::new(vec!["UUID", "STATUS", "HASH / PROGRESS", "LAST CHECKED"])
            .style(Style::default().fg(Color::Cyan)),
    )
    .block(Block::default().borders(Borders::NONE));

    f.render_widget(table, chunks[0]);
    f.render_widget(
        Paragraph::new(status).style(Style::default().fg(Color::DarkGray)),
        chunks[1],
    );
}

fn centered_rect(percent_x: u16, percent_y: u16, r: Rect) -> Rect {
    let popup_layout = Layout::default()
        .direction(Direction::Vertical)
        .constraints(
            [
                Constraint::Percentage((100 - percent_y) / 2),
                Constraint::Percentage(percent_y),
                Constraint::Percentage((100 - percent_y) / 2),
            ]
            .as_ref(),
        )
        .split(r);
    Layout::default()
        .direction(Direction::Horizontal)
        .constraints(
            [
                Constraint::Percentage((100 - percent_x) / 2),
                Constraint::Percentage(percent_x),
                Constraint::Percentage((100 - percent_x) / 2),
            ]
            .as_ref(),
        )
        .split(popup_layout[1])[1]
}

fn run_hashing_worker(uuids: Vec<String>, tx: Sender<WorkerMessage>) {
    for uuid in uuids {
        let device_path = match find_device_path(&uuid) {
            Ok(p) => p,
            Err(e) => {
                let _ = tx.send(WorkerMessage::Error(uuid.clone(), e.to_string()));
                continue;
            }
        };

        // Create a temporary mount point
        let mount_dir = format!("/tmp/bootwarden_{}", uuid.replace('-', "_"));
        if let Err(e) = fs::create_dir_all(&mount_dir) {
            let _ = tx.send(WorkerMessage::Error(uuid.clone(), format!("mkdir: {}", e)));
            continue;
        }

        // Mount read-only so we don't alter anything
        let mount_res = Command::new("mount")
            .args(&["-o", "ro", device_path.to_str().unwrap_or(""), &mount_dir])
            .output();

        let already_mounted;
        match mount_res {
            Ok(out) if out.status.success() => {
                already_mounted = false;
            }
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                // Check if already mounted
                if stderr.contains("already mounted") {
                    already_mounted = true;
                } else {
                    let _ = tx.send(WorkerMessage::Error(
                        uuid.clone(),
                        format!("mount failed: {}", stderr.trim()),
                    ));
                    let _ = fs::remove_dir(&mount_dir);
                    continue;
                }
            }
            Err(e) => {
                let _ = tx.send(WorkerMessage::Error(
                    uuid.clone(),
                    format!("mount exec: {}", e),
                ));
                let _ = fs::remove_dir(&mount_dir);
                continue;
            }
        }

        let hash_result =
            compute_hash_from_mounted_fs(&mount_dir, &uuid, &tx);

        // Unmount only if we mounted it
        if !already_mounted {
            let _ = Command::new("umount").arg(&mount_dir).output();
            let _ = fs::remove_dir(&mount_dir);
        }

        match hash_result {
            Ok(hash) => {
                let _ = tx.send(WorkerMessage::Result(uuid, hash));
            }
            Err(e) => {
                let _ = tx.send(WorkerMessage::Error(uuid, e.to_string()));
            }
        }
    }
    let _ = tx.send(WorkerMessage::AllFinished);
}

/// Collect all regular files under the mount point, sort them by their
/// relative path, then hash (relative_path || file_contents) for each one.
/// This is deterministic across reboots because:
///   - We only hash actual file data (not free space, journal, timestamps)
///   - Sorting by path ensures order is consistent
///   - Any evil-maid modification to bootloader/kernel/initramfs changes the hash
fn compute_hash_from_mounted_fs(
    mount_dir: &str,
    uuid: &str,
    tx: &Sender<WorkerMessage>,
) -> Result<String> {
    // Phase 1: collect and sort all file paths
    let mount_path = Path::new(mount_dir);
    let mut file_entries: Vec<PathBuf> = Vec::new();

    for entry in WalkDir::new(mount_dir).follow_links(false).into_iter() {
        match entry {
            Ok(e) => {
                if e.file_type().is_file() {
                    file_entries.push(e.into_path());
                }
            }
            Err(_) => continue, // skip unreadable entries
        }
    }

    // Sort by relative path for deterministic ordering
    file_entries.sort_by(|a, b| {
        let ra = a.strip_prefix(mount_path).unwrap_or(a);
        let rb = b.strip_prefix(mount_path).unwrap_or(b);
        ra.cmp(rb)
    });

    // Phase 2: compute total size for progress reporting
    let total_bytes: u64 = file_entries
        .iter()
        .filter_map(|p| p.metadata().ok())
        .map(|m| m.len())
        .sum();

    // Phase 3: hash all files
    let mut hasher = Sha3_512::new();
    let mut total_read: u64 = 0;
    let start_time = Instant::now();
    let mut last_update = Instant::now();
    let buf_size = 1024 * 1024;
    let mut buffer = vec![0u8; buf_size];

    for path in &file_entries {
        // Hash the relative path so that renaming a file changes the hash
        let rel_path = path
            .strip_prefix(mount_path)
            .unwrap_or(path)
            .to_string_lossy();
        hasher.update(rel_path.as_bytes());
        // Separator so path and content don't bleed into each other
        hasher.update(b"\x00");

        let mut file = match File::open(path) {
            Ok(f) => f,
            Err(_) => continue, // skip unreadable files
        };

        loop {
            let n = file.read(&mut buffer)?;
            if n == 0 {
                break;
            }
            hasher.update(&buffer[..n]);
            total_read += n as u64;

            if last_update.elapsed().as_millis() > 100 {
                let elapsed_sec = start_time.elapsed().as_secs_f64().max(0.001);
                let stats = ProgressStats {
                    percent: if total_bytes > 0 {
                        total_read as f64 / total_bytes as f64
                    } else {
                        0.0
                    },
                    current_mb: total_read as f64 / 1_048_576.0,
                    total_mb: total_bytes as f64 / 1_048_576.0,
                    speed_mb_s: (total_read as f64 / 1_048_576.0) / elapsed_sec,
                };
                let _ = tx.send(WorkerMessage::Progress(uuid.to_string(), stats));
                last_update = Instant::now();
            }
        }
    }

    let elapsed_sec = start_time.elapsed().as_secs_f64().max(0.001);
    let final_stats = ProgressStats {
        percent: 1.0,
        current_mb: total_bytes as f64 / 1_048_576.0,
        total_mb: total_bytes as f64 / 1_048_576.0,
        speed_mb_s: (total_bytes as f64 / 1_048_576.0) / elapsed_sec,
    };
    let _ = tx.send(WorkerMessage::Progress(uuid.to_string(), final_stats));
    Ok(hex::encode(hasher.finalize()))
}

fn perform_unlock_and_load(
    password: &str,
) -> Result<(
    Vec<String>,
    HashMap<String, (String, String)>,
    Option<String>,
)> {
    if !Path::new(UUID_FILENAME).exists() {
        return Ok((Vec::new(), HashMap::new(), None));
    }

    let uuids_bytes = load_encrypted_file(UUID_FILENAME, password)
        .context("Invalid Password or Corrupt UUID file")?;
    let uuid_list: Vec<String> = String::from_utf8(uuids_bytes)?
        .lines()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();

    let mut db_map = HashMap::new();
    let mut warning = None;

    if Path::new(DB_FILENAME).exists() {
        match load_encrypted_file(DB_FILENAME, password) {
            Ok(bytes) => {
                let content = String::from_utf8(bytes)?;
                for line in content.lines() {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if parts.len() >= 3 {
                        db_map.insert(
                            parts[0].to_string(),
                            (parts[1].to_string(), parts[2].to_string()),
                        );
                    }
                }
            }
            Err(_) => {
                warning = Some("Pass changed. DB Reset.".to_string());
                let _ = std::fs::rename(DB_FILENAME, format!("{}.bak", DB_FILENAME));
            }
        }
    }
    Ok((uuid_list, db_map, warning))
}

fn load_encrypted_file(path: &str, password: &str) -> Result<Vec<u8>> {
    let data = std::fs::read(path)?;
    if data.len() < SALT_LEN + IV_LEN {
        return Err(anyhow::anyhow!("File too short"));
    }
    let (salt, rest) = data.split_at(SALT_LEN);
    let (iv, ciphertext) = rest.split_at(IV_LEN);
    let key = derive_key(password, salt)?;
    let cipher = Aes256CbcDec::new(&key.into(), iv.into());
    let mut buf = ciphertext.to_vec();
    let plaintext = cipher
        .decrypt_padded_mut::<Pkcs7>(&mut buf)
        .map_err(|_| anyhow::anyhow!("Decryption Error"))?;
    Ok(plaintext.to_vec())
}

fn save_to_encrypted_file(path: &str, data: &[u8], password: &str) -> Result<()> {
    let mut salt = [0u8; SALT_LEN];
    let mut iv = [0u8; IV_LEN];
    OsRng.fill_bytes(&mut salt);
    OsRng.fill_bytes(&mut iv);
    let key = derive_key(password, &salt)?;
    let cipher = Aes256CbcEnc::new(&key.into(), &iv.into());
    let mut buf = vec![0u8; data.len() + 16];
    buf[..data.len()].copy_from_slice(data);
    let ciphertext = cipher
        .encrypt_padded_mut::<Pkcs7>(&mut buf, data.len())
        .map_err(|e| anyhow::anyhow!("Encrypt Error: {}", e))?;
    let mut file = File::create(path)?;
    file.write_all(&salt)?;
    file.write_all(&iv)?;
    file.write_all(ciphertext)?;
    Ok(())
}

fn save_encrypted_db(db: &HashMap<String, (String, String)>, password: &str) -> Result<()> {
    let mut content = String::new();
    for (uuid, (hash, time)) in db {
        content.push_str(&format!("{} {} {}\n", uuid, hash, time));
    }
    save_to_encrypted_file(DB_FILENAME, content.as_bytes(), password)?;
    Ok(())
}

fn derive_key(password: &str, salt: &[u8]) -> Result<[u8; 32]> {
    let mut key = [0u8; 32];
    let params = Params::new(ARGON_MEM_COST, ARGON_TIME_COST, ARGON_LANES, Some(32))
        .map_err(|e| anyhow::anyhow!("{}", e))?;
    let argon2 = Argon2::new(Algorithm::Argon2id, Version::V0x13, params);
    argon2
        .hash_password_into(password.as_bytes(), salt, &mut key)
        .map_err(|e| anyhow::anyhow!("{}", e))?;
    Ok(key)
}

fn find_device_path(uuid: &str) -> Result<PathBuf> {
    let path = Path::new("/dev/disk/by-uuid").join(uuid);
    if !path.exists() {
        return Err(anyhow::anyhow!("UUID Not Found"));
    }
    Ok(std::fs::canonicalize(&path).unwrap_or(path))
}
