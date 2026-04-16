# BootWarden
A minimalist tool to verify the integrity of unencrypted boot partitions in high-risk environments. Mitigates Evil Maid attacks by cryptographically validating the bootloader before the OS loads.

Recommended to install to a lightweight iso such as void Linux with MUSL to carry around a tool to verify the boot partitions. 

Used in environments when putting the boot partition onto a detachable usb is not an option, such as when using Qubes and want to keep the sys-usb functionality.
