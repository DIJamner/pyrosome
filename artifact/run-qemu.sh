#!/usr/bin/env bash
# Boot the QEMU image: the desktop opens in a window, and a text console runs
# in this terminal (exit with Ctrl-a x). Set NOGRAPHIC=1 for the console only.
# SSH is forwarded: ssh -p 2222 artifact@localhost
set -euo pipefail
img=${1:-$(dirname "$0")/pyrosome-artifact.qcow2}
if [ -n "${NOGRAPHIC:-}" ]; then
  display=(-display none)
else
  display=(-vga none -device "virtio-vga,xres=1920,yres=1080")
fi
exec qemu-system-x86_64 -accel kvm -accel hvf -accel tcg \
  -m 8G -smp 4 -drive "file=$img,if=virtio" \
  -nic user,model=virtio-net-pci,hostfwd=tcp:127.0.0.1:2222-:22 \
  "${display[@]}" -serial mon:stdio
