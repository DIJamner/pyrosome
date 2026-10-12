#!/usr/bin/env bash
# Boot the QEMU image in this terminal (exit with Ctrl-a x).
# SSH is forwarded: ssh -p 2222 artifact@localhost
set -euo pipefail
img=${1:-$(dirname "$0")/pyrosome-artifact.qcow2}
exec qemu-system-x86_64 -accel kvm -accel hvf -accel tcg \
  -m 8G -smp 4 -drive "file=$img,if=virtio" \
  -nic user,model=virtio-net-pci,hostfwd=tcp:127.0.0.1:2222-:22 -nographic
