#!/usr/bin/env bash
# Build the artifact VM image with Nix.
#   artifact/build-vm.sh [qemu|virtualbox]     (default: qemu)
# Writes the image, plus the guide and the QEMU launcher, to artifact/out/.
# Only files tracked by git are included in the image.
set -euo pipefail
fmt=${1:-qemu}
case $fmt in
  qemu) ext=qcow2 ;;
  virtualbox) ext=ova ;;
  *) echo "usage: $0 [qemu|virtualbox]" >&2; exit 1 ;;
esac
cd "$(dirname "$0")/.."
out=$(nix --extra-experimental-features 'nix-command flakes' \
        build --no-link --print-out-paths ".#vm-$fmt")
mkdir -p artifact/out
install -m 644 "$out"/*."$ext" "artifact/out/pyrosome-artifact.$ext"
install -m 755 artifact/run-qemu.sh artifact/out/
ls -l artifact/out
