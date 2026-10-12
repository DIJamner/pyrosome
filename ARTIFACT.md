# Pyrosome artifact: VM guide

The VM is a console-only x86_64 NixOS system with Rocq 9.1 and its Stdlib
installed. The sources are in `~/pyrosome`, with the `coqutil` and
`canonical-binary-tries` dependencies already included.

- Login: user `artifact`, password `artifact`. The console logs in
  automatically, and `sudo` does not ask for a password.
- Resources: allocate at least 8 GB RAM and 4 cores. The disk grows as
  needed, up to 20 GB.

## Booting

**QEMU** (`pyrosome-artifact.qcow2`):

    ./run-qemu.sh pyrosome-artifact.qcow2

The VM runs in the terminal. Press `Ctrl-a x` to quit. You can also log in
over SSH from another terminal with `ssh -p 2222 artifact@localhost`.

**VirtualBox** (`pyrosome-artifact.ova`): use *File > Import Appliance*, then
start the VM. SSH is forwarded to host port 2222, as with QEMU.

## Checking the proofs

    cd ~/pyrosome
    make -j4

This takes about 45 minutes with 4 cores. If the build finishes with exit
status 0, every proof in `src/` has been checked. `README.md` describes how the sources are organized.

## Rebuilding the image (optional)

On a machine with Nix and flakes enabled, from the repository root:

    artifact/build-vm.sh qemu         # or: virtualbox

This writes the image to `artifact/out/`, along with this guide and
`run-qemu.sh`. Running `nix build .#proofs` checks the proofs without a VM.
