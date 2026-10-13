# Pyrosome artifact: VM guide

The VM is an x86_64 NixOS system with Rocq 9.1 and its Stdlib, and a small
Xfce desktop with Emacs and Proof General. The sources are in `~/pyrosome`,
with the `coqutil` and `canonical-binary-tries` dependencies already included.

- Login: user `artifact`, password `artifact`. Both the desktop and the
  console log in automatically, and `sudo` does not ask for a password.
- Resources: allocate at least 8 GB RAM and 4 cores. The disk grows as
  needed, up to 20 GB.

## Booting

**QEMU** (`pyrosome-artifact.qcow2`):

    ./run-qemu.sh pyrosome-artifact.qcow2

The desktop opens in a window, and a text console runs in the terminal; press
`Ctrl-a x` there to quit. With `NOGRAPHIC=1 ./run-qemu.sh ...` you get only
the console. You can also log in over SSH from another terminal with
`ssh -p 2222 artifact@localhost`.

**VirtualBox** (`pyrosome-artifact.ova`): use *File > Import Appliance*, then
start the VM. SSH is forwarded to host port 2222, as with QEMU.

## Checking the proofs

    cd ~/pyrosome
    make -j4

This takes about 45 minutes with 4 cores. If the build finishes with exit
status 0, every proof in `src/` has been checked. `README.md` describes how
the sources are organized.

To step through a proof interactively, use the terminal that opens on the
desktop at login and run `emacs` on a file, e.g.
`emacs src/Pyrosome/Theory/Core.v &`. Proof General needs the generated
`_CoqProject` and compiled dependencies, so run `make` first.

## Rebuilding the image (optional)

On a machine with Nix and flakes enabled, from the repository root:

    artifact/build-vm.sh qemu         # or: virtualbox

This writes the image to `artifact/out/`, along with this guide and
`run-qemu.sh`. Running `nix build .#proofs` checks the proofs without a VM.
