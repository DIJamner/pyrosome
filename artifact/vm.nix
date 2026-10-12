# Minimal console-only NixOS guest for evaluating the artifact.
{ config, lib, pkgs, modulesPath, src, coqPackages, ... }:
{
  imports = [ (modulesPath + "/profiles/minimal.nix") ];

  # Per-format settings.
  image.modules.qemu = {
    imports = [ (modulesPath + "/profiles/qemu-guest.nix") ];
  };
  image.modules.virtualbox = {
    virtualbox = {
      vmName = "Pyrosome artifact";
      memorySize = 8192;
      params.cpus = 4;
      params.natpf1 = "ssh,tcp,127.0.0.1,2222,,22";
    };
  };

  virtualisation.diskSize = 20 * 1024; # MiB; images are sparse, so this is a ceiling

  # Console on both the VGA screen and the serial port (for `qemu -nographic`).
  boot.kernelParams = [ "console=tty0" "console=ttyS0,115200" ];

  networking.hostName = "pyrosome";

  users.users.artifact = {
    isNormalUser = true;
    password = "artifact";
    extraGroups = [ "wheel" ];
  };
  security.sudo.wheelNeedsPassword = false;
  services.getty.autologinUser = "artifact";
  services.openssh = {
    enable = true;
    settings.PasswordAuthentication = true;
  };

  environment.systemPackages = [
    coqPackages.coq
    coqPackages.stdlib
    pkgs.gnumake
  ];
  environment.pathsToLink = [ "/lib/coq" ];
  environment.variables.ROCQPATH =
    "/run/current-system/sw/lib/coq/${coqPackages.coq.coq-version}/user-contrib";

  # Put a writable copy of the sources in the home directory on first boot.
  systemd.services.artifact-sources = {
    wantedBy = [ "multi-user.target" ];
    before = [ "getty@tty1.service" "serial-getty@ttyS0.service" "sshd.service" ];
    unitConfig.ConditionPathExists = "!/home/artifact/pyrosome";
    serviceConfig.Type = "oneshot";
    script = ''
      cp -r ${src} /home/artifact/pyrosome
      chmod -R u+w /home/artifact/pyrosome
      chown -R artifact:users /home/artifact/pyrosome
    '';
  };

  users.motd = ''
    Pyrosome artifact. Sources are in ~/pyrosome; see ~/pyrosome/ARTIFACT.md.
    Build all proofs with:  cd ~/pyrosome && make -j$(nproc)
  '';

  # Keep the image small: no Nix tooling or nixpkgs copy inside the guest.
  nix.enable = false;
  nixpkgs.flake.setNixPath = false;
  nixpkgs.flake.setFlakeRegistry = false;
  system.disableInstallerTools = true;
  environment.defaultPackages = [ ];

  system.stateVersion = "25.11";
}
