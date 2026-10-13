# Small NixOS guest for evaluating the artifact: an Xfce desktop with
# Emacs + Proof General, plus a text console on the serial port.
{ config, lib, pkgs, modulesPath, src, coqPackages, ... }:
let
  # Start the desktop at this resolution, whatever size the hypervisor's window
  # reports, unless the user has saved their own choice in Xfce's Display settings.
  resolution = "1920x1080";
  setResolution = pkgs.writeShellScript "set-resolution" ''
    PATH=${lib.makeBinPath [ pkgs.xorg.xrandr pkgs.libxcvt pkgs.gawk ]}
    [ -e ~/.config/xfce4/xfconf/xfce-perchannel-xml/displays.xml ] && exit 0
    res=${resolution}
    out=$(xrandr | awk '/ connected/ { print $1; exit }')
    [ -n "$out" ] || exit 0
    if ! xrandr --output "$out" --mode "$res"; then
      # Not offered by the display: define it ourselves.
      xrandr --newmode "$res" $(cvt ''${res%x*} ''${res#*x} | awk '/Modeline/ { $1 = $2 = ""; print }')
      xrandr --addmode "$out" "$res"
      xrandr --output "$out" --mode "$res"
    fi
  '';
in
{
  # Per-format settings.
  image.modules.qemu = {
    imports = [ (modulesPath + "/profiles/qemu-guest.nix") ];
  };
  image.modules.virtualbox = {
    # Guest Additions: the desktop resizes with the VirtualBox window.
    virtualisation.virtualbox.guest.enable = true;
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

  # Graphical session: log straight into Xfce, with a terminal open in ~/pyrosome.
  services.xserver = {
    enable = true;
    desktopManager.xfce.enable = true;
  };
  environment.etc."xdg/autostart/pyrosome-terminal.desktop".text = ''
    [Desktop Entry]
    Type=Application
    Name=Pyrosome terminal
    Exec=xfce4-terminal --working-directory=/home/artifact/pyrosome
  '';
  environment.etc."xdg/autostart/pyrosome-resolution.desktop".text = ''
    [Desktop Entry]
    Type=Application
    Name=Default screen resolution
    Exec=${setResolution}
  '';
  # X pulls these in by default; unneeded for Emacs, and ~1.5 GB together.
  hardware.graphics.enable = lib.mkForce false; # Mesa/LLVM; X falls back to software rendering
  services.speechd.enable = false;
  services.displayManager = {
    defaultSession = "xfce";
    autoLogin = {
      enable = true;
      user = "artifact";
    };
  };

  environment.systemPackages = [
    coqPackages.coq
    coqPackages.stdlib
    pkgs.gnumake
    pkgs.xorg.xrandr
    # Native compilation would add gcc and libgccjit to the image.
    ((pkgs.emacsPackagesFor (pkgs.emacs.override { withNativeCompilation = false; })).emacsWithPackages
      (epkgs: [ epkgs.proof-general ]))
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

  # Keep the image small: no docs, Nix tooling or nixpkgs copy inside the guest.
  documentation.enable = false;
  nix.enable = false;
  nixpkgs.flake.setNixPath = false;
  nixpkgs.flake.setFlakeRegistry = false;
  system.disableInstallerTools = true;
  environment.defaultPackages = [ ];

  system.stateVersion = "25.11";
}
