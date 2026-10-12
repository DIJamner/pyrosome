{
  description = "Pyrosome POPL artifact: Rocq development + minimal evaluation VM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    # The two git submodules, pinned to the same commits as in this repository.
    coqutil = {
      url = "github:mit-plv/coqutil/f595ddf0de48aae23862dc146928825db960c955";
      flake = false;
    };
    canonical-binary-tries = {
      url = "github:xavierleroy/canonical-binary-tries/60b616370ba29f527bf98b541c232da508492093";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, coqutil, canonical-binary-tries }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      coqPackages = pkgs.coqPackages_9_1;

      # The repository's tracked files with the submodules filled in.
      src = pkgs.runCommand "pyrosome-src" { } ''
        cp -r ${self} $out
        chmod -R u+w $out
        rm -rf $out/coqutil $out/canonical-binary-tries
        cp -r ${coqutil} $out/coqutil
        cp -r ${canonical-binary-tries} $out/canonical-binary-tries
        chmod -R u+w $out
      '';

      vm = nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs = { inherit src coqPackages; };
        modules = [ ./artifact/vm.nix ];
      };
    in
    {
      packages.${system} = {
        inherit src;
        # Checks every proof in src/ (the same `make` the VM's users run).
        proofs = pkgs.stdenv.mkDerivation {
          name = "pyrosome-proofs";
          inherit src;
          nativeBuildInputs = [ coqPackages.coq coqPackages.stdlib ];
          buildPhase = "make -j$NIX_BUILD_CORES";
          installPhase = "touch $out";
        };
        # Compressed copy of the QEMU image, for distribution.
        vm-qemu = pkgs.runCommand "pyrosome-vm-qemu" { nativeBuildInputs = [ pkgs.qemu-utils ]; } ''
          mkdir $out
          qemu-img convert -c -O qcow2 ${vm.config.system.build.images.qemu}/*.qcow2 $out/pyrosome-artifact.qcow2
        '';
        vm-virtualbox = vm.config.system.build.images.virtualbox;
        default = self.packages.${system}.vm-qemu;
      };

      nixosConfigurations.artifact-vm = vm;

      devShells.${system}.default = pkgs.mkShell {
        packages = [ coqPackages.coq coqPackages.stdlib ];
      };
    };
}
