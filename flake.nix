{
  description = "An x7 interpreter in Rust";

  inputs = {
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };
  outputs = {
    self,
    fenix,
    nixpkgs,
  }: let
    supportedSystems = nixpkgs.lib.systems.flakeExposed;
    allSystems = output:
      nixpkgs.lib.genAttrs supportedSystems
      (system: output nixpkgs.legacyPackages.${system});
  in {
    packages = allSystems (pkgs: {
      default = pkgs.rustPlatform.buildRustPackage {
        pname = "rx7";
        version = "0.1.0";
        src = self;
        cargoLock.lockFile = ./Cargo.lock;
      };
    });

    devShells = allSystems (pkgs: let
      pkgsFenix = fenix.packages.${pkgs.system};
      stable = pkgsFenix.toolchainOf {
        channel = "1.80.0";
        sha256 = "sha256-6eN/GKzjVSjEhGO9FhWObkRFaE1Jf+uqMSdQnb8lcB4=";
      };
      nightly = pkgsFenix.latest; # If you use multiple nightly components, you may want to change this to `pkgsFenix.complete` to reduce the risk of incompatibility.
      rustPackages = pkgsFenix.combine [
        (stable.withComponents [
          "cargo"
          "clippy"
          "rustc" # includes rust-std
          #"miri"
          #"rust-src" # rust stdlib source code. used by rust-analyzer and miri
        ])
        nightly.rustfmt
      ];
    in {
      default = pkgs.mkShell {
        inherit
          (self.outputs.packages.${pkgs.system}.default)
          nativeBuildInputs
          buildInputs
          ;
        packages = [rustPackages];
        RUST_BACKTRACE = 1;
      };
    });
  };
}
