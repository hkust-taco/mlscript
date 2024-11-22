{
  description = "mlscript";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.sbt-deriv.url = "github:zaninime/sbt-derivation";
  inputs.sbt-deriv.inputs.nixpkgs.follows = "nixpkgs";

  outputs = { self, nixpkgs, flake-utils, sbt-deriv }:
    flake-utils.lib.eachDefaultSystem
      (system:
      let 
        sbtOverlay = self: super: {
          sbt = super.sbt.override { jre = super.jdk8_headless; };
        };
        pkgs = import nixpkgs { 
          inherit system;
          overlays = [ sbtOverlay ];
        };
      in with pkgs; {
          devShells.default = mkShell {
            buildInputs = [
              clang
              gcc
              gnumake
              boost
              gmp
              mimalloc
              sbt
              nodejs_22
            ];
          };
      });
}
