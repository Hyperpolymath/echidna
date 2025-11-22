{
  description = "ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rustfmt" "clippy" ];
        };

        # Julia with required packages
        julia-with-packages = pkgs.julia.withPackages [
          "Flux"
          "GraphNeuralNetworks"
          "Oxygen"
          "Gen"
          "ReinforcementLearning"
          "MLJ"
        ];

      in
      {
        # Development shell
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Rust toolchain
            rustToolchain
            cargo-watch
            cargo-audit
            cargo-edit

            # Julia
            julia-with-packages

            # Deno for ReScript
            deno

            # Node.js for ReScript tooling
            nodejs_20

            # Build tools
            just
            podman

            # Theorem provers (where available in nixpkgs)
            coq
            lean4
            isabelle
            z3
            cvc5

            # Quality tools
            trivy
            reuse

            # Documentation
            mdbook

            # Development utilities
            git
            gh
            ripgrep
            fd
            jq

            # LSPs and formatters
            rust-analyzer
            nixpkgs-fmt
          ];

          shellHook = ''
            echo "ECHIDNA Development Environment"
            echo "================================"
            echo ""
            echo "Available commands:"
            echo "  just build    - Build all components"
            echo "  just test     - Run all tests"
            echo "  just check    - Run quality checks"
            echo "  just dev      - Start development server"
            echo ""
            echo "Installed provers:"
            which coq >/dev/null && echo "  ✓ Coq $(coqc --version | head -1)"
            which lean >/dev/null && echo "  ✓ Lean $(lean --version)"
            which isabelle >/dev/null && echo "  ✓ Isabelle"
            which z3 >/dev/null && echo "  ✓ Z3 $(z3 --version)"
            which cvc5 >/dev/null && echo "  ✓ CVC5 $(cvc5 --version)"
            echo ""
          '';
        };

        # Build package
        packages.default = pkgs.rustPlatform.buildRustPackage {
          pname = "echidna";
          version = "0.1.0";

          src = ./.;

          cargoLock = {
            lockFile = ./Cargo.lock;
          };

          nativeBuildInputs = with pkgs; [
            rustToolchain
            just
            pkg-config
          ];

          buildInputs = with pkgs; [
            openssl
          ];

          # Run tests
          checkPhase = ''
            cargo test --release
          '';

          # Install
          installPhase = ''
            mkdir -p $out/bin
            cp target/release/echidna $out/bin/
          '';

          meta = with pkgs.lib; {
            description = "Neurosymbolic theorem proving platform";
            homepage = "https://gitlab.com/non-initiate/rhodinised/quill";
            license = with licenses; [ mit /* AND Palimpsest-0.6 */ ];
            maintainers = [];
            platforms = platforms.unix;
          };
        };

        # Apps
        apps.default = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/echidna";
        };

        # Checks (run with `nix flake check`)
        checks = {
          # Format check
          format = pkgs.runCommand "check-format" {
            buildInputs = [ rustToolchain ];
          } ''
            cd ${./.}
            cargo fmt -- --check
            touch $out
          '';

          # Clippy check
          clippy = pkgs.runCommand "check-clippy" {
            buildInputs = [ rustToolchain ];
          } ''
            cd ${./.}
            cargo clippy -- -D warnings
            touch $out
          '';

          # Tests
          test = pkgs.runCommand "run-tests" {
            buildInputs = [ rustToolchain ];
          } ''
            cd ${./.}
            cargo test
            touch $out
          '';
        };
      }
    );
}
