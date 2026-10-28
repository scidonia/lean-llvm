{
  description = "lean-llvm — certified LLVM transformations and refinement in Lean 4";

  inputs = {
    # Pinned to the revision the sibling `lean` flake resolved, so the
    # `lean4` derivation below is the one already present in the store rather
    # than a fresh source build.  `nix flake update nixpkgs` advances it.
    nixpkgs.url = "github:NixOS/nixpkgs/151fa4e8ddfdd8dd25d945ad94ed54a13de9f6e4";
  };

  outputs =
    { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (
        pkgs:
        let
          # Lean `v4.35.0-rc3`, the toolchain the Scidonia Lean work targets.
          # The source is fetched rather than resolved by `elan` so that a
          # build needs no network access.
          lean4 = pkgs.lean4.overrideAttrs (prev: {
            version = "4.35.0-rc3";
            src = pkgs.fetchFromGitHub {
              owner = "leanprover";
              repo = "lean4";
              tag = "v4.35.0-rc3";
              hash = "sha256-gVqvQ9fdyCFxMiplNl5fQsw3uc3fPrkO2N3RymVAi7Y=";
            };
            # The tag's own `LEAN_SPECIAL_VERSION_DESC` is empty; the RC tarball
            # was built with `rc3`, and the string is part of the `.olean`
            # format, so every stage must agree on it.
            cmakeFlags = prev.cmakeFlags ++ [ "-DLEAN_SPECIAL_VERSION_DESC=rc3" ];
            # 4.35's CMakeLists declares `lean4lean`, `nanoda` and `con-leche`
            # as `EXCLUDE_FROM_ALL` external projects; CMake still probes for
            # the download tool during configure.
            nativeBuildInputs = prev.nativeBuildInputs ++ [ pkgs.gitMinimal ];
          });
          llvm = pkgs.llvmPackages;
        in
        {
          default = pkgs.mkShell {
            name = "lean-llvm";

            packages = [
              lean4
              pkgs.git
              pkgs.coreutils
              pkgs.file
              pkgs.binutils
              pkgs.gnugrep
              pkgs.gnused
              pkgs.gawk
              pkgs.zstd
              # The IR the driver emits is checked against the real assembler in
              # the verification runs.
              llvm.llvm
              llvm.clang
            ];

            shellHook = ''
              unset -f lake lean
              printf 'lean-llvm: %s\n' "$(lean --version)"
            '';
          };
        }
      );

      packages = forAllSystems (pkgs: {
        default = self.devShells.${pkgs.system}.default;
      });
    };
}
