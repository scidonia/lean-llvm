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
          # Lean `v4.36.0-rc1`, the toolchain the Scidonia Lean work targets.
          # The source is fetched rather than resolved by `elan` so that a
          # build needs no network access.
          # 4.36 links cadical into the runtime; point CMake at the packaged
          # build instead of letting it clone from the network in the sandbox.
          cadical = pkgs.cadical.override { version = "2.1.3"; };
          lean4 = pkgs.lean4.overrideAttrs (prev: {
            version = "4.36.0-rc1";
            src = pkgs.fetchFromGitHub {
              owner = "leanprover";
              repo = "lean4";
              tag = "v4.36.0-rc1";
              hash = "sha256-IWQV0m4I9qhREhWCWtnyMtAE5HgRezcSOy+YSr2GxoU=";
            };
            # The tag's own `LEAN_SPECIAL_VERSION_DESC` is empty; the RC tarball
            # was built with `rc1`, and the string is part of the `.olean`
            # format, so every stage must agree on it.
            cmakeFlags = prev.cmakeFlags ++ [
              "-DLEAN_SPECIAL_VERSION_DESC=rc1"
              "-DCADICAL=${cadical}/bin/cadical"
              "-DCADICAL_LIB=${cadical.lib}/lib/libcadical.a"
              "-DCADICAL_INCLUDE_DIR=${cadical.dev}/include"
            ];
            # 4.36's CMakeLists declares `lean4lean`, `nanoda`, `con-leche` and
            # `con-ron` as `EXCLUDE_FROM_ALL` external projects; CMake still
            # probes for the download tool during configure.
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
