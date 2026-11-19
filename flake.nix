{
  description = "lean-llvm — certified LLVM transformations and refinement in Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
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
          # The toolchain and mathlib come from nixpkgs' `leanPackages` set, not
          # from Lake's fetch: a checkout elaborates this project's modules and
          # nothing else.  The set's own `lean4` is the one whose Lake treats a
          # `/nix/store` package directory as up to date (`pkgs.lean4` does not
          # carry that patch), and its mathlib is the revision `lakefile.toml`
          # pins, which is tag `v4.35.0` of `leanprover-community/mathlib4`.
          lean = pkgs.leanPackages.lean4;
          mathlib = pkgs.leanPackages.mathlib;
          leanDeps = mathlib.passthru.allLeanDeps;

          # Lake otherwise resolves each manifest entry by fetching it.  These
          # path entries replace every one -- mathlib and the libraries mathlib
          # requires -- with its store package, so no git fetch and no mathlib
          # elaboration happens locally.
          lakePackages = pkgs.writeText "lake-overrides.json" (
            builtins.toJSON {
              schemaVersion = "1.2.0";
              packages = map (dep: {
                type = "path";
                name = dep.passthru.lakePackageName;
                inherited = false;
                dir = "${dep}";
              }) (leanDeps ++ [ mathlib ]);
            }
          );

          # `--packages` is a global Lake option, so one wrapper covers `build`,
          # `exe`, `env` and the rest of the surface the repository uses.
          # `--version` is only accepted as Lake's first argument, so it is
          # forwarded without the override.
          lake = pkgs.writeShellScriptBin "lake" ''
            if [ "''${1-}" = "--version" ]; then
              exec ${lean}/bin/lake "$@"
            fi
            exec ${lean}/bin/lake --packages=${lakePackages} "$@"
          '';

          llvm = pkgs.llvmPackages;
        in
        {
          default = pkgs.mkShell {
            name = "lean-llvm";

            packages = [
              lean
              mathlib
            ]
            ++ leanDeps
            ++ [
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
              # The wrapper takes precedence over the toolchain's own `lake`, and
              # Lake's own caches are off: the store packages are the only source
              # of dependency artifacts.
              export PATH=${lake}/bin:$PATH
              export LAKE_NO_CACHE=1
              export RESERVOIR_API_URL=""
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
