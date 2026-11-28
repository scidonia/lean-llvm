{
  description = "lean-llvm — certified LLVM transformations and refinement in Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      # aarch64-linux is declared so a consumer running on Arm gets a `lake`
      # wrapper built for that architecture. Nothing under it is cached:
      # nixpkgs' Lean packages compile from source there, mathlib included.
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      # The toolchain and mathlib come from nixpkgs' `leanPackages` set, not
      # from Lake's fetch: a checkout elaborates this project's modules and
      # nothing else.  The set's own `lean4` is the one whose Lake treats a
      # `/nix/store` package directory as up to date (`pkgs.lean4` does not
      # carry that patch), and its mathlib is the revision `lakefile.toml`
      # pins, which is tag `v4.35.0` of `leanprover-community/mathlib4`.
      mkLeanEnv =
        pkgs:
        let
          leanPackages = pkgs.leanPackages;
          lean = leanPackages.lean4;
          mathlib = leanPackages.mathlib;
          leanDeps = mathlib.passthru.allLeanDeps;

          # Lake writes the C objects it needs for linking an executable into
          # each package's own `.lake/build/ir`.  A package used straight from
          # the store is read-only, so linking fails with EROFS there; these
          # packages are copied into a writable cache first, under a
          # `$XDG_CACHE_HOME` that belongs to the user rather than to the
          # store.  The copy is a reflink where the filesystem supports one.
          # A store path already materialised is reused, and directories for
          # packages this project no longer uses are pruned.
          allDeps = [ mathlib ] ++ leanDeps;
          overrides = pkgs.writeShellApplication {
            name = "lean-llvm-overrides";
            runtimeInputs = [ pkgs.coreutils pkgs.util-linux ];
            text = ''
              cache="''${XDG_CACHE_HOME:-$HOME/.cache}/lean-llvm/packages"
              mkdir -p "$cache/stamps"
              exec 9>"$cache/.lock"
              flock 9

              keep=" "
              ${lib.concatMapStringsSep "\n" (
                dep:
                let
                  store = "${dep}";
                in
                ''
                  dir="$cache/$(basename "${store}")"
                  keep="$keep $(basename "${store}") "
                  if [ ! -f "$cache/stamps/$(basename "${store}")" ] \
                    || [ "$(cat "$cache/stamps/$(basename "${store}")")" != "${store}" ]; then
                    rm -rf "$dir"
                    cp -r --reflink=auto "${store}" "$dir"
                    chmod -R u+w "$dir"
                    printf '%s\n' "${store}" > "$cache/stamps/$(basename "${store}")"
                  fi
                ''
              ) allDeps}

              # `stamps/` sits inside the cache it records.  Pruning it with the
              # package directories would drop every stamp on each invocation,
              # so the next run would re-copy every package and reset the
              # mtimes Lake's staleness check reads, redoing build work that
              # nothing changed.
              for entry in "$cache"/*/; do
                [ -d "$entry" ] || continue
                case "$(basename "$entry")" in
                  stamps) continue ;;
                esac
                case "$keep" in
                  *" $(basename "$entry") "*) ;;
                  *) rm -rf "$entry" ;;
                esac
              done

              json="$cache/overrides.json"
              tmp="$json.tmp.$$"
              {
                printf '{"schemaVersion":"1.2.0","packages":['
                sep=""
                ${lib.concatMapStringsSep "\n" (
                  dep:
                  let
                    name = dep.passthru.lakePackageName;
                  in
                  ''
                    printf '%s{"type":"path","name":"${name}","inherited":false,"dir":"%s"}' \
                      "$sep" "$cache/$(basename "${dep}")"
                    sep=,
                  ''
                ) allDeps}
                printf ']}'
              } > "$tmp"
              mv "$tmp" "$json"
              printf '%s\n' "$json"
            '';
          };

          # `--packages` is a global Lake option, so one wrapper covers `build`,
          # `exe`, `env` and the rest of the surface the repository uses.
          # `--version` is only accepted as Lake's first argument, so it is
          # forwarded without the override, and it must not pay for
          # materialising the packages either.
          lake = pkgs.writeShellScriptBin "lake" ''
            if [ "''${1-}" = "--version" ]; then
              exec ${lean}/bin/lake "$@"
            fi
            exec ${lean}/bin/lake --packages=$(${overrides}/bin/lean-llvm-overrides) "$@"
          '';
        in
        { inherit lake lean mathlib leanDeps overrides; };
    in
    {
      devShells = forAllSystems (
        pkgs:
        let
          env = mkLeanEnv pkgs;
          llvm = pkgs.llvmPackages;
        in
        {
          default = pkgs.mkShell {
            name = "lean-llvm";

            packages = [
              env.lean
              env.mathlib
            ]
            ++ env.leanDeps
            ++ [
              env.lake
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
              # Two checks read IR and generate corpora: the switch-lowering
              # correspondence and the fair-measurement corpus generator.  Both
              # were reaching an inherited `python3`, which is not the shell's to
              # rely on; providing it here makes them runnable where the rest of
              # the toolchain does.
              pkgs.python3
            ];

            shellHook = ''
              unset -f lake lean
              # The wrapper takes precedence over the toolchain's own `lake`, and
              # Lake's own caches are off: the store packages are the only source
              # of dependency artifacts.
              export PATH=${env.lake}/bin:$PATH
              export LAKE_NO_CACHE=1
              export RESERVOIR_API_URL=""
              printf 'lean-llvm: %s\n' "$(lean --version)"
            '';
          };
        }
      );

      packages = forAllSystems (pkgs: {
        default = self.devShells.${pkgs.system}.default;
        # The `lake` wrapper alone, for a NixOS image or another consumer that
        # needs the same dependency resolution without the shell.
        inherit (mkLeanEnv pkgs) lake;
      });
    };
}
