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

      # `leanPackages.lean4` carries the patch that makes Lake treat a package
      # under `/nix/store` as already elaborated, so a checkout builds this
      # project's modules and nothing else.  Its mathlib is the revision
      # `lakefile.toml` pins, tag `v4.35.0` of `leanprover-community/mathlib4`.
      #
      # The store packages ship the generated `.c` files but not the
      # `.c.o.export` objects an executable links.  A dummy package that
      # imports Mathlib makes Lake compile that facet for every module of the
      # whole closure; the farm below redirects those writes into a writable
      # tree of symlinks, leaving the store untouched.
      mkLeanPackagesWithExports =
        pkgs:
        let
          lean = pkgs.leanPackages.lean4;
          mathlib = pkgs.leanPackages.mathlib;
          allPackages = mathlib.passthru.allLeanDeps ++ [ mathlib ];
          packageName = dep: dep.passthru.lakePackageName;
          names = map packageName allPackages;
        in
        pkgs.runCommand "lean-packages-with-exports"
          {
            nativeBuildInputs = [
              lean
              pkgs.stdenv.cc
              pkgs.jq
              pkgs.coreutils
            ];

            # The export objects are the artifact; keep them whole and leave the
            # symlink farm alone.
            dontStrip = true;
            dontPatchELF = true;

            passthru = {
              inherit lean mathlib;
            };
          }
          ''
            set -euo pipefail

            export HOME="$TMPDIR"
            export LAKE_NO_CACHE=1
            export RESERVOIR_API_URL=""
            export LEAN_CC="${pkgs.stdenv.cc}/bin/cc"
            export LEAN_NUM_THREADS="''${NIX_BUILD_CORES:-1}"

            mkdir -p "$out"

            # One directory per package name, mirroring the store package as
            # symlinks.  Only directories are made writable, so Lake creates the
            # missing objects beside the store files instead of inside them.
            ${nixpkgs.lib.concatMapStringsSep "\n" (dep: ''
              mkdir -p "$out/${packageName dep}"
              cp -as ${dep}/. "$out/${packageName dep}"/
              find "$out/${packageName dep}" -type d -exec chmod u+w {} +
            '') allPackages}

            # The manifest names each dependency, and `--packages` replaces every
            # entry with the writable farm directory.
            printf '%s\n' ${nixpkgs.lib.escapeShellArgs names} \
              | jq -R . \
              | jq -s --arg out "$out" \
                '{schemaVersion: "1.2.0", packages: map({type: "path", name: ., inherited: false, dir: ($out + "/" + .)})}' \
              > "$out/lake-overrides.json"

            # The store packages are read-only; record the moment before the
            # build so any write that somehow bypassed the farm is visible.
            touch "$TMPDIR/store-marker"

            dummy="$TMPDIR/dummy"
            mkdir -p "$dummy"
            cat > "$dummy/lakefile.toml" <<'EOF'
            name = "dummy"
            version = "0.1.0"
            defaultTargets = ["dummy"]

            [[require]]
            name = "mathlib"

            [[lean_exe]]
            name = "dummy"
            root = "Main"
            EOF
            cat > "$dummy/Main.lean" <<'EOF'
            import Mathlib
            def main : IO Unit := pure ()
            EOF
            cp ${./lake-manifest.json} "$dummy/lake-manifest.json"

            (
              cd "$dummy"
              ${lean}/bin/lake --packages="$out/lake-overrides.json" build --no-ansi
            )

            # A build that reused the store packages in place would have needed
            # a write there and failed; assert none happened.
            for dep in ${nixpkgs.lib.escapeShellArgs (map toString allPackages)}; do
              if [ -n "$(find "$dep" -newer "$TMPDIR/store-marker" -print -quit)" ]; then
                echo "error: wrote into store package $dep" >&2
                exit 1
              fi
            done

            # `import Mathlib` does not reach every module in the tree --
            # `Mathlib.Basic` is one it skips -- so the count is the check, not
            # a particular module path.  A zero count is a hard failure.
            exports="$out/mathlib/.lake/build/ir"
            count="$(find "$exports" -name '*.c.o.export' | wc -l)"
            if [ "$count" -eq 0 ]; then
              echo "error: the build produced no .c.o.export objects" >&2
              exit 1
            fi
            if [ "$count" -le 8000 ]; then
              echo "error: expected more than 8000 mathlib exports, found $count" >&2
              exit 1
            fi
          '';
    in
    {
      packages = forAllSystems (pkgs: {
        default = self.devShells.${pkgs.stdenv.hostPlatform.system}.default;
        leanPackagesWithExports = mkLeanPackagesWithExports pkgs;
      });

      devShells = forAllSystems (
        pkgs:
        let
          lean = pkgs.leanPackages.lean4;
          leanPackagesWithExports = mkLeanPackagesWithExports pkgs;

          # `--packages` is a global Lake option, so one wrapper covers `build`,
          # `exe`, `env` and the rest of the surface the repository uses.
          # `--version` is only accepted as Lake's first argument, so it is
          # forwarded without the override.
          lake = pkgs.writeShellScriptBin "lake" ''
            if [ "''${1-}" = "--version" ]; then
              exec ${lean}/bin/lake "$@"
            fi
            exec ${lean}/bin/lake --packages=${leanPackagesWithExports}/lake-overrides.json "$@"
          '';

          llvm = pkgs.llvmPackages;
        in
        {
          default = pkgs.mkShell {
            name = "lean-llvm";

            packages = [
              lean
              leanPackagesWithExports
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
              # Lake's own caches are off: the packages with exports are the only
              # source of dependency artifacts.
              export PATH=${lake}/bin:$PATH
              export LAKE_NO_CACHE=1
              export RESERVOIR_API_URL=""
              printf 'lean-llvm: %s\n' "$(lean --version)"
            '';
          };
        }
      );
    };
}
