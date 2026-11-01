{
  description = "lean-llvm — certified LLVM transformations and refinement in Lean 4";

  inputs = {
    # Pinned to a `nixos-unstable` revision whose `lean4` is the released
    # toolchain, so the shell substitutes a binary from `cache.nixos.org`
    # instead of building Lean from source.  Mathlib's tag `v4.35.0` names the
    # same version, so `lake` sees one toolchain on both sides.
    nixpkgs.url = "github:NixOS/nixpkgs/1c89083e451e891152365b799595cf7790a43325";
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
          # `pkgs.lean4` is the released toolchain at this nixpkgs pin and comes
          # from the binary cache, so no Lean build happens on a fresh store.
          # Mathlib's tag names the same version; see `lakefile.toml`.
          llvm = pkgs.llvmPackages;
        in
        {
          default = pkgs.mkShell {
            name = "lean-llvm";

            packages = [
              pkgs.lean4
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
