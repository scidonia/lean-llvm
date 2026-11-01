#!/usr/bin/env bash
# The toolchain revision recorded in an installation certificate.
#
#   bash probes/install/toolchain-id.sh
#   -> sha256:<64 lowercase hex>
#
# The digest is the SHA-256 of one fixed ASCII record: a `leanllvm-toolchain-v1`
# header, then one line per input, each line terminated by one LF:
#
#   lean-toolchain=<sha256 of lean-toolchain>
#   flake-nix=<sha256 of flake.nix>
#   flake-lock=<sha256 of flake.lock>
#   lakefile=<sha256 of lakefile.toml>
#   lake-manifest=<sha256 of lake-manifest.json>
#   lean-version=<sha256 of `lean --version` stdout>
#   clang-version=<sha256 of `clang --version` stdout>
#   ld-version=<sha256 of `ld --version` stdout>
#
# A file digest is over the file's exact bytes; a version digest is over all
# bytes of the command's stdout under `LC_ALL=C`.  The revision-bearing pin
# files are the Lean toolchain tag (`lean-toolchain`), the flake's pinned
# sources (`flake.nix`, `flake.lock`), the Mathlib revision
# (`lakefile.toml`) and the resolved package revisions (`lake-manifest.json`),
# so a single component change changes the digest.
#
# The script resolves the repository root from its own location, so the
# selector that invokes it and the producer that invokes it both measure the
# tree they are running in.  A missing pin file or a failing version command
# fails the script instead of printing a digest computed from less input.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)

die() {
  echo "toolchain-id: $*" >&2
  exit 1
}

hash_file() { # path
  [ -f "$1" ] || die "missing pin file $1"
  local digest
  digest=$(sha256sum "$1" | cut -d' ' -f1) || die "cannot hash $1"
  printf '%s' "$digest"
}

hash_stdout() { # command and arguments
  local digest
  [ "$#" -gt 0 ] || die "no version command"
  digest=$(LC_ALL=C "$@" | sha256sum | cut -d' ' -f1) ||
    die "version command failed: $*"
  printf '%s' "$digest"
}

is_digest() {
  [[ "$1" =~ ^[0-9a-f]{64}$ ]]
}

record=$(
  printf 'leanllvm-toolchain-v1\n'
  printf 'lean-toolchain=%s\n' "$(hash_file "$root/lean-toolchain")"
  printf 'flake-nix=%s\n' "$(hash_file "$root/flake.nix")"
  printf 'flake-lock=%s\n' "$(hash_file "$root/flake.lock")"
  printf 'lakefile=%s\n' "$(hash_file "$root/lakefile.toml")"
  printf 'lake-manifest=%s\n' "$(hash_file "$root/lake-manifest.json")"
  printf 'lean-version=%s\n' "$(hash_stdout lean --version)"
  printf 'clang-version=%s\n' "$(hash_stdout clang --version)"
  printf 'ld-version=%s\n' "$(hash_stdout ld --version)"
)

# Every component must be a digest in the canonical form, so a truncated or
# decorated value cannot be folded into the revision.
while IFS='=' read -r key value; do
  case "$key" in
    leanllvm-toolchain-v1) continue ;;
    *) ;;
  esac
  is_digest "$value" || die "component $key is not a lowercase sha256: '$value'"
done <<< "$record"

revision=$(printf '%s\n' "$record" | sha256sum | cut -d' ' -f1)
is_digest "$revision" || die "cannot compute the record digest"
printf 'sha256:%s\n' "$revision"
