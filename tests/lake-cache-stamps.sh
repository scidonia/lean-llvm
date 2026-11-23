#!/usr/bin/env bash
# The Lake package cache keeps one stamp per store package it copied.  The
# stamps must survive an invocation: without them each run re-copies every
# package, which resets the mtimes Lake's staleness check reads, so every build
# redoes work nothing changed.
#
# The check states both directions.  Removing a stamp must make the next
# invocation copy that package, which shows the detector sees a copy at all;
# with the stamps in place, a further invocation must copy nothing.
set -euo pipefail

cache="${XDG_CACHE_HOME:-$HOME/.cache}/lean-llvm/packages"

lake=$(nix develop -c bash -c 'command -v lake' | tail -1)
wrapper=$(readlink -f "$lake")
overrides=$(sed -n 's|.*--packages=\$*(\([^)]*\)).*|\1|p' "$wrapper" | head -1)
[ -x "$overrides" ] || { echo "no overrides binary in $wrapper" >&2; exit 1; }
run() { "$overrides" >/dev/null; }

run
[ -d "$cache/stamps" ] || { echo "no stamps directory after an invocation" >&2; exit 1; }

# Control: a package whose stamp is gone is copied again.
victim=$(find "$cache" -mindepth 1 -maxdepth 1 -type d ! -name stamps | head -1)
[ -n "$victim" ] || { echo "no package copy to use as the control" >&2; exit 1; }
rm -f "$cache/stamps/$(basename "$victim")"
before=$(stat -c %Y "$victim")
run
after=$(stat -c %Y "$victim")
if [ "$before" = "$after" ]; then
  echo "control failed: $victim was not copied after its stamp was removed" >&2
  exit 1
fi

# The property: with every stamp present, another invocation copies nothing.
stamps=$(find "$cache/stamps" -type f | wc -l)
before=$(stat -c %Y "$victim")
run
[ -d "$cache/stamps" ] || { echo "invocation pruned the stamps directory" >&2; exit 1; }
[ "$(find "$cache/stamps" -type f | wc -l)" = "$stamps" ] \
  || { echo "invocation changed the stamp set" >&2; exit 1; }
[ "$(stat -c %Y "$victim")" = "$before" ] \
  || { echo "invocation copied $victim again" >&2; exit 1; }

echo "lake cache stamps: control copied, stamps kept, second invocation copied nothing"
