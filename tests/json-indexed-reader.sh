#!/usr/bin/env bash
# The indexed event reader against the list specification, on hand-built
# buffers.
#
#   nix develop -c bash tests/json-indexed-reader.sh
#
# `tests/json-indexed-reader.lean` runs the two readers over the cases a route
# never sees: an empty stream, a truncated final record, a span past the end of
# either source, an unknown tag and a body that does not decode.  It fails if
# the two readers disagree or if a case returns `none` where a record is
# readable, so an agreement produced by both readers failing is a red.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/.." && pwd)
cd "$repo"

bash probes/install/lake-locked.sh build LeanLLVM.Refinement.JsonEventCursorInterface
lake env lean --run tests/json-indexed-reader.lean
