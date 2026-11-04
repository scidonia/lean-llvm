#!/usr/bin/env bash
# Run the JSON parser's scaling instrument over the documents beside it.
#
#   bash probes/bench/json-bench.sh <leanllvm-json-bench> [reps]
#   bash probes/bench/json-bench.sh --digest <leanllvm-json-bench>
#
# The rows are printed floor first, so the harness's own cost is visible before
# any size is compared, and every row carries the repetitions it took.  The
# digest mode prints each document's parse so two revisions' binaries can be
# diffed; it is the check that the timed rows measured the same work.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
docs="$here/json"

case "${1:-}" in
  --digest)
    exe=${2:?usage: json-bench.sh --digest <exe>}
    [ -x "$exe" ] || { echo "json-bench: $exe is not executable" >&2; exit 2; }
    exec "$exe" --digest "$docs"
    ;;
esac

exe=${1:?usage: json-bench.sh <exe> [reps]}
reps=${2:-5}
[ -x "$exe" ] || { echo "json-bench: $exe is not executable" >&2; exit 2; }

"$exe" --floor "$docs/cheapest.json"
for size in 4096 16384 65536; do
  "$exe" "$docs/scale-$size.json" "$reps"
done
