#!/usr/bin/env bash
# Build the JSON pipeline's Lean call route and its native adapter.
#
#   nix develop -c bash probes/json/route/build.sh
#
# The kernel is outside Lake (kernel/json/README.md), so this script is the link
# step: it compiles the six kernel translation units and the two additive
# no-event units (`stage2_noevent.c`, `pipeline_noevent.c`), the proved stage-1
# depth counter (`tests/v16/depth_count.ll`, at the same `clang -c` line the
# install uses for the unit), the probe's native character-policy scan
# (`policy.c`), the C adapter, and the standalone Lean program, then links them
# with `leanc`.  It asserts that the adapter imports the units it calls --
# `leanllvm_json_pipeline`, `leanllvm_json_pipeline_noevent`,
# `leanllvm_json_entry_table`, the mask unit, the depth counter and the policy
# scan -- and that the executable defines each of them, including the no-event
# units, so a build that silently lost a call is a failure rather than a pass.
# The certified objects' flags and symbol assertions are unchanged.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
build=${BUILD_DIR:-"$here/build"}

rm -rf "$build"
mkdir -p "$build"

# The kernel object's optimisation level and the adapter's stage instrument are
# the two build knobs; both default to the build the route ships.  `OPT` names
# the level the six kernel units are compiled at (the route's object); `TIMING=1`
# makes the adapter record its three stage intervals for `--stages`.  Everything
# else is held fixed, so an `OPT` pair differs in the optimisation level alone.
opt=${OPT:--O2}
timing=${TIMING:-0}
base=(-march=x86-64-v3 -mpclmul -std=gnu11
      -falign-loops=64 -falign-functions=64 -I "$repo/kernel/json")
kflags=("$opt" "${base[@]}")
shim_flags=(-O2 "${base[@]}")
if [ "$timing" = 1 ]; then
  shim_flags+=(-DROUTE_TIMING=1)
fi

printf 'flags: kernel=%s adapter=-O2 timing=%s\n' "$opt" "$timing"

for f in pipeline s1_block entry escape utf8; do
  clang "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done

# The certified stage-2 unit's object.  It is compiled from the identified
# production IR when `STAGE2_IR` names that artifact, and from the source
# otherwise; either way the object the route links carries the ABI wrapper and
# the walk the certificate is about.  The IR path disables the middle end, so
# the object is the backend's compilation of those bytes rather than a second
# optimisation of them; the flags above still supply the codegen level and the
# alignment the artifact was emitted under.
if [ -n "${STAGE2_IR:-}" ]; then
  [ -f "$STAGE2_IR" ] || { printf 'missing STAGE2_IR: %s\n' "$STAGE2_IR" >&2; exit 3; }
  stage2_ir_sha=$(sha256sum "$STAGE2_IR" | awk '{print $1}')
  clang "${kflags[@]}" -c -Xclang -disable-llvm-passes "$STAGE2_IR" -o "$build/stage2.o"
  stage2_object_sha=$(sha256sum "$build/stage2.o" | awk '{print $1}')
  printf 'stage2: ir=%s sha256=%s\n' "$STAGE2_IR" "$stage2_ir_sha"
  printf 'stage2: object=%s sha256=%s\n' "${build#$repo/}/stage2.o" "$stage2_object_sha"
  # The release artifact's identity is the capture record's.  When the supplied
  # IR is the recorded production emission, the object compiled from it must be
  # the object the record binds; a toolchain or flag drift is a failed build
  # rather than a silently different artifact.  An IR that is not the recorded
  # one is reported as such and is not bound to the record.
  production_record="$repo/probes/install/ir/stage2.production.tsv"
  if [ -f "$production_record" ]; then
    recorded_ir=$(awk -F'\t' '$1=="sha256"{print $2}' "$production_record")
    recorded_object=$(awk -F'\t' '$1=="object_sha256"{print $2}' "$production_record")
    if [ "$stage2_ir_sha" = "$recorded_ir" ]; then
      [ "$stage2_object_sha" = "$recorded_object" ] || {
        printf 'build: the recorded production IR compiled to %s, not the recorded object %s\n' \
          "$stage2_object_sha" "$recorded_object" >&2
        exit 1
      }
      printf 'stage2: bound to probes/install/ir/stage2.production.tsv (input %s, object %s)\n' \
        "$recorded_ir" "$recorded_object"
    else
      printf 'stage2: not the recorded production IR (record has %s)\n' "$recorded_ir"
    fi
  fi
else
  clang "${kflags[@]}" -c "$repo/kernel/json/stage2.c" -o "$build/stage2.o"
  printf 'stage2: object=%s sha256=%s (from kernel/json/stage2.c)\n' \
    "${build#$repo/}/stage2.o" "$(sha256sum "$build/stage2.o" | awk '{print $1}')"
fi

# The no-event arm's two units, at the same kernel flags.  They are additive:
# `stage2_noevent.c` includes `stage2.c` under a rename of the certified entry,
# so the helper text is the certified unit's, and `pipeline_noevent.c` is the
# stage-1 loop with the reading tail.  Nothing in the certified objects changes.
for f in stage2_noevent pipeline_noevent; do
  clang "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done

# The depth counter is the census fixture's text, compiled at the line the
# install uses for it (`probes/install/build.sh`), so the object the route runs
# is the object `depth_count_refines` is about.
clang -c "$repo/tests/v16/depth_count.ll" -o "$build/depth_count.o"

clang "${shim_flags[@]}" $(leanc --print-cflags) -I "$here" -c "$here/policy.c" \
  -o "$build/policy.o"
clang "${shim_flags[@]}" $(leanc --print-cflags) -c "$here/shim.c" -o "$build/shim.o"

# The instrument is a compile-time gate, so its cost in the ordinary adapter is
# checkable rather than asserted: an uninstrumented build must not reference the
# clock at all, and an instrumented one must.
clock_refs=$(nm -u "$build/shim.o" | grep -c 'clock_gettime' || true)
if [ "$timing" = 1 ]; then
  if [ "$clock_refs" -lt 1 ]; then
    echo "build: TIMING=1 but the adapter does not read the clock" >&2
    exit 1
  fi
else
  if [ "$clock_refs" -ne 0 ]; then
    echo "build: the ordinary adapter references clock_gettime; the gate is off" >&2
    exit 1
  fi
fi

# The decision and the fallback are the library's, so the program imports the
# domain module and the reference parser.  Their Lean modules are built by Lake,
# and the emitted C is what links: the input must be inside the Lake project so
# the module prefix resolves, and `-I` is the emitted C's own include root.
#
# `admission`'s depth clause folds `deltaZ` (`DepthCountRefine`), so the domain
# module's link carries that module and the eight-module cone its emitted C
# names: the three the initialiser chain reaches (`Memory`, `Parser`, `Semantics`)
# and the four they in turn reach (`Basic`, `Syntax`, `Binary64`, `Printer`).  A
# module absent from this list is an undefined `deltaZ` at link, not a green
# build: the list is what the emitted C names, not a choice.
#
# The value arm adds the event decoder (`JsonEventDecode`), the canonicalisation
# (`JsonCanon`), the schema vocabulary (`JsonPipelineSpec`) and the shared
# rendering (`JSON.Render`), and their import closure follows them into the link.
# That closure is Mathlib-free by construction, and the list is the fence that
# keeps it so: a module importing `StrtodTier1`/`StrtodTier3` (and through them
# `ITree.Internal.FloatingPoint` and `Mathlib.Data.FP.Basic`) would pull the
# Mathlib initialiser chain into the binary and would make the compiler pick
# Mathlib's specialisation entries for this program's own `IO.println`/`List.foldl`
# uses.  `StrtodRead` holds the reader the canonicalisation needs precisely so the
# tier proofs stay out; a new import that breaks the fence fails at this link
# rather than growing the binary and its start-up work silently.
cone_ir=("$repo/.lake/build/ir/LeanLLVM/JsonKernelDomain.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ByteString.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Bytes.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Utf8.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Spec.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Scan.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Tape.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Parse.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/DepthCountRefine.c"
         "$repo/.lake/build/ir/LeanLLVM/Basic.c"
         "$repo/.lake/build/ir/LeanLLVM/Binary64.c"
         "$repo/.lake/build/ir/LeanLLVM/Memory.c"
         "$repo/.lake/build/ir/LeanLLVM/Parser.c"
         "$repo/.lake/build/ir/LeanLLVM/Printer.c"
         "$repo/.lake/build/ir/LeanLLVM/Semantics.c"
         "$repo/.lake/build/ir/LeanLLVM/Syntax.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Correct.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Render.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ScanBlock.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ScanBlocks.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ScanBody.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ScanString.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ScanWindow.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Strtod.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/TapeCorrect.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/BitLanes.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/CallsFootprint.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonB3Steps.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonB8Steps.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonCanon.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonConsumerEvent.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEntSpec.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEntryIR.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEntrySteps.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeBatch.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeBatchEntries.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeIR.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeIntrinsics.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListBody.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListContract.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListFixpoint.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListInvariant.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListLanes.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListLoop.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListMemo.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListPositions.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListRun.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeListWriter.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeSpec.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEscapeSteps.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEventBytes.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEventCursor.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEventIndexed.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEventIndexedStep.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonEventDecode.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonPipelineContract.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonPipelineIR.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonPipelineSpec.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonS1MasksIR.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonS1MasksSteps.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonScanSpec.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonStage2Scratch.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonUnitContracts.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonUtf8IR.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonUtf8Spec.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/JsonUtf8Steps.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/LoopFuel.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/Pclmul.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/QuoteDerive.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/Relation.c"
         "$repo/.lake/build/ir/LeanLLVM/StrtodRead.c")
for f in "${cone_ir[@]}"; do
  [ -f "$f" ] || {
    echo "build: absent: $f" >&2
    echo "build: build the route's Lean modules first:" >&2
    echo "  nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonKernelDomain LeanLLVM.JSON.Parse LeanLLVM.JSON.Render LeanLLVM.Refinement.JsonEventBytes LeanLLVM.Refinement.JsonEventCursor LeanLLVM.Refinement.JsonCanon LeanLLVM.Refinement.JsonPipelineSpec" >&2
    exit 1
  }
done

(cd "$repo" && lake env lean -c "$build/RouteMain.c" "$here/RouteMain.lean")
leanc -c "$build/RouteMain.c" -I "$repo/.lake/build/ir" -o "$build/RouteMain.o"

if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_json_pipeline_noevent$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_json_pipeline_noevent" >&2
  exit 1
fi

if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_json_pipeline$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_json_pipeline" >&2
  exit 1
fi

# The adapter's setup fills the entry unit's POS8 table before the call; a
# build that lost that call leaves the table zero and every container refused.
if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_json_entry_table$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_json_entry_table" >&2
  exit 1
fi

# Phase one of the admission is the depth walk, and its lane list goes through
# the proved depth counter: an adapter that stopped calling the counter would
# still build and would report a maximum with no second arithmetic beside it.
# The mask unit is not on this path -- the walk reads the bytes it folds, because
# the classifier's in-string mask is a different reading of a string from the
# reference scan's (see `shim.c`'s depth section) -- so it is checked where it is
# defined, by the object, and not here.
if [ "$(nm -u "$build/shim.o" | grep -c ' depth_count$')" -eq 0 ]; then
  echo "build: the adapter does not import depth_count" >&2
  exit 1
fi
if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_route_body_stop$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_route_body_stop" >&2
  exit 1
fi
# Phase two of the admission is this scan: an adapter that stopped calling it
# would build, would still answer every document, and would be reading the
# reference's rule from nowhere, so the import is checked like the pipeline's.
if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_route_policy_scan$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_route_policy_scan" >&2
  exit 1
fi

leanc "$build/RouteMain.o" "$build/shim.o" "$build/policy.o" \
  "${cone_ir[@]}" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  "$build/stage2_noevent.o" "$build/pipeline_noevent.o" "$build/depth_count.o" \
  -I "$repo/.lake/build/ir" -o "$build/leanllvm-json-route"

if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_pipeline_noevent$')" -eq 0 ]; then
  echo "build: the route does not define leanllvm_json_pipeline_noevent" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_stage2_noevent$')" -eq 0 ]; then
  echo "build: the route does not define leanllvm_json_stage2_noevent" >&2
  exit 1
fi

if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_pipeline$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_pipeline" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_entry_table$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_entry_table" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_s1_masks$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_s1_masks" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T depth_count$')" -eq 0 ]; then
  echo "build: the executable does not define depth_count" >&2
  exit 1
fi
if [ "$(nm --defined-only "$build/leanllvm-json-route" | grep -c ' leanllvm_route_policy_scan$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_route_policy_scan" >&2
  exit 1
fi

clang "${kflags[@]}" "$here/driver.c" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  "$build/stage2_noevent.o" "$build/pipeline_noevent.o" -o "$build/driver"

# The guard's own scenario (`guard.sh`) drives this probe over the corpus, the
# escape unit's rows and the bench's documents; it is built here so the probe
# and the route share one kernel object set.
clang "${kflags[@]}" "$here/guard_check.c" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" -o "$build/guard_check"

printf 'ok: %s (sha256 %s)\n' "$build/leanllvm-json-route" \
  "$(sha256sum "$build/leanllvm-json-route" | awk '{print $1}')"
