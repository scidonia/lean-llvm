#!/usr/bin/env bash
# Checks for the emitted loop fixture and the driver's header refusal.
#
#   bash tests/m4-loop-emission.sh --capture
#   nix develop -c lake build leanllvm
#   nix develop -c bash tests/m4-loop-emission.sh --return-attr
#   nix develop -c bash tests/m4-loop-emission.sh --function-attr
#
# The `lake build leanllvm` step prepares `.lake/build/bin/leanllvm` outside
# the temporary directory; the two driver modes copy that binary into their own
# temporary directory and run only the copy.
#
# --capture is E1: running probes/install/ir/capture.sh must write
# probes/install/ir/loop.ll from a Lean emission of the loop body instead of
# leaving the fixture the tree starts with in place.
#
# --return-attr is E2 and --function-attr is E3: the leanllvm driver must
# refuse a function header carrying a semantic attribute it does not model,
# rather than parse past it and rewrite the function without it.  E2's header
# carries the return attribute `range(i64 0, 1)` before the return type, E3's
# carries the function attribute `noreturn` after the parameter list.
#
# --capture builds a private, repository-shaped tree under a temporary
# directory, copies probes/install/ir/capture.sh into it, and runs that copy
# against local shims for the only tools the script invokes — lake, clang and
# opt.  The lake shim answers the two questions the route asks of it: the Lean
# prefix, and the loop emission.  The emission is the tree's loop body with its
# xor operand taken from the delimiter pattern the tree's Lean body fixture
# binds, so the value the check looks for is computed from the fixtures rather
# than typed here.  The command must exit zero, and the loop's blocks are bound
# by their roles: the entry block allocates two distinct slots, the conditional
# block loads one and branches on a comparison of that load, the body stores
# both slots and returns to the conditional block.  The XOR result must be the
# value the body's `lshr` shifts, and that shift's amount must be the SSA result
# of a `mul i64 <counter-load>, 8` in the loop body whose multiplicand is the
# counter load the conditional block tests.  The check also applies one
# relation-breaking edit at a time to that body — a counter store moved into the
# fall-through block, an accumulator load removed from the body, a back-edge
# removed, the branch's targets exchanged, a comparison that ignores the slot's
# load, a false branch naming a block the body does not define, a shift amount
# fixed to a constant, a lane offset multiplied from a constant instead of the
# counter load, a lane offset multiplied by a value other than 8 — and requires
# each to be named, so a passing check is about the relations and not the
# instruction tokens.  The
# clang and opt shims answer with one minimal module, a pass-through copy and a
# successful `verify`, so the rest of the capture run — the baseline and
# candidate fixtures — completes.
#
# --return-attr and --function-attr run the repository driver `lake build
# leanllvm` prepares, copied into the temporary directory and invoked there
# with `--passes none`, so the header rule is observed at the driver's command
# line.  A clean input that carries no attribute is rewritten by the same
# copied driver first, so the output the refusal asserts is absent is shown to
# be observable when a run does write it.  The refusal's diagnostic must bind
# the attribute token to an unsupported or unmodelled statement on one line —
# `unsupported`, `unmodelled`, `unmodeled`, or `is not modelled yet`; a line
# that only echoes the input header does not pass.
#
# TMPDIR points inside the temporary directory.  The check itself reaches no
# compiler, linker, network, clock or other service once it runs inside the
# prepared dev shell — `nix develop` may provision that shell before the check
# starts — and nothing outside the temporary directory is written.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails,
# 2 on bad usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  echo "usage: bash tests/m4-loop-emission.sh --capture|--return-attr|--function-attr" >&2
  exit 2
}

mode=${1:-}
case "$mode" in
  --capture|--return-attr|--function-attr) ;;
  *) usage ;;
esac
[ "$#" -eq 1 ] || usage

repo=$(cd "$(dirname "$0")/.." && pwd)

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

fails=0
ok() { printf 'ok: %s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*" >&2; fails=$((fails + 1)); }

# The `define` block of @leanllvm_comma_mask8, verbatim, from an emission.
parse_fn() {
  awk '
    !d && $0 == "define i64 @leanllvm_comma_mask8(i64 %arg) {" {
      d = 1; print; depth = 0; depth += gsub(/\{/, "{"); next
    }
    d { print; depth += gsub(/\{/, "{"); depth -= gsub(/\}/, "}"); if (depth <= 0) exit }
  ' "$1"
}

# The constant of the body's `xor i64 %arg, <constant>`, empty when absent.
xor_constant() {
  sed -nE 's/^  %[A-Za-z0-9_.]+ = xor i64 %arg, ([0-9]+)$/\1/p' "$1" | sed -n '1p'
}

# The SSA name that xor produces, empty when absent.
xor_result() {
  sed -nE 's/^  %([A-Za-z0-9_.]+) = xor i64 %arg, [0-9]+$/\1/p' "$1" | sed -n '1p'
}

# Why the body is not the memory-backed conditional loop, empty when it is.
# The blocks are bound by their roles: the entry block allocates two distinct
# i64 slots; a conditional block loads one slot and feeds that load to the
# `icmp` its `br i1` tests in the same block, branching on true to the loop
# body and on false to a distinct fall-through block the function defines; the
# loop body stores the counter slot, loads and then stores the accumulator
# slot, and branches back to the conditional block.  Because every instruction
# is placed in its block, a counter store in the fall-through block, an
# accumulator load only there, a body that never returns to the condition, a
# branch naming a block the function does not define, and a comparison fed from
# anything but the slot's load are named rather than passed on the mere
# presence of an alloca, a load, a store, an `icmp` and a branch.
memory_loop_defect() {
  awk '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    function bare(s) { sub(/^%/, "", s); return s }
    function defect(msg) { print msg; exit 1 }
    /^[A-Za-z0-9_.]+:$/ {
      blk = substr($0, 1, length($0) - 1)
      is_block[blk] = 1
      if (blockno++ == 0) entry = blk
      next
    }
    /^[[:space:]]*;/ { next }
    NF == 0 { next }
    {
      pos++
      if ($2 == "=") {
        name = bare($1)
        if ($3 == "alloca" && strip_comma($4) == "i64") {
          if (blk == entry) { slot[++nslot] = name; is_slot[name] = 1 }
        } else if ($3 == "load" && strip_comma($4) == "i64" && $5 == "ptr") {
          p = bare(strip_comma($6))
          load_ptr[name] = p
          load_block[name] = blk
          if (!((p, blk) in first_load)) first_load[p, blk] = pos
        } else if ($3 == "icmp" && strip_comma($5) == "i64") {
          cmp[++ncmp] = name
          cmp_src[name] = bare(strip_comma($6))
          cmp_block[name] = blk
        }
        next
      }
      if ($1 == "store" && $2 == "i64" && $4 == "ptr") {
        p = bare(strip_comma($5))
        if (!((p, blk) in first_store)) first_store[p, blk] = pos
        next
      }
      if ($1 == "br" && $2 == "i1") {
        c = bare(strip_comma($3))
        br_block[c] = blk
        br_true[c] = bare(strip_comma($5))
        br_false[c] = bare(strip_comma($7))
        next
      }
      if ($1 == "br" && $2 == "label") {
        br_target[blk] = bare(strip_comma($3))
        next
      }
    }
    END {
      for (i = 1; i <= ncmp; i++) {
        c = cmp[i]
        cond = br_block[c]
        if (cond == "" || cmp_block[c] != cond) continue
        src = cmp_src[c]
        p = load_ptr[src]
        if (p == "" || !(p in is_slot)) continue
        if (load_block[src] != cond) continue
        body = br_true[c]
        done = br_false[c]
        if (body == "" || done == "" || body == cond || done == cond ||
            done == body) continue
        if (!(done in is_block))
          defect("the false target " done " of the conditional branch is not a block of the function")
        if (br_target[body] != cond)
          defect("the loop body " body " does not branch back to the conditional block " cond)
        if (!((p, body) in first_store))
          defect("the loop body " body " never stores the counter slot " p)
        acc = ""
        for (j = 1; j <= nslot && acc == ""; j++) {
          q = slot[j]
          if (q == p) continue
          if (((q, body) in first_load) && ((q, body) in first_store) &&
              first_store[q, body] > first_load[q, body]) acc = q
        }
        if (acc == "")
          defect("no second slot allocated in the entry block is loaded and then stored by the loop body")
        exit 0
      }
      defect("no conditional branch tests an icmp of a load from an entry-allocated slot in its own block")
    }
  ' "$1"
}

# Why the body's shift is not the XOR result shifted by the counter's lane
# offset, empty when it is.  The lane offset is the SSA result of a `mul i64`
# in the loop body whose multiplicand is the counter load — the load, in the
# conditional block, of the entry-allocated slot that block's `icmp` tests and
# whose branch on true reaches the body — and whose multiplier is 8; the `lshr`
# the body applies to the XOR result is that mul's SSA result.
shift_lane_defect() {
  awk '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    function bare(s) { sub(/^%/, "", s); return s }
    function defect(msg) { print msg; exit 1 }
    /^[A-Za-z0-9_.]+:$/ {
      blk = substr($0, 1, length($0) - 1)
      if (blockno++ == 0) entry = blk
      next
    }
    /^[[:space:]]*;/ { next }
    NF == 0 { next }
    {
      if ($2 == "=") {
        name = bare($1)
        if ($3 == "alloca" && strip_comma($4) == "i64") {
          if (blk == entry) is_slot[name] = 1
        } else if ($3 == "load" && strip_comma($4) == "i64" && $5 == "ptr") {
          load_ptr[name] = bare(strip_comma($6))
          load_block[name] = blk
        } else if ($3 == "icmp") {
          cmp_src[name] = bare(strip_comma($6))
          cmp_block[name] = blk
        } else if ($3 == "xor" && strip_comma($4) == "i64" &&
                   bare(strip_comma($5)) == "arg") {
          if (xorres == "") xorres = name
        } else if ($3 == "mul" && strip_comma($4) == "i64") {
          mul_block[name] = blk
          mul_lhs[name] = bare(strip_comma($5))
          mul_rhs[name] = strip_comma($6)
        } else if ($3 == "lshr" && strip_comma($4) == "i64") {
          sh_block[name] = blk
          sh_val[name] = bare(strip_comma($5))
          sh_amt[name] = bare(strip_comma($6))
        }
        next
      }
      if ($1 == "br" && $2 == "i1") {
        c = bare(strip_comma($3))
        br_block[c] = blk
        br_true[c] = bare(strip_comma($5))
        next
      }
    }
    END {
      if (xorres == "") defect("the body has no xor of %arg")
      for (c in br_block) {
        cond = br_block[c]
        if (cmp_block[c] != cond) continue
        src = cmp_src[c]
        p = load_ptr[src]
        if (p == "" || !(p in is_slot)) continue
        if (load_block[src] != cond) continue
        body = br_true[c]
        if (body == "" || body == cond) continue
        shift = ""
        for (s in sh_val) if (sh_val[s] == xorres) { shift = s; break }
        if (shift == "")
          defect("the body does not shift the xor result " xorres)
        amt = sh_amt[shift]
        if (!(amt in mul_block))
          defect("the lshr amount " amt " is not the SSA result of a mul in the body")
        if (mul_block[amt] != body || sh_block[shift] != body)
          defect("the lane offset " amt " and the lshr " shift " are not both in the loop body " body)
        if (mul_lhs[amt] != src)
          defect("the lane offset " amt " multiplies " mul_lhs[amt] ", not the counter load " src)
        if (mul_rhs[amt] != "8")
          defect("the lane offset " amt " multiplies by " mul_rhs[amt] ", not 8")
        exit 0
      }
      defect("no conditional branch tests an icmp of a load from an entry-allocated slot in its own block")
    }
  ' "$1"
}

# Whether one diagnostic line binds the attribute to a refusal: it must carry
# the attribute token and say that attribute is unsupported or unmodelled —
# `unsupported`, either spelling of `unmodelled`, or the parser's own
# `is not modelled yet` idiom.  A line that only echoes the input header does
# not satisfy this.
attribute_refusal() {
  grep -E 'unsupported|unmodell?ed|is not modelled yet' "$1" |
    grep -Eq '(^|[^A-Za-z0-9_.])'"$2"'([^A-Za-z0-9_.]|$)'
}

# The `define` lines of a file, for a failure message.
define_lines() {
  grep -nE '^define ' "$1" 2>/dev/null | tr '\n' ';'
}

if [ "$mode" = --capture ]; then
  capture_source=$repo/probes/install/ir/capture.sh
  start_fixture=$repo/probes/install/ir/loop.ll
  fakebin=$work/bin
  tree=$work/tree
  tree_ir=$tree/probes/install/ir

  mkdir -p "$work/tmp"
  TMPDIR=$work/tmp
  export TMPDIR

  # Exit before the scenario's own assertions if the fixture cannot be built,
  # so a construction failure is never read as an assertion result.
  trap 'printf "SETUP: fixture construction failed: %s\n" "$BASH_COMMAND" >&2; exit 3' ERR
  set -e

  mkdir -p "$fakebin" "$tree/probes/install/build" "$tree_ir" \
    "$work/lean-prefix/include"

  # The tree starts from the fixture the repository checks in and the route's
  # own inputs.
  cp "$capture_source" "$tree_ir/capture.sh"
  cp "$start_fixture" "$tree_ir/loop.ll"

  # The constant the tree's fixture binds, and the pattern the Lean body
  # fixture carries: one greater per byte of that constant, so the pair cannot
  # silently agree.  The mock emission takes its xor operand from the Lean
  # fixture, so no fixture value is typed here.
  old_operand=$(xor_constant "$tree_ir/loop.ll")
  [ -n "$old_operand" ] || {
    echo "SETUP: the tree's loop fixture has no 'xor i64 %arg, <constant>' to read" >&2
    exit 3
  }
  new_pattern=$((old_operand + 0x0101010101010101))
  { [ "$new_pattern" -gt 0 ] && [ "$new_pattern" -ne "$old_operand" ]; } || {
    echo "SETUP: the derived delimiter pattern is not a distinct positive constant" >&2
    exit 3
  }
  pattern_hex=$(printf '0x%X' "$new_pattern")

  cat > "$tree/probes/install/Loop.lean" <<LEAN
/-- Loop body: the memory-backed delimiter mask, one lane per iteration. -/
@[export leanllvm_comma_mask8]
def commaMask8 (x : UInt64) : UInt64 :=
  let m := x ^^^ $pattern_hex
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if i < 8 then
      let shift := UInt64.ofNat (8 * i)
      let b := (m >>> shift) &&& 0xFF
      go (i + 1) (if b = 0 then acc ||| (0x80 <<< shift) else acc)
    else acc
  go 0 0
LEAN

  # The C inputs the route compiles.  The clang shim answers with a fixed
  # module, so their contents only have to be the shape capture.sh extracts.
  cat > "$tree/probes/install/build/Baseline.c" <<C
#include <lean/lean.h>

LEAN_EXPORT uint64_t leanllvm_comma_mask8(uint64_t x) {
  return lean_uint64_xor(x, $old_operand);
}
C

  cat > "$tree/probes/install/build/Candidate.c" <<'C'
#include <lean/lean.h>

LEAN_EXPORT uint64_t leanllvm_comma_mask8(uint64_t x) {
  uint64_t acc = 0;
  return lean_uint64_or(acc, x);
}
C

  cat > "$tree_ir/candidate_lanes.c" <<'C'
/* The candidate's lane-by-lane fold, compiled by the capture route. */
C

  {
    printf 'FAKE_LEAN_PREFIX=%q\n' "$work/lean-prefix"
    printf 'FAKE_LOOP_FIXTURE=%q\n' "$tree_ir/loop.ll"
    printf 'FAKE_LOOP_LEAN=%q\n' "$tree/probes/install/Loop.lean"
    printf 'FAKE_TARGET=%q\n' 'x86_64-unknown-linux-gnu'
    printf 'FAKE_DATALAYOUT=%q\n' 'e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128'
  } > "$fakebin/fake.env"

  # --- local toolchain ----------------------------------------------------
  # lake: the Lean prefix, and the loop emission.  The emission is the tree's
  # loop body with its xor operand taken from the delimiter pattern the Lean
  # body fixture binds, so the answer is derived from the fixtures rather than
  # restated.  Any other invocation fails loudly, so an unexpected call is
  # visible instead of being answered by a guess.
  cat > "$fakebin/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"

case "${1:-}" in
  env)
    shift
    { [ "${1:-}" = lean ] && [ "${2:-}" = --print-prefix ]; } || {
      echo "lake: unexpected env invocation: $*" >&2
      exit 3
    }
    printf '%s\n' "$FAKE_LEAN_PREFIX"
    exit 0
    ;;
  exe)
    shift
    [ "${1:-}" = leanllvm-loop-emit ] || {
      echo "lake: unexpected exe target: $*" >&2
      exit 3
    }
    ;;
  *)
    echo "lake: unexpected invocation: $*" >&2
    exit 3
    ;;
esac

pattern_hex=$(sed -nE 's/.*\^\^\^ (0x[0-9A-Fa-f]+).*$/\1/p' "$FAKE_LOOP_LEAN" | sed -n '1p')
[ -n "$pattern_hex" ] || {
  echo "lake: the Lean body fixture binds no delimiter pattern" >&2
  exit 3
}
pattern=$((pattern_hex))
[ "$pattern" -gt 0 ] || {
  echo "lake: the Lean body fixture's delimiter pattern is not a positive constant" >&2
  exit 3
}
substituted=0
awk -v pattern="$pattern" '
  /^  %[A-Za-z0-9_.]+ = xor i64 %arg, [0-9]+$/ {
    sub(/xor i64 %arg, [0-9]+$/, "xor i64 %arg, " pattern)
    substituted++
  }
  { print }
  END {
    if (substituted == 0) {
      print "lake: the loop body has no xor of %arg to bind" > "/dev/stderr"
      exit 3
    }
  }
' "$FAKE_LOOP_FIXTURE"
SHIM

  # clang: one minimal module, whatever the input.  The capture route extracts
  # the `define` blocks of @leanllvm_comma_mask8 and @l_commaMask8_go from it
  # and reduces them to one block each, so the module carries exactly those.
  cat > "$fakebin/clang" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"

out=
src=
args=("$@")
i=0
while [ "$i" -lt "${#args[@]}" ]; do
  case "${args[i]}" in
    -o) i=$((i + 1)); out=${args[i]} ;;
    -*) ;;
    *) src=${args[i]} ;;
  esac
  i=$((i + 1))
done
[ -n "$out" ] || { echo "clang: no output file" >&2; exit 1; }
{ [ -n "$src" ] && [ -f "$src" ]; } || { echo "clang: no source file" >&2; exit 1; }
{
  printf '; %s\n' "$(basename "$src")"
  printf 'source_filename = "%s"\n' "$(basename "$src")"
  printf 'target datalayout = "%s"\n' "$FAKE_DATALAYOUT"
  printf 'target triple = "%s"\n\n' "$FAKE_TARGET"
  cat <<'IR'
define i64 @leanllvm_comma_mask8(i64 %arg) {
entry:
  %m = xor i64 %arg, 42
  ret i64 %m
}

define i64 @l_commaMask8_go(i64 %arg) {
entry:
  ret i64 %arg
}
IR
} > "$out"
SHIM

  # opt: a pass-through copy for the passes the route runs, and success for
  # `verify`.
  cat > "$fakebin/opt" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail

out=
src=
verify=0
args=("$@")
i=0
while [ "$i" -lt "${#args[@]}" ]; do
  case "${args[i]}" in
    -o) i=$((i + 1)); out=${args[i]} ;;
    -passes=verify) verify=1 ;;
    -*) ;;
    *) src=${args[i]} ;;
  esac
  i=$((i + 1))
done
if [ "$verify" -eq 1 ]; then
  { [ -n "$src" ] && [ -f "$src" ]; } || { echo "opt: verify of no file" >&2; exit 1; }
  exit 0
fi
{ [ -n "$out" ] && [ -n "$src" ] && [ -f "$src" ]; } || {
  echo "opt: bad invocation" >&2
  exit 1
}
cp "$src" "$out"
SHIM

  chmod +x "$fakebin/lake" "$fakebin/clang" "$fakebin/opt"
  PATH="$fakebin:$PATH"
  export PATH

  set +e
  trap - ERR

  # --- affirmative control ------------------------------------------------
  # The lake shim must answer with the loop emission: the body bound to the
  # Lean fixture's pattern, still the memory-backed loop.  Without this the
  # run would not be able to tell an inert shim from a capture route that
  # leaves the fixture alone.
  control_ll=$work/control.emission.ll
  control_status=0
  "$fakebin/lake" exe leanllvm-loop-emit \
    > "$control_ll" 2> "$work/control.stderr" || control_status=$?
  parse_fn "$control_ll" > "$work/control.body.ll"
  control_operand=$(xor_constant "$work/control.body.ll")
  control_defect=$(memory_loop_defect "$work/control.body.ll")

  if [ "$control_status" -eq 0 ] &&
     [ "$control_operand" = "$new_pattern" ] &&
     [ -z "$control_defect" ]; then
    ok "control: the emission shim answers with the loop body bound to the Lean body's pattern ($new_pattern)"
  else
    echo "SETUP: the lake shim does not answer with the loop emission (status $control_status, constant '${control_operand:-none}', loop '${control_defect:-none}')" >&2
    sed 's/^/  lake stderr: /' "$work/control.stderr" >&2
    exit 3
  fi

  # --- near misses --------------------------------------------------------
  # The structural check is only evidence if it names a body that keeps every
  # instruction and breaks one relation, so each near miss is derived from the
  # control body and must be rejected.  A check that accepted one would be
  # counting tokens rather than binding the slots and the blocks.
  read -r cond_block body_block done_block <<<"$(
    awk '
      /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1) }
      /^  br i1 / {
        t = $5; f = $7
        sub(/,$/, "", t); sub(/,$/, "", f)
        sub(/^%/, "", t); sub(/^%/, "", f)
        print blk, t, f
        exit
      }
    ' "$work/control.body.ll"
  )"

  counter_slot=$(awk -v cond="$cond_block" '
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1) }
    blk == cond && $2 == "=" && $3 == "load" && $4 == "i64," && $5 == "ptr" {
      sub(/^%/, "", $6); print $6; exit
    }
  ' "$work/control.body.ll")

  { [ -n "$cond_block" ] && [ -n "$body_block" ] && [ -n "$done_block" ] &&
    [ -n "$counter_slot" ]; } || {
    echo "SETUP: the control body has no conditional loop to derive the near misses from" >&2
    exit 3
  }

  # The counter store moved out of the loop body into the fall-through block.
  awk -v body="$body_block" -v done="$done_block" -v slot="%$counter_slot" '
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == body && $1 == "store" && $2 == "i64" && $4 == "ptr" && $5 == slot {
      moved = $0; next
    }
    blk == done && /^  ret / && moved != "" { print moved; moved = "" }
    { print }
  ' "$work/control.body.ll" > "$work/miss.counter-in-done.ll"

  # The accumulator load removed from the loop body, its fall-through load kept.
  awk -v body="$body_block" -v slot="%$counter_slot" '
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == body && $2 == "=" && $3 == "load" && $4 == "i64," && $5 == "ptr" &&
      $6 != slot { next }
    { print }
  ' "$work/control.body.ll" > "$work/miss.acc-load-in-done.ll"

  # The back-edge from the loop body removed.
  awk -v body="$body_block" -v cond="$cond_block" '
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == body && $0 == "  br label %" cond { next }
    { print }
  ' "$work/control.body.ll" > "$work/miss.no-back-edge.ll"

  # The conditional branch's targets exchanged, so the fall-through block is
  # the true target and the loop body the false one.
  awk '
    /^  br i1 / {
      t = $5; sub(/,$/, "", t)
      print "  br i1 " $3 " label " $7 ", label " t
      next
    }
    { print }
  ' "$work/control.body.ll" > "$work/miss.swapped-edges.ll"

  # The comparison fed from a constant instead of the slot's load.
  awk -v cond="$cond_block" '
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == cond && $2 == "=" && $3 == "icmp" && $4 == "ult" {
      print "  " $1 " = icmp ult " $5 " 0, " $7
      next
    }
    { print }
  ' "$work/control.body.ll" > "$work/miss.constant-condition.ll"

  # The false branch pointed at a label the function never defines, so the
  # fall-through block the conditional promises does not exist.  The name is
  # derived so that no block of the control body can carry it.
  absent_label=absent_done
  while grep -qxF "$absent_label:" "$work/control.body.ll"; do
    absent_label="${absent_label}_x"
  done
  awk -v missing="$absent_label" '
    /^  br i1 / {
      line = $0
      sub(/%[A-Za-z0-9_.]+$/, "%" missing, line)
      print line
      next
    }
    { print }
  ' "$work/control.body.ll" > "$work/miss.absent-false-target.ll"

  for miss in counter-in-done acc-load-in-done no-back-edge swapped-edges \
    constant-condition absent-false-target; do
    miss_defect=$(memory_loop_defect "$work/miss.$miss.ll")
    if [ -n "$miss_defect" ]; then
      ok "near miss: the structural check names $miss ($miss_defect)"
    else
      echo "SETUP: the structural check accepts the near miss $miss" >&2
      exit 3
    fi
  done

  # The shift relation's own controls, derived from the same valid body: the
  # shift amount, the lane offset's multiplicand and its multiplier each get a
  # token-preserving edit that breaks only that binding, so a check that passed
  # them would be reading tokens rather than the relation.
  counter_load=$(awk -v cond="$cond_block" '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1) }
    blk == cond && $2 == "=" && $3 == "load" && strip_comma($4) == "i64" &&
      $5 == "ptr" {
      sub(/^%/, "", $1); print $1; exit
    }
  ' "$work/control.body.ll")

  lane_offset=$(awk -v body="$body_block" -v cload="%$counter_load" '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1) }
    blk == body && $2 == "=" && $3 == "mul" && strip_comma($4) == "i64" &&
      strip_comma($5) == cload {
      sub(/^%/, "", $1); print $1; exit
    }
  ' "$work/control.body.ll")

  xor_name=$(xor_result "$work/control.body.ll")

  { [ -n "$counter_load" ] && [ -n "$lane_offset" ] && [ -n "$xor_name" ]; } || {
    echo "SETUP: the control body has no counter load, lane offset and xor result to derive the shift near misses from" >&2
    exit 3
  }

  # The shift applied to a fixed constant rather than the lane offset's result.
  awk -v body="$body_block" -v value="%$xor_name" '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == body && $2 == "=" && $3 == "lshr" && strip_comma($4) == "i64" &&
      strip_comma($5) == value {
      print "  " $1 " = lshr i64 " $5 " 8"
      next
    }
    { print }
  ' "$work/control.body.ll" > "$work/miss.fixed-shift-amount.ll"

  # The lane offset multiplied from a constant rather than the counter load.
  awk -v body="$body_block" -v shift="%$lane_offset" -v cload="%$counter_load" '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == body && $1 == shift && $2 == "=" && $3 == "mul" &&
      strip_comma($4) == "i64" && strip_comma($5) == cload {
      print "  " $1 " = mul i64 1, " $6
      next
    }
    { print }
  ' "$work/control.body.ll" > "$work/miss.constant-multiplier-operand.ll"

  # The lane offset multiplied by a value other than 8.
  awk -v body="$body_block" -v shift="%$lane_offset" '
    function strip_comma(s) { sub(/,$/, "", s); return s }
    /^[A-Za-z0-9_.]+:$/ { blk = substr($0, 1, length($0) - 1); print; next }
    blk == body && $1 == shift && $2 == "=" && $3 == "mul" &&
      strip_comma($4) == "i64" {
      print "  " $1 " = mul i64 " $5 " 16"
      next
    }
    { print }
  ' "$work/control.body.ll" > "$work/miss.wrong-multiplier.ll"

  for miss in fixed-shift-amount constant-multiplier-operand \
    wrong-multiplier; do
    miss_defect=$(shift_lane_defect "$work/miss.$miss.ll")
    if [ -n "$miss_defect" ]; then
      ok "near miss: the shift relation check names $miss ($miss_defect)"
    else
      echo "SETUP: the shift relation check accepts the near miss $miss" >&2
      exit 3
    fi
  done

  # --- E1 -----------------------------------------------------------------
  capture_status=0
  (cd "$tree" && bash "$tree_ir/capture.sh") \
    > "$work/capture.stdout" 2> "$work/capture.stderr" || capture_status=$?

  if [ "$capture_status" -eq 0 ]; then
    ok "E1: the copied capture command exited 0"
  else
    bad "E1: the copied capture command exited $capture_status (stderr: $(tr '\n' ' ' < "$work/capture.stderr"))"
  fi

  body=$work/body.ll
  parse_fn "$tree_ir/loop.ll" > "$body"

  if [ -s "$body" ]; then
    ok "E1: the regenerated fixture carries the define block of @leanllvm_comma_mask8"
  else
    bad "E1: the regenerated fixture has no 'define i64 @leanllvm_comma_mask8(i64 %arg)' block (define lines: $(define_lines "$tree_ir/loop.ll"))"
  fi

  operand=$(xor_constant "$body")

  if [ -z "$operand" ]; then
    bad "E1: the loop body has no 'xor i64 %arg, <constant>' instruction"
  elif [ "$operand" != "$new_pattern" ]; then
    bad "E1: the loop body XORs %arg with $operand, not the Lean body's pattern $new_pattern (the fixture the tree starts with binds $old_operand)"
  else
    ok "E1: the loop body XORs %arg with the Lean body's pattern ($new_pattern)"
  fi

  if [ -s "$body" ]; then
    shift_defect=$(shift_lane_defect "$body")

    if [ -z "$shift_defect" ]; then
      ok "E1: the body shifts the xor result by the lane offset that is the SSA result of 'mul i64 <counter-load>, 8' in the loop body, from the counter the conditional block loads and tests"
    else
      bad "E1: the shift relation does not hold: $shift_defect"
    fi
  fi

  loop_defect=$(memory_loop_defect "$body")

  if [ -z "$loop_defect" ]; then
    ok "E1: the body allocates two entry slots, stores the counter slot after the conditional block loads it, loads the accumulator slot and stores that slot after the load, and branches back from the loop body to the counter comparison"
  else
    bad "E1: the body is not the memory-backed conditional loop: $loop_defect"
  fi

  printf 'capture status: %s\n' "$capture_status"
  printf 'capture stdout: %s\n' "$(cat "$work/capture.stdout")"
  sed 's/^/capture stderr: /' "$work/capture.stderr"
else
  driver=$repo/.lake/build/bin/leanllvm
  [ -x "$driver" ] || {
    echo "SETUP: no built driver at $driver" >&2
    exit 3
  }

  trap 'printf "SETUP: fixture construction failed: %s\n" "$BASH_COMMAND" >&2; exit 3' ERR
  set -e

  case_dir=$work/case
  mkdir -p "$case_dir"
  cp "$driver" "$case_dir/leanllvm"
  chmod +x "$case_dir/leanllvm"

  cat > "$case_dir/clean.ll" <<'IR'
define i64 @f(i64 %x) {
entry:
  ret i64 %x
}
IR

  # The attribute is carried in the header line and nowhere else in the input,
  # so a diagnostic naming it can only come from reading that header.
  if [ "$mode" = --return-attr ]; then
    label=E2
    attribute=range
    construct="return attribute 'range(i64 0, 1)'"
    cat > "$case_dir/header.ll" <<'IR'
; The return attribute constrains the value the function returns.
define range(i64 0, 1) i64 @f(i64 %x) {
entry:
  ret i64 %x
}
IR
  else
    label=E3
    attribute=noreturn
    construct="function attribute 'noreturn'"
    cat > "$case_dir/header.ll" <<'IR'
; The function attribute changes what the function promises its caller.
define i64 @f(i64 %x) noreturn {
entry:
  ret i64 %x
}
IR
  fi

  set +e
  trap - ERR

  # --- affirmative control ------------------------------------------------
  # The copied driver must rewrite an input with no attribute and leave an
  # output file, so the absence the refusal asserts is observable rather than
  # an artifact of a driver that never writes.
  control_status=0
  "$case_dir/leanllvm" --passes none "$case_dir/clean.ll" \
    -o "$case_dir/clean.out.ll" \
    > "$work/clean.stdout" 2> "$work/clean.stderr" || control_status=$?

  if [ "$control_status" -eq 0 ] && [ -s "$case_dir/clean.out.ll" ]; then
    ok "control: the copied driver rewrote the clean input and wrote $(wc -c < "$case_dir/clean.out.ll") bytes"
  else
    echo "SETUP: the copied driver did not rewrite the clean input (status $control_status)" >&2
    sed 's/^/  driver stderr: /' "$work/clean.stderr" >&2
    exit 3
  fi

  # --- the refusal --------------------------------------------------------
  status=0
  "$case_dir/leanllvm" --passes none "$case_dir/header.ll" \
    -o "$case_dir/out.ll" \
    > "$work/run.stdout" 2> "$work/run.stderr" || status=$?

  if [ "$status" -ne 0 ]; then
    ok "$label: the driver exited $status for a header carrying the $construct"
  else
    bad "$label: the driver exited 0 for a header carrying the $construct, so it accepted the function"
  fi

  if attribute_refusal "$work/run.stderr" "$attribute"; then
    ok "$label: the diagnostic says the $construct is unsupported or unmodelled"
  else
    bad "$label: no diagnostic line binds '$attribute' to an unsupported or unmodelled construct (stderr: $(tr '\n' ' ' < "$work/run.stderr"))"
  fi

  if [ ! -e "$case_dir/out.ll" ]; then
    ok "$label: no output file was created"
  else
    bad "$label: an output file was created at $case_dir/out.ll"
  fi

  printf 'driver status: %s\n' "$status"
  printf 'driver stdout: %s\n' "$(cat "$work/run.stdout")"
  sed 's/^/driver stderr: /' "$work/run.stderr"
fi

if [ "$fails" -ne 0 ]; then
  printf '%d assertion(s) failed\n' "$fails" >&2
  exit 1
fi
printf 'all assertions held\n'
