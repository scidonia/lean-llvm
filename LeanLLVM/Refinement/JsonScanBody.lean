/-
The JSON window scanner as an AST: the certified body, and the scalar body it is
compared with.

This module is the one definition of both bodies.  `lake exe
leanllvm-json-scan-emit` renders `scanWindowBody` with `LeanLLVM.Function.render`
into `probes/install/ir/json-scan-body.ll`, and `LeanLLVM/Refinement/JsonScanIR.lean`
parses that fixture at build time and pins it back to this AST.  The refinement
statement about the body is `JsonScanIR.scanWindowStatement` and is **not yet
proved**: `JsonScanIR.lean` proves the prefix facts the statement rests on, states
the band hypothesis the prose elided, and records in its header the
instruction-level step that remains.  The frame also stops at the caller's state
region, whose content the body writes as the rule's own words rather than as the
encoding's; that boundary is measured and the statement that pinned the slot's
bytes is refuted in `JsonScanIR`.  `scanWindowBaselineBody` is the scalar
byte-wise counterpart; its fixture and its instantiation of the same statement are
likewise outstanding.

The stop word is one word per refusal reason the lane rule can raise, and the
chain that chooses the `badUtf8` word tests the bad-continuation bit as well as the
bad-lead one (`%bad8`, below): a byte outside a pending requirement is the former,
a byte no character starts with is the latter, and testing the lead bit alone
leaves the `badUtf8` word unreachable on every continuation byte.

The definition lives here rather than in the proof module so that the emitter
does not depend on its own output: the proof module reads the fixture through
`include_str`, which the kernel only pins when the module is elaborated, so a
change to the body would otherwise have to be made by editing the fixture.

`probes/install/json/scan-window.candidate.c` is the same algorithm written in C
and captured, and it is *not* this body: it is the record of what the compiler
makes of the algorithm, and it is not certified.  This is the certified text, and
every instruction below is inside the subset `LeanLLVM.Semantics` models, so the
printer emits the function as it stands.

The shape is the one a `phi`-free loop forces.  The counter, the mask word, the
stop word and the carry all live in memory: the carry in the caller's 16-byte
state slot, the rest in `alloca`d cells the entry block reserves.  The lane body
is `select`-based, so no branch on a comparison chain over one byte exists (a
chain folds to a `switch`, which `Term` has no form for), and the structural mask
is computed scalar-ly from a two-word bit table rather than from a stored vector
product.  The state freezes at the first stop by a `select` on the stop word, and
the lane masks — quote, backslash and `b < 0x20` — come from the vector chain on
the full-window path.  A short window reads no vector: its skip bits are the
byte's own predicates, and each mask bit is or-ed with them, so one lane body
serves both.
-/
import LeanLLVM.Printer

namespace LeanLLVM.Refinement.JsonScanBody

open LeanLLVM

/-! ### Literals

Operands are written through these helpers so the instruction lists read as the
text they render to; a literal carries its own width, which is what the printer
recovers for a `getelementptr` index. -/

/-- A one-bit literal. -/
def lit1 (v : Nat) : Operand := .imm (.int 1 (BitVec.ofNat 1 v))

/-- A one-byte literal. -/
def lit8 (v : Nat) : Operand := .imm (.int 8 (BitVec.ofNat 8 v))

/-- A 32-bit literal. -/
def lit32 (v : Nat) : Operand := .imm (.int 32 (BitVec.ofNat 32 v))

/-- A 64-bit literal. -/
def lit64 (v : Nat) : Operand := .imm (.int 64 (BitVec.ofNat 64 v))

/-- A `splat` of thirty-two one-byte lanes. -/
def splat8 (v : Nat) : Operand := .imm (.splat 32 8 (BitVec.ofNat 8 v))

/-- The first word of the structural bit table: a byte `b < 64` sets bit `b` when
it is one of `{0x09, 0x0A, 0x0D, 0x20, 0x22, 0x2C, 0x3A}` — seven of RFC 8259's
whitespace and structural characters, the ones below `64`.  The rest of
`IsStructOrSpaceB`'s set, `{0x5B, 0x5C, 0x5D, 0x7B, 0x7D}`, is not representable
in this word and lives in `structHi`. -/
def structLo : Nat := 288247989812602368

/-- The second word: a byte `b` with `64 ≤ b < 128` sets bit `b - 64` when it is
one of `{0x5B, 0x5C, 0x5D, 0x7B, 0x7D}`; every other byte in that range, and
every byte above `0x7F`, takes the zero word. -/
def structHi : Nat := 2882303762456641536

/-! ### The lane body

One lane's instructions, in three pieces: the opening (the counter, the lane's
bit and the byte), the skip bits, and the byte rule with the memory it touches.
The two bodies differ only in the middle piece — the full-window path reads the
three vector masks, the scalar path tests the byte — so the rule, the mask
accumulator, the carry and the stop are one definition.
-/

/-- The lane's opening: the counter read back, its low thirty-two bits, the
lane's bit, the byte's address and the byte. -/
def laneHead : List Instr := [
  .load "%ki" (.int 64) (.reg "%k"),
  .trunc "%k32" 64 32 (.reg "%ki"),
  .binop "%one" .shl 32 (lit32 1) (.reg "%k32"),
  .gep "%bp" (.int 8) (.reg "%in") (.reg "%ki"),
  .load "%b" (.int 8) (.reg "%bp")]

/-- The full-window path's skip bits: the quote, backslash and `< 0x20` lane
masks, bit `k` of each, or-ed with the byte's own predicate.  The masks are the
vector chain's; the disjunct is what the short path, whose mask words are zero,
is decided by, and the two agree wherever both are present. -/
def maskedSkipBits : List Instr := [
  .load "%q0" (.int 32) (.reg "%qmp"),
  .binop "%q1" .lshr 32 (.reg "%q0") (.reg "%k32"),
  .binop "%q2" .and 32 (.reg "%q1") (lit32 1),
  .icmp "%q3" .ne 32 (.reg "%q2") (lit32 0),
  .icmp "%q4" .eq 8 (.reg "%b") (lit8 34),
  .binop "%qb" .or 1 (.reg "%q3") (.reg "%q4"),
  .load "%s0" (.int 32) (.reg "%smp"),
  .binop "%s1" .lshr 32 (.reg "%s0") (.reg "%k32"),
  .binop "%s2" .and 32 (.reg "%s1") (lit32 1),
  .icmp "%s3" .ne 32 (.reg "%s2") (lit32 0),
  .icmp "%s4" .eq 8 (.reg "%b") (lit8 92),
  .binop "%sb" .or 1 (.reg "%s3") (.reg "%s4"),
  .load "%c0" (.int 32) (.reg "%cmp"),
  .binop "%c1" .lshr 32 (.reg "%c0") (.reg "%k32"),
  .binop "%c2" .and 32 (.reg "%c1") (lit32 1),
  .icmp "%c3" .ne 32 (.reg "%c2") (lit32 0),
  .icmp "%c4" .ult 8 (.reg "%b") (lit8 32),
  .binop "%cb" .or 1 (.reg "%c3") (.reg "%c4")]

/-- The scalar path's skip bits: the same three predicates on the byte, with no
mask read at all. -/
def plainSkipBits : List Instr := [
  .icmp "%qb" .eq 8 (.reg "%b") (lit8 34),
  .icmp "%sb" .eq 8 (.reg "%b") (lit8 92),
  .icmp "%cb" .ult 8 (.reg "%b") (lit8 32)]

/-- Everything after the skip bits: the structural bit, the mask accumulator, the
carry, the stop, the freeze and the counter. -/
def ruleInstrs : List Instr := [
  -- the structural bit: the two-word table test, data flow rather than a
  -- comparison chain
  .zext "%b64" 8 64 (.reg "%b"),
  .binop "%bt" .and 64 (.reg "%b64") (lit64 63),
  .icmp "%g64" .ult 8 (.reg "%b") (lit8 64),
  .icmp "%g128" .ult 8 (.reg "%b") (lit8 128),
  .select "%t0" (.int 64) (.reg "%g128") (lit64 structHi) (lit64 0),
  .select "%t1" (.int 64) (.reg "%g64") (lit64 structLo) (.reg "%t0"),
  .binop "%sh" .lshr 64 (.reg "%t1") (.reg "%bt"),
  .binop "%sb1" .and 64 (.reg "%sh") (lit64 1),
  .icmp "%stb" .ne 64 (.reg "%sb1") (lit64 0),
  -- the structural mask accumulator
  .load "%m0" (.int 32) (.reg "%maskp"),
  .binop "%m1" .or 32 (.reg "%m0") (.reg "%one"),
  .select "%m2" (.int 32) (.reg "%stb") (.reg "%m1") (.reg "%m0"),
  .store (.int 32) (.reg "%m2") (.reg "%maskp"),
  -- the carry, as the slot's four words, and the stop word
  .load "%f" (.int 32) (.reg "%state"),
  .gep "%sp4" (.int 8) (.reg "%state") (lit32 4),
  .load "%nw" (.int 32) (.reg "%sp4"),
  .gep "%sp8" (.int 8) (.reg "%state") (lit32 8),
  .load "%lo" (.int 32) (.reg "%sp8"),
  .gep "%sp12" (.int 8) (.reg "%state") (lit32 12),
  .load "%hi" (.int 32) (.reg "%sp12"),
  .load "%stp" (.int 32) (.reg "%stopp"),
  -- the byte rule's conditions, in its own order
  .icmp "%live" .eq 32 (.reg "%stp") (lit32 0),
  .binop "%innb" .and 32 (.reg "%f") (lit32 1),
  .icmp "%inn" .ne 32 (.reg "%innb") (lit32 0),
  .binop "%oddb" .and 32 (.reg "%f") (lit32 2),
  .icmp "%odd" .ne 32 (.reg "%oddb") (lit32 0),
  .binop "%ninn" .xor 1 (.reg "%inn") (lit1 1),
  .icmp "%mre" .ne 32 (.reg "%nw") (lit32 0),
  .icmp "%nmre" .eq 32 (.reg "%nw") (lit32 0),
  .binop "%lov" .and 32 (.reg "%lo") (lit32 255),
  .binop "%hiv" .and 32 (.reg "%hi") (lit32 255),
  .zext "%b32" 8 32 (.reg "%b"),
  .icmp "%ilo" .ule 32 (.reg "%lov") (.reg "%b32"),
  .icmp "%ihi" .ule 32 (.reg "%b32") (.reg "%hiv"),
  .binop "%irg" .and 1 (.reg "%ilo") (.reg "%ihi"),
  .binop "%nirg" .xor 1 (.reg "%irg") (lit1 1),
  .binop "%uok" .and 1 (.reg "%mre") (.reg "%irg"),
  .binop "%ubad" .and 1 (.reg "%mre") (.reg "%nirg"),
  .binop "%nod" .and 1 (.reg "%nmre") (.reg "%odd"),
  .binop "%nodd" .xor 1 (.reg "%odd") (lit1 1),
  .binop "%npm" .and 1 (.reg "%nmre") (.reg "%nodd"),
  .binop "%aq" .and 1 (.reg "%npm") (.reg "%qb"),
  .binop "%aqo" .and 1 (.reg "%aq") (.reg "%ninn"),
  .binop "%aqc" .and 1 (.reg "%aq") (.reg "%inn"),
  .binop "%nq" .xor 1 (.reg "%qb") (lit1 1),
  .binop "%npq" .and 1 (.reg "%npm") (.reg "%nq"),
  .binop "%abs" .and 1 (.reg "%npq") (.reg "%sb"),
  .binop "%absin" .and 1 (.reg "%abs") (.reg "%inn"),
  .binop "%nbs" .xor 1 (.reg "%sb") (lit1 1),
  .binop "%npb" .and 1 (.reg "%npq") (.reg "%nbs"),
  .binop "%ib" .and 1 (.reg "%npb") (.reg "%inn"),
  .binop "%ncb" .xor 1 (.reg "%cb") (lit1 1),
  .binop "%actl" .and 1 (.reg "%ib") (.reg "%cb"),
  .binop "%leadb" .and 1 (.reg "%ib") (.reg "%ncb"),
  .icmp "%asc" .ult 8 (.reg "%b") (lit8 128),
  .binop "%nasc" .xor 1 (.reg "%asc") (lit1 1),
  .binop "%lead" .and 1 (.reg "%leadb") (.reg "%nasc"),
  .icmp "%lge" .uge 8 (.reg "%b") (lit8 194),
  .icmp "%lle" .ule 8 (.reg "%b") (lit8 244),
  .binop "%lok" .and 1 (.reg "%lge") (.reg "%lle"),
  .binop "%nlok" .xor 1 (.reg "%lok") (lit1 1),
  .binop "%lbad" .and 1 (.reg "%lead") (.reg "%nlok"),
  .binop "%lset" .and 1 (.reg "%lead") (.reg "%lok"),
  -- the fast skip: the three mask bits clear, inside, no run, no sequence, and
  -- the byte printable ASCII
  .binop "%sk0" .and 1 (.reg "%inn") (.reg "%nodd"),
  .binop "%sk1" .and 1 (.reg "%sk0") (.reg "%nmre"),
  .binop "%sk2" .and 1 (.reg "%sk1") (.reg "%nq"),
  .binop "%sk3" .and 1 (.reg "%sk2") (.reg "%nbs"),
  .binop "%sk4" .and 1 (.reg "%sk3") (.reg "%ncb"),
  .binop "%skip" .and 1 (.reg "%sk4") (.reg "%asc"),
  -- the lead byte's requirement, as the rule's nine classes collapse to it: the
  -- accepted range is `[0xC2, 0xF4]`, the count is its top class, and the two
  -- bounds are the two bytes whose ranges differ from the class's own
  .icmp "%b3" .uge 8 (.reg "%b") (lit8 240),
  .icmp "%b2" .uge 8 (.reg "%b") (lit8 224),
  .select "%n3v" (.int 32) (.reg "%b3") (lit32 3) (lit32 2),
  .select "%nc" (.int 32) (.reg "%b2") (.reg "%n3v") (lit32 1),
  .icmp "%e0" .eq 8 (.reg "%b") (lit8 224),
  .icmp "%f0" .eq 8 (.reg "%b") (lit8 240),
  .select "%lc0" (.int 32) (.reg "%f0") (lit32 144) (lit32 128),
  .select "%lc" (.int 32) (.reg "%e0") (lit32 160) (.reg "%lc0"),
  .icmp "%q1b" .eq 8 (.reg "%b") (lit8 237),
  .icmp "%q2b" .eq 8 (.reg "%b") (lit8 244),
  .select "%hc0" (.int 32) (.reg "%q2b") (lit32 143) (lit32 191),
  .select "%hc" (.int 32) (.reg "%q1b") (lit32 159) (.reg "%hc0"),
  -- the status word this lane raises, and the first stop.  `%wbd` is the
  -- refusal a byte outside a pending requirement raises, and the rule reaches
  -- it two ways — a bad lead byte (`%lbad`) or a bad continuation byte
  -- (`%ubad`) — so the chain that chooses it tests both; testing the lead bit
  -- alone leaves `%wbd` unreachable on every continuation byte.
  .binop "%lane1" .add 32 (.reg "%k32") (lit32 1),
  .binop "%wcl" .add 32 (.reg "%lane1") (lit32 64),
  .binop "%wct" .add 32 (.reg "%lane1") (lit32 640),
  .binop "%wbd" .add 32 (.reg "%lane1") (lit32 896),
  .binop "%bad8" .or 1 (.reg "%ubad") (.reg "%lbad"),
  .select "%sw0" (.int 32) (.reg "%bad8") (.reg "%wbd") (.reg "%wct"),
  .select "%sw1" (.int 32) (.reg "%actl") (.reg "%wct") (.reg "%sw0"),
  .select "%sw2" (.int 32) (.reg "%aqc") (.reg "%wcl") (.reg "%sw1"),
  .binop "%ras" .or 1 (.reg "%ubad") (.reg "%actl"),
  .binop "%ras2" .or 1 (.reg "%ras") (.reg "%lbad"),
  .binop "%raise" .or 1 (.reg "%ras2") (.reg "%aqc"),
  .binop "%stp0" .and 1 (.reg "%live") (.reg "%raise"),
  .select "%stpn" (.int 32) (.reg "%stp0") (.reg "%sw2") (.reg "%stp"),
  .store (.int 32) (.reg "%stpn") (.reg "%stopp"),
  .binop "%nact" .xor 1 (.reg "%skip") (lit1 1),
  .binop "%act" .and 1 (.reg "%live") (.reg "%nact"),
  -- the carry's four words as the rule leaves them
  .binop "%nw0" .sub 32 (.reg "%nw") (lit32 1),
  .binop "%fc0" .xor 32 (.reg "%f") (lit32 2),
  .select "%f1" (.int 32) (.reg "%nod") (.reg "%fc0") (.reg "%f"),
  .binop "%fq1" .or 32 (.reg "%f1") (lit32 1),
  .select "%f2" (.int 32) (.reg "%aqo") (.reg "%fq1") (.reg "%f1"),
  .binop "%fb1" .or 32 (.reg "%f2") (lit32 2),
  .select "%f3" (.int 32) (.reg "%absin") (.reg "%fb1") (.reg "%f2"),
  .select "%cw0" (.int 32) (.reg "%uok") (.reg "%nw0") (.reg "%nw"),
  .select "%cw1" (.int 32) (.reg "%lset") (.reg "%nc") (.reg "%cw0"),
  .select "%lw0" (.int 32) (.reg "%uok") (lit32 128) (.reg "%lov"),
  .select "%lw1" (.int 32) (.reg "%lset") (.reg "%lc") (.reg "%lw0"),
  .select "%hw0" (.int 32) (.reg "%uok") (lit32 191) (.reg "%hiv"),
  .select "%hw1" (.int 32) (.reg "%lset") (.reg "%hc") (.reg "%hw0"),
  .select "%fout" (.int 32) (.reg "%act") (.reg "%f3") (.reg "%f"),
  .select "%cout" (.int 32) (.reg "%act") (.reg "%cw1") (.reg "%nw"),
  .select "%lout" (.int 32) (.reg "%act") (.reg "%lw1") (.reg "%lo"),
  .select "%hout" (.int 32) (.reg "%act") (.reg "%hw1") (.reg "%hi"),
  .store (.int 32) (.reg "%fout") (.reg "%state"),
  .store (.int 32) (.reg "%cout") (.reg "%sp4"),
  .store (.int 32) (.reg "%lout") (.reg "%sp8"),
  .store (.int 32) (.reg "%hout") (.reg "%sp12"),
  -- the counter
  .binop "%kn" .add 64 (.reg "%ki") (lit64 1),
  .store (.int 64) (.reg "%kn") (.reg "%k")]

/-! ### The two bodies -/

/-- The cells every body carries, and the window's length as an `i64`: the
counter, the mask word and the stop word, allocated in that order and zeroed. -/
def entryCoreInstrs : List Instr := [
  .alloca "%k" (.int 64) 8,
  .alloca "%maskp" (.int 32) 4,
  .alloca "%stopp" (.int 32) 4,
  .zext "%v64" 32 64 (.reg "%valid"),
  .store (.int 64) (lit64 0) (.reg "%k"),
  .store (.int 32) (lit32 0) (.reg "%maskp"),
  .store (.int 32) (lit32 0) (.reg "%stopp")]

/-- The three mask words, zeroed: a short window reads no vector, so its skip
bits are its own byte's and these words stay zero. -/
def entryMaskInstrs : List Instr := [
  .alloca "%qmp" (.int 32) 4,
  .alloca "%smp" (.int 32) 4,
  .alloca "%cmp" (.int 32) 4,
  .store (.int 32) (lit32 0) (.reg "%qmp"),
  .store (.int 32) (lit32 0) (.reg "%smp"),
  .store (.int 32) (lit32 0) (.reg "%cmp")]

/-- The path test: `%short` is set exactly when the window is shorter than
thirty-two bytes, and the entry block takes the scalar path when it is.  Taking
the vector path on a short window would read bytes the caller has not promised,
which is why the branch is on `%short` and not on its complement. -/
def entryPathInstrs : List Instr := [
  .icmp "%short" .ne 32 (.reg "%valid") (lit32 32)]

/-- The full-window path: one vector load of the thirty-two readable bytes, the
three lane masks over it, and the three mask words. -/
def wideInstrs : List Instr := [
  .load "%vv" (.vec 32 (.int 8)) (.reg "%in"),
  .icmpVec "%qv" .eq 32 8 (.reg "%vv") (splat8 34),
  .bitcastMask "%qm" 32 (.reg "%qv"),
  .icmpVec "%sv" .eq 32 8 (.reg "%vv") (splat8 92),
  .bitcastMask "%sm" 32 (.reg "%sv"),
  .icmpVec "%cv" .ult 32 8 (.reg "%vv") (splat8 32),
  .bitcastMask "%cm" 32 (.reg "%cv"),
  .store (.int 32) (.reg "%qm") (.reg "%qmp"),
  .store (.int 32) (.reg "%sm") (.reg "%smp"),
  .store (.int 32) (.reg "%cm") (.reg "%cmp")]

/-- The loop condition: the counter against the window's length. -/
def condInstrs : List Instr := [
  .load "%kc" (.int 64) (.reg "%k"),
  .icmp "%lt" .ult 64 (.reg "%kc") (.reg "%v64")]

/-- The exit: the mask word is written to `%out`, and the stop word is the
status the unit returns. -/
def doneInstrs : List Instr := [
  .load "%rm" (.int 32) (.reg "%maskp"),
  .store (.int 32) (.reg "%rm") (.reg "%out"),
  .load "%rs" (.int 32) (.reg "%stopp")]

/-- The unit's symbol, as the AST names it. -/
def scanName : String := "leanllvm_json_scan_window"

/-- The scalar body's symbol: the same algorithm, one lane at a time, with no
vector type in it. -/
def scanScalarName : String := "leanllvm_json_scan_window_scalar"

/-- The unit's parameters: the window, the mask's slot, the carry's slot, and the
number of bytes to scan. -/
def scanParams : List (String × Ty) :=
  [("%in", .ptr), ("%out", .ptr), ("%state", .ptr), ("%valid", .int 32)]

/-- The certified body: the full-window path's masks over the three skip bits,
the one lane body, and the memory-carried counter, carry and stop. -/
def scanWindowBody : Function :=
  { name := scanName, retTy := .int 32, params := scanParams,
    blocks := [
      { name := "entry", instrs := entryCoreInstrs ++ entryMaskInstrs ++ entryPathInstrs,
        term := .condbr (.reg "%short") "cond" "wide" },
      { name := "wide", instrs := wideInstrs, term := .br "cond" },
      { name := "cond", instrs := condInstrs, term := .condbr (.reg "%lt") "body" "done" },
      { name := "body", instrs := laneHead ++ maskedSkipBits ++ ruleInstrs, term := .br "cond" },
      { name := "done", instrs := doneInstrs, term := .ret (.int 32) (some (.reg "%rs")) }] }

/-- The scalar body: one lane at a time, the byte rule spelled out, no vector
type, no mask word and no path test.  It is the same lane body with the byte's
own predicates as its skip bits, and it is the pair's baseline. -/
def scanWindowBaselineBody : Function :=
  { name := scanScalarName, retTy := .int 32, params := scanParams,
    blocks := [
      { name := "entry", instrs := entryCoreInstrs, term := .br "cond" },
      { name := "cond", instrs := condInstrs, term := .condbr (.reg "%lt") "body" "done" },
      { name := "body", instrs := laneHead ++ plainSkipBits ++ ruleInstrs, term := .br "cond" },
      { name := "done", instrs := doneInstrs, term := .ret (.int 32) (some (.reg "%rs")) }] }

end LeanLLVM.Refinement.JsonScanBody
