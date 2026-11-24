/-
`od_gap_recover` at its call boundary: the rule, the record it writes, and the
text it is the rule of.

The no-event body reaches `od_gap_recover` as an unresolved `call` (three call
sites, `probes/install/ir/stage2-noevent.candidate.ll:996`, `:1044`, `:1126`, and
the declaration at `:1201`).  This module supplies the model that the body's
selection needs: `stage2GapRecover`, a `Calls` entry, and its post at the call
boundary.

**What the helper does** (`kernel/json/stage2.c:898-929`).  It reads the cursor's
`b`, `n`, `ix`, `nix`, `k` and `e`, and the token's `pos`; it computes
`ip = (k < nix ? ix[k] : n)`, walks `ee` from `pos` to `ip` over non-whitespace,
and **writes nothing when `ee == ip`**.  Otherwise it takes the token's first
byte and refuses through one of four `err_set` sites — a malformed number at
`pos + ei`, a mismatched literal at `pos + ei`, a non-scalar first byte at `pos` —
and, past an accepted number or literal, writes the **unconditional**
second-token refusal at `s2` (the first non-whitespace after `ee`, or `ip` when
the window has none).  The two `#guard`s on that line below pin the absence of a
condition: the text's `err_set(c->e, s2, "extra token")` follows the loop
directly, so an accepted token whose gap is trailing whitespace still writes the
record, at `ip`.  `err_set` overwrites the record's three words and the three
refusing arms `return`, so exactly one site is reached and it is what a reader
observes.

**The two arguments.**  The fixture promotes the token's dead fields away and
passes `(ptr %c, i64 %t.0.val)` (`:1201`), so the model takes the cursor address
and the token's position as a word, not a pointer.  The token's other fields are
not read by the helper.

**The cursor's fields are read at the fixture's offsets.**  `%c` is the entry's
1192-byte local (`stage2-noevent.candidate.ll:57`), and the GEPs the body makes
into it fix the offsets: `0` for `b`, pinned by the fixture's
`store ptr %b, ptr %c` guard rather than by a new use in the rule, then `8`,
`16`, `24`, `32`, and `1112`.  The `#guard`s below assert those lines are in the
fixture, and a one-word mutation of the `e` offset is the control that the marker
discriminates.  The index word is the four-byte load `IXP(c->ix[c->k])` reads.

**The message word.**  The C writes the address of a string literal there
(`err_set(c->e, …, "number")`); the fragment has no module-global representation,
and the entry neither loads the word nor passes it out (`stage2-noevent.rewrites.tsv`
class r6: "nothing in the entry or the callees it reaches loads it, so the value
stored there is unconstrained").  The model therefore records a **tag** of which
`err_set` ran, not a pointer.  Each tag is tied to its literal by the `#guard` on
that `err_set` line.

**What this does not establish.**  The rule is a transcription of the helper's C
text, not a proof that the compiled object executes it: the pin says the lines
the rule encodes are lines of `kernel/json/stage2.c`, and the
transcription-to-instructions distance is `docs/contract.md` §7.6's trust row
(the same seam every helper model in `JsonStage2Body` stands on).  `pos ≤ ip` and
`ip ≤ length of the document read` are the staging's, not consequences here: the
rule's total form beyond that is a definition, and the entry answers `none` when
a read it needs is absent.
-/
import LeanLLVM.Refinement.JsonStage2Body

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_writeBytes_frame)

/-! ### The fixture's offsets, and the C text

`%c`'s fields are the offsets the pinned body addresses: `b` at `0` — pinned by
the fixture's `store ptr %b, ptr %c`, not a new use in the rule — and `n` at `8`,
`ix` at `16`, `nix` at `24`, `k` at `32`, `e` at `1112`.  The fixture is read
here only to pin those addresses; the body's own text is `JsonStage2NoEventIR`'s.
-/

/-- The pinned no-event body, as this module reads it. -/
def stage2NoEventFixture : String :=
  include_str "../../probes/install/ir/stage2-noevent.candidate.ll"

/-- `OdCur.n`: the document's length. -/
def odGapCurN : Nat := 8
/-- `OdCur.ix`: the index list. -/
def odGapCurIx : Nat := 16
/-- `OdCur.nix`: the index count. -/
def odGapCurNix : Nat := 24
/-- `OdCur.k`: the next index. -/
def odGapCurK : Nat := 32
/-- `OdCur.e`: the refusal record. -/
def odGapCurE : Nat := 1112

-- The cursor's six fields are the fixture's GEPs, at the offsets the model reads.
#guard occurs stage2NoEventFixture "store ptr %b, ptr %c"
#guard occurs stage2NoEventFixture "getelementptr inbounds i8, ptr %c, i64 8"
#guard occurs stage2NoEventFixture "getelementptr inbounds i8, ptr %c, i64 16"
#guard occurs stage2NoEventFixture "getelementptr inbounds i8, ptr %c, i64 24"
#guard occurs stage2NoEventFixture "getelementptr inbounds i8, ptr %c, i64 32"
#guard occurs stage2NoEventFixture "getelementptr inbounds i8, ptr %c, i64 1112"
-- The entry's cursor local is 1192 bytes, so the last field's word is inside it.
#guard occurs stage2NoEventFixture "call void @llvm.lifetime.start.p0(i64 1192, ptr %c)"
-- The call shape: two arguments, the cursor and the token's position as a word.
#guard occurs stage2NoEventFixture
  "declare void @od_gap_recover(ptr %c, i64 %t.0.val)"
#guard (stage2NoEventFixture.splitOn "call void @od_gap_recover(ptr %c, i64 %idxprom.lcssa)").length = 4
-- The control: the same search on a one-word mutation of the `e` offset reports
-- absence, so the markers above are about the fixture's text rather than a
-- search that would accept anything.
#guard !occurs stage2NoEventFixture "getelementptr inbounds i8, ptr %c, i64 1113"

-- The helper's own text, line by line, at `kernel/json/stage2.c:898-929`.
#guard occurs stage2Src "static void err_set(Err *e, uint64_t off, const char *msg) {"
#guard occurs stage2Src "static void od_gap_recover(OdCur *c, const OdTok *t) {"
#guard occurs stage2Src "const uint8_t *b = c->b;"
#guard occurs stage2Src "uint64_t ip = (c->k < c->nix) ? IXP(c->ix[c->k]) : c->n;"
#guard occurs stage2Src "uint64_t ee = t->pos;"
#guard occurs stage2Src "while (ee < ip && !is_ws(b[ee])) ee++;"
#guard occurs stage2Src "if (ee == ip) return;"
#guard occurs stage2Src "t2.end = ee;"
#guard occurs stage2Src "uint8_t ch = b[t2.pos];"
#guard occurs stage2Src "if (ch == '-' || (ch >= '0' && ch <= '9')) {"
#guard occurs stage2Src "if (!num_fast(b + t2.pos, t2.end - t2.pos, &d, &ei)) {"
#guard occurs stage2Src "err_set(c->e, t2.pos + ei, \"number\");"
#guard occurs stage2Src "if (ch == 't') { lit = \"true\"; ln = 4; }"
#guard occurs stage2Src "else if (ch == 'f') { lit = \"false\"; ln = 5; }"
#guard occurs stage2Src "else if (ch == 'n') { lit = \"null\"; ln = 4; }"
#guard occurs stage2Src "else { err_set(c->e, t2.pos, \"scalar\"); return; }"
#guard occurs stage2Src
  "if (!lit_check(b + t2.pos, t2.end - t2.pos, lit, ln, &ei)) {"
#guard occurs stage2Src "err_set(c->e, t2.pos + ei, \"literal\");"
#guard occurs stage2Src "uint64_t s2 = ee;"
#guard occurs stage2Src "while (s2 < ip && is_ws(b[s2])) s2++;"
#guard occurs stage2Src "err_set(c->e, s2, \"extra token\");"
-- The extra-token write is unconditional in the text: the loop is followed by
-- the `err_set` with nothing between them, and a guarded form is absent.
#guard !occurs stage2Src "if (s2 < ip) err_set(c->e, s2, \"extra token\");"
#guard !occurs stage2Src "if (s2 != ip) err_set(c->e, s2, \"extra token\");"
-- The whitespace test is the four-byte disjunction the model states.
#guard occurs stage2Src "return c == ' ' || c == '\\n' || c == '\\r' || c == '\\t';"
-- The number rule and the literal rule the model calls are the certified text's.
#guard occurs stage2Src "static int lit_check(const uint8_t *p, uint64_t n, const char *lit, uint32_t ln,"
#guard occurs stage2Src "#define num_fast num_fast_el1"
-- Controls: one-word mutations of the guarded lines are absent.
#guard !occurs stage2Src "if (ee == ip) continue;"
#guard !occurs stage2Src "while (ee < ip && is_ws(b[ee])) ee++;"
#guard !occurs stage2Src "err_set(c->e, t2.pos + ei, \"numbers\");"
#guard !occurs stage2Src "err_set(c->e, s2, \"extra tokens\");"

/-! ### The rule over the document's bytes

`gapRecoverWrite` is the helper's control flow over the document window the model
reads (`readBytes mem b ip`, so the window's length is `ip` and the loop's
`getD` never leaves it).  The two loops are the C's: the first stops at `ip` or
at whitespace, the second stops at `ip` or at the first non-whitespace.
-/

/-- `is_ws`, as the C spells it: space, newline, carriage return, tab. -/
def gapIsWs (c : UInt8) : Bool :=
  c = 0x20 || c = 0x0A || c = 0x0D || c = 0x09

/-- The first loop: the count of non-whitespace bytes at the front of `bytes`
(`ee` advancing while `ee < ip && !is_ws`). -/
def gapNonWsRun : Nat → List UInt8 → Nat
  | 0, _ => 0
  | Nat.succ _, [] => 0
  | Nat.succ k, b :: bs => if gapIsWs b then 0 else 1 + gapNonWsRun k bs

/-- The second loop: the count of whitespace bytes at the front of `bytes`
(`s2` advancing while `s2 < ip && is_ws`). -/
def gapWsRun : Nat → List UInt8 → Nat
  | 0, _ => 0
  | Nat.succ _, [] => 0
  | Nat.succ k, b :: bs => if gapIsWs b then 1 + gapWsRun k bs else 0

/-- `ee`: the first whitespace at or after `pos`, or `ip` when the window holds
none before it.  `bytes` is the document's first `ip` bytes. -/
def gapEe (bytes : List UInt8) (ip pos : Nat) : Nat :=
  pos + gapNonWsRun (ip - pos) (bytes.drop pos)

/-- `s2`: the first non-whitespace at or after `ee`, or `ip`. -/
def gapS2 (bytes : List UInt8) (ip ee : Nat) : Nat :=
  ee + gapWsRun (ip - ee) (bytes.drop ee)

/-- The token's window `[pos, ee)`: the lexeme `num_fast` and `lit_check` read. -/
def gapSegment (bytes : List UInt8) (pos ee : Nat) : List UInt8 :=
  (bytes.drop pos).take (ee - pos)

/-- The message tags the model writes in the record's message word.  The C writes
the address of the literal at the `err_set` line each tag names; the fragment has
no globals and nothing loads the word (rewrite r6), so the model records which
site ran. -/
def gapTagNumber : Nat := 1
def gapTagLiteral : Nat := 2
def gapTagScalar : Nat := 3
def gapTagExtra : Nat := 4

/-- The three literal byte strings the helper compares against. -/
def gapTrueLit : List UInt8 := [0x74, 0x72, 0x75, 0x65]
def gapFalseLit : List UInt8 := [0x66, 0x61, 0x6C, 0x73, 0x65]
def gapNullLit : List UInt8 := [0x6E, 0x75, 0x6C, 0x6C]

/-- **The observable the helper's write produces**: `none` for no write, `err off
tag` for the record's `(offset, message tag)`. -/
inductive GapWrite where
  /-- The call wrote nothing. -/
  | none
  /-- The call wrote the refusal record at `off`, with message tag `tag`. -/
  | err (off tag : Nat)
  deriving DecidableEq

/-- The last site in the text, and it is **unconditional**: past an accepted
number or literal, the first non-whitespace after `ee` (or `ip`) is written as a
second token, with no test before the `err_set`.  So a valid token followed only
by whitespace in the gap is still refused, at `ip`. -/
def gapExtraWrite (bytes : List UInt8) (ip ee : Nat) : GapWrite :=
  GapWrite.err (gapS2 bytes ip ee) gapTagExtra

/-- The literal arm: `lit_check`'s first differing position, or the accepted
fall-through to the extra-token test. -/
def gapLiteralWrite (bytes : List UInt8) (ip pos ee : Nat) (seg lit : List UInt8) :
    GapWrite :=
  match litCheck seg lit with
  | some i => GapWrite.err (pos + i) gapTagLiteral
  | none => gapExtraWrite bytes ip ee

/-- The decision after the first loop, at `ee`: `ch = b[pos]`, the number arm, the
three literal arms, and the scalar refusal.  This is a definition on its own so
that the `ee == ip` guard's contribution is the *model's* post-loop value at
`ee == ip` (`gapAfterLoop … ip ip`), not a second transcription. -/
def gapAfterLoop (bytes : List UInt8) (ip pos ee : Nat) : GapWrite :=
  let ch := bytes.getD pos 0
  let seg := gapSegment bytes pos ee
  if ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39) then
    if (numLexScan seg).2 then gapExtraWrite bytes ip ee
    else GapWrite.err (pos + (numLexScan seg).1) gapTagNumber
  else if ch = 0x74 then gapLiteralWrite bytes ip pos ee seg gapTrueLit
  else if ch = 0x66 then gapLiteralWrite bytes ip pos ee seg gapFalseLit
  else if ch = 0x6E then gapLiteralWrite bytes ip pos ee seg gapNullLit
  else GapWrite.err pos gapTagScalar

/-- **`od_gap_recover`'s rule** over the document window `[0, ip)` and the token's
`pos`: no write when the first loop reaches `ip`, and the post-loop decision
otherwise. -/
def gapRecoverWrite (bytes : List UInt8) (ip pos : Nat) : GapWrite :=
  let ee := gapEe bytes ip pos
  if ee = ip then GapWrite.none else gapAfterLoop bytes ip pos ee

/-! ### The case table

One witness per site the C text reaches: the no-write case, a number refusal with
internal whitespace, a literal refusal, a non-scalar first byte, the extra token
inside the gap, and the same unconditional write at `ip`.  `gapCases` is the
table and `gapCases_sound` is its statement; the entries' comments name the site
and the offset the C reaches. -/

/-- One row of the model's case table. -/
structure GapCase where
  /-- The site, in the C text's own words. -/
  site : String
  /-- The document window (`readBytes mem b ip`). -/
  bytes : List UInt8
  /-- The token's end boundary `ip`. -/
  ip : Nat
  /-- The token's start. -/
  pos : Nat
  /-- What the rule answers. -/
  expected : GapWrite

/-- The six sites the C text reaches, one witness each: no write, the number,
literal and scalar refusals, the extra token inside the gap, and the same
unconditional extra-token write at `ip` when the gap is trailing whitespace. -/
def gapCases : List GapCase :=
  [ { site := "no write (ee == ip)", bytes := [0x74, 0x72, 0x75, 0x65], ip := 4,
      pos := 0, expected := GapWrite.none },
    -- "1e x": the lexeme "1e" refuses at its second byte, `pos + 2`, although the
    -- window has whitespace in it.
    { site := "number refusal", bytes := [0x31, 0x65, 0x20, 0x78], ip := 4, pos := 0,
      expected := GapWrite.err 2 gapTagNumber },
    -- "tru x": `lit_check("tru", "true")` stops at 3 (the literal is longer).
    { site := "literal refusal", bytes := [0x74, 0x72, 0x75, 0x20, 0x78], ip := 4,
      pos := 0, expected := GapWrite.err 3 gapTagLiteral },
    -- "[ x": the first byte selects no arm, so the refusal is at `pos`.
    { site := "non-scalar first byte", bytes := [0x5B, 0x20, 0x78], ip := 3, pos := 0,
      expected := GapWrite.err 0 gapTagScalar },
    -- "12 3": the number is accepted, and the whitespace before "3" leaves a token.
    { site := "extra token", bytes := [0x31, 0x32, 0x20, 0x33], ip := 4, pos := 0,
      expected := GapWrite.err 3 gapTagExtra },
    -- "true ": the literal is accepted and the rest of the gap is whitespace, so
    -- `s2 = ip`: the unconditional write still refuses, at `ip`.
    { site := "extra token at ip", bytes := [0x74, 0x72, 0x75, 0x65, 0x20], ip := 5,
      pos := 0, expected := GapWrite.err 5 gapTagExtra } ]

/-- **The case table holds.**  The rule answers each row's expected value: a
refused number at `pos + ei`, a refused literal at `pos + ei`, a scalar refusal at
`pos`, an extra token at `s2` (or at `ip` when the gap is trailing whitespace),
and no write when `ee == ip`. -/
theorem gapCases_sound :
    gapCases.all (fun c => decide (gapRecoverWrite c.bytes c.ip c.pos = c.expected)) =
      true := by
  decide

-- The `ee == ip` guard is load-bearing: at "[" with `ip = 1` the first loop
-- reaches `ip`, and the rule returns with no write.  The post-loop decision at
-- the same `ee` would refuse the first byte as a scalar at `pos` — which is what
-- the guard suppresses.
#guard gapRecoverWrite [0x5B] 1 0 = GapWrite.none
#guard gapAfterLoop [0x5B] 1 0 1 = GapWrite.err 0 gapTagScalar

-- The control for the loop's bound: the byte at `ip` is not part of the segment,
-- so `"123"` with `ip = 2` has no gap and writes nothing.
#guard gapRecoverWrite [0x31, 0x32, 0x33] 2 0 = GapWrite.none

-- The last `err_set` wins where the C reaches it: a refused number returns, so
-- "1e 3" observes the number site at 2 even though "3" follows the whitespace;
-- an accepted number falls through, so "12 3" observes the extra-token site at 3,
-- and "true " observes it at `ip` with no second token in the window at all.
#guard gapRecoverWrite [0x31, 0x65, 0x20, 0x33] 4 0 = GapWrite.err 2 gapTagNumber
#guard gapRecoverWrite [0x31, 0x32, 0x20, 0x33] 4 0 = GapWrite.err 3 gapTagExtra
#guard gapRecoverWrite [0x74, 0x72, 0x75, 0x65, 0x20] 5 0 = GapWrite.err 5 gapTagExtra

-- The write is unconditional, as a statement about the definition rather than a
-- reading of the guards: every accepted-token fall-through has a second-token
-- record.
theorem gapExtraWrite_writes (bytes : List UInt8) (ip ee : Nat) :
    ∃ s2, gapExtraWrite bytes ip ee = GapWrite.err s2 gapTagExtra :=
  ⟨gapS2 bytes ip ee, rfl⟩

-- The literal bytes are the certified rule's, at the kinds `stage2Literal` names.
theorem gapTrueLit_eq : gapTrueLit = (stage2Literal 8).getD [] := rfl
theorem gapFalseLit_eq : gapFalseLit = (stage2Literal 9).getD [] := rfl
theorem gapNullLit_eq : gapNullLit = (stage2Literal 10).getD [] := rfl

/-! ### The call-boundary effect

The cursor's fields are reads at the fixture's offsets; `ip` is the index word
when `k < nix` and the document's length otherwise; the document window is
`readBytes mem b ip`.  A read the model needs and the memory does not hold makes
the call unresolved (`none`), which is the semantics' `ub`.
-/

/-- The effect a resolved call has on the caller's memory. -/
inductive GapRecoverEffect where
  /-- The helper wrote nothing. -/
  | unchanged
  /-- The helper wrote the refusal record at `e` with `(off, tag)`. -/
  | wrote (e off tag : Nat)

/-- Apply an effect to the caller's memory. -/
def GapRecoverEffect.apply (mem : Mem) : GapRecoverEffect → Mem
  | .unchanged => mem
  | .wrote e off tag => stage2ErrSetMsg mem e off tag

/-- **The helper at the cursor and the token's position**: `ip`, the document
window, the rule, and the record's write.  `none` is an unreadable field, an
unreadable index word, or an unreadable window — an unresolved call. -/
def stage2GapRecoverRule (mem : Mem) (c pos : Nat) : Option GapRecoverEffect :=
  match stage2ReadWord mem c 8, stage2ReadWord mem (c + odGapCurN) 8,
      stage2ReadWord mem (c + odGapCurIx) 8, stage2ReadWord mem (c + odGapCurNix) 8,
      stage2ReadWord mem (c + odGapCurK) 8, stage2ReadWord mem (c + odGapCurE) 8 with
  | some b, some n, some ix, some nix, some k, some e =>
      match (if k < nix then stage2ReadWord mem (ix + 4 * k) 4 else some n) with
      | none => none
      | some ip =>
          match readBytes mem b ip with
          | none => none
          | some bytes =>
              match gapRecoverWrite bytes ip pos with
              | GapWrite.none => some .unchanged
              | GapWrite.err off tag => some (.wrote e off tag)
  | _, _, _, _, _, _ => none

/-- **`od_gap_recover` as a `Calls` entry.**  It answers its own symbol and
nothing else; the two arguments are the cursor's address and the token's
position. -/
def stage2GapRecover (callee : String) (args : List Value) (mem : Mem) (next : Nat) :
    Option CallOutcome :=
  if callee = "od_gap_recover" then
    match args with
    | [.ptr c, .int 64 p] =>
        match stage2GapRecoverRule mem c p.toNat with
        | none => none
        | some eff => some { ret := voidRet, mem := eff.apply mem, next := next }
    | _ => none
  else none

/-- **The post at the call boundary**: a void answer at the caller's allocator,
and a memory that is the rule's effect — unchanged, or the record's three words
at one site. -/
def Stage2GapRecoverPost (mem : Mem) (next c pos : Nat) (out : CallOutcome) : Prop :=
  out.ret = voidRet ∧ out.next = next ∧
    ∃ eff, stage2GapRecoverRule mem c pos = some eff ∧ out.mem = eff.apply mem

/-- The entry answers only its own symbol. -/
theorem stage2GapRecover_other {callee : String} (h : callee ≠ "od_gap_recover")
    (args : List Value) (mem : Mem) (next : Nat) :
    stage2GapRecover callee args mem next = none := by
  unfold stage2GapRecover
  rw [ite_eq_right h]

/-- **Every answer is the post.**  The call resolves, its arguments are the
fixture's two, and its memory is the rule's effect at the cursor's refusal
record. -/
theorem stage2GapRecover_post {callee : String} {args : List Value} {mem : Mem}
    {next : Nat} {out : CallOutcome}
    (h : stage2GapRecover callee args mem next = some out) :
    callee = "od_gap_recover" ∧
      ∃ c p, args = [.ptr c, .int 64 p] ∧ Stage2GapRecoverPost mem next c p.toNat out := by
  unfold stage2GapRecover at h
  split at h
  · rename_i hcallee
    split at h
    · rename_i c p
      split at h
      · cases h
      · rename_i eff hr
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨hcallee, c, p, rfl, rfl, rfl, eff, hr, rfl⟩
    · cases h
  · cases h

/-- **The no-write answer**: the caller's memory comes back unchanged. -/
theorem stage2GapRecover_unchanged {mem : Mem} {next c : Nat} {p : BitVec 64}
    (h : stage2GapRecoverRule mem c p.toNat = some .unchanged) :
    stage2GapRecover "od_gap_recover" [.ptr c, .int 64 p] mem next =
      some { ret := voidRet, mem := mem, next := next } := by
  simp [stage2GapRecover, h, GapRecoverEffect.apply]

/-- **The refusal answer**: the record's three words at the rule's site. -/
theorem stage2GapRecover_wrote {mem : Mem} {next c e off tag : Nat} {p : BitVec 64}
    (h : stage2GapRecoverRule mem c p.toNat = some (.wrote e off tag)) :
    stage2GapRecover "od_gap_recover" [.ptr c, .int 64 p] mem next =
      some { ret := voidRet, mem := stage2ErrSetMsg mem e off tag, next := next } := by
  simp [stage2GapRecover, h, GapRecoverEffect.apply]

/-! ### The record's words, and the last write

`err_set` writes `ok = 0` at `e`, the offset at `e + 8`, and the message at
`e + 16`; `stage2ErrSetMsg` is those three stores.  The reads below are what a
caller observes, and the `last` lemmas are the overwrite: a second `err_set` on
the same record leaves the second `(off, msg)` where a reader looks.
-/

/-- A word written at its own address reads back there, at any width. -/
theorem readBytes_wordBytes_own {mem : Mem} {addr v w : Nat} :
    readBytes (writeBytes mem addr (wordBytes w v)) addr w = some (wordBytes w v) := by
  have h := readBytes_writeBytes_same mem (wordBytes w v) (addr := addr)
  rwa [show (wordBytes w v).length = w from natToBytes_length v w] at h

/-- The record's `ok` word after `err_set`. -/
theorem stage2ErrSetMsg_ok_read (mem : Mem) (e off tag : Nat) :
    readBytes (stage2ErrSetMsg mem e off tag) e 4 = some (wordBytes 4 0) := by
  unfold stage2ErrSetMsg stage2ErrSet
  rw [readBytes_wordBytes_frame (p := e) (n := 4) (by omega)]
  rw [readBytes_wordBytes_frame (p := e) (n := 4) (by omega)]
  exact readBytes_wordBytes_own

/-- The record's offset word after `err_set`. -/
theorem stage2ErrSetMsg_off_read (mem : Mem) (e off tag : Nat) :
    readBytes (stage2ErrSetMsg mem e off tag) (e + 8) 8 = some (wordBytes 8 off) := by
  unfold stage2ErrSetMsg stage2ErrSet
  rw [readBytes_wordBytes_frame (p := e + 8) (n := 8) (by omega)]
  exact readBytes_wordBytes_own

/-- The record's message word after `err_set`. -/
theorem stage2ErrSetMsg_msg_read (mem : Mem) (e off tag : Nat) :
    readBytes (stage2ErrSetMsg mem e off tag) (e + 16) 8 = some (wordBytes 8 tag) := by
  unfold stage2ErrSetMsg
  exact readBytes_wordBytes_own

/-- **The last `err_set` wins at the offset word**: a second record write on the
same record leaves its offset where a reader looks. -/
theorem stage2ErrSetMsg_last_off (mem : Mem) (e o1 t1 o2 t2 : Nat) :
    readBytes (stage2ErrSetMsg (stage2ErrSetMsg mem e o1 t1) e o2 t2) (e + 8) 8 =
      some (wordBytes 8 o2) := by
  unfold stage2ErrSetMsg stage2ErrSet
  rw [readBytes_wordBytes_frame (p := e + 8) (n := 8) (by omega)]
  exact readBytes_wordBytes_own

/-- **The last `err_set` wins at the message word.** -/
theorem stage2ErrSetMsg_last_msg (mem : Mem) (e o1 t1 o2 t2 : Nat) :
    readBytes (stage2ErrSetMsg (stage2ErrSetMsg mem e o1 t1) e o2 t2) (e + 16) 8 =
      some (wordBytes 8 t2) := by
  unfold stage2ErrSetMsg
  exact readBytes_wordBytes_own

/-- **The last `err_set` wins at the `ok` word** (all three sites write zero). -/
theorem stage2ErrSetMsg_last_ok (mem : Mem) (e o1 t1 o2 t2 : Nat) :
    readBytes (stage2ErrSetMsg (stage2ErrSetMsg mem e o1 t1) e o2 t2) e 4 =
      some (wordBytes 4 0) := by
  unfold stage2ErrSetMsg stage2ErrSet
  rw [readBytes_wordBytes_frame (p := e) (n := 4) (by omega)]
  rw [readBytes_wordBytes_frame (p := e) (n := 4) (by omega)]
  exact readBytes_wordBytes_own

-- The overwrite is a value a reader sees, not just a term: the second write's
-- offset and tag are the words at the record's two fields.
#guard readBytes (stage2ErrSetMsg (stage2ErrSetMsg [] 0 1 1) 0 2 3) 8 8 =
  some (wordBytes 8 2)
#guard readBytes (stage2ErrSetMsg (stage2ErrSetMsg [] 0 1 1) 0 2 3) 16 8 =
  some (wordBytes 8 3)
#guard readBytes (stage2ErrSetMsg (stage2ErrSetMsg [] 0 1 1) 0 2 3) 0 4 =
  some (wordBytes 4 0)

/-! ### Axiom footprints -/

#print axioms gapCases_sound
#print axioms gapExtraWrite_writes
#print axioms stage2GapRecover_post
#print axioms stage2GapRecover_unchanged
#print axioms stage2GapRecover_wrote
#print axioms stage2GapRecover_other
#print axioms stage2ErrSetMsg_last_off
#print axioms stage2ErrSetMsg_last_msg
#print axioms stage2ErrSetMsg_last_ok

end LeanLLVM.Refinement
