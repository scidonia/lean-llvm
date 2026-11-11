/-
The decoder's loop invariant, stated against the specification's own recursion.

`escapeDecodeGo` is the walk the expander's record claims (`JsonEscapeSpec`), and
the pinned `@us_dec_x` is one loop over the caller's position list.  Relating the
two needs a vocabulary in which a state of the body's loop is a state of the walk:
a byte cursor, the position index, an output prefix, and the remaining positions.
The remaining list is the document's own list after `k` entries, which is the list
`escapeDecodeGo` itself walks, so each step of the body is one unfolding of the
specification's recursion rather than a second walk that agrees on examples.

The measured signature carries the position cursor **in and out** (`*xj`), so the
clause is written at the caller's baseline: a staging that resumes at `k0 > 0` seeds
the invariant at `k = k0` with the list already dropped, and the fresh call is the
`k0 = 0` case of the same clause rather than the definition the clause is written
at.  `goal` is a parameter for the same reason: it is the outcome the caller's
staging names, not a term fixed by the body.

What is *not* here is the body side — the `runFuel` trace that carries a
`DecodeInv` from one iteration to the next — and the note at the end of this file
records where the assembly stops.
-/
import LeanLLVM.Refinement.JsonEscapeSteps
import LeanLLVM.Refinement.LoopFuel

set_option maxRecDepth 8000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonScanSpec

/-! ### The walk's step laws

Each law fixes `escapeDecodeGo` at a head whose bytes the shape names.  They are
the definition unfolded once, packaged so a step of the body can name the outcome
it produces without re-unfolding the recursion at every use. -/

/-- The walk's base case: no positions left, so the rest of the body is copied. -/
theorem escapeDecodeGo_nil (bs : List UInt8) (i k : Nat) (out : List UInt8) :
    escapeDecodeGo bs i k [] out = .decoded (out ++ bs.drop i) k := rfl

/-- A control byte inside a string is a refusal at its own offset. -/
theorem escapeDecodeGo_step_control {bs : List UInt8} {i q k : Nat} {qs : List Nat}
    {out : List UInt8} {b : UInt8}
    (hb : bs[q]? = some b) (hlt : q < bs.length) (hctl : IsControlB b = true) :
    escapeDecodeGo bs i k (q :: qs) out = .refused q (k + 1) := by
  simp [escapeDecodeGo, show ¬ bs.length ≤ q from by omega, hb, hctl]

/-- A byte that is not an escape is a refusal at its own offset. -/
theorem escapeDecodeGo_step_refuse {bs : List UInt8} {i q k : Nat} {qs : List Nat}
    {out : List UInt8} {b : UInt8}
    (hb : bs[q]? = some b) (hlt : q < bs.length) (hctl : IsControlB b = false)
    (hesc : escapeAt bs q = none) :
    escapeDecodeGo bs i k (q :: qs) out = .refused q (k + 1) := by
  simp [escapeDecodeGo, show ¬ bs.length ≤ q from by omega, hb, hctl, hesc]

/-- A two-character escape: the body copies up to it, appends its byte, and the
walk continues two bytes on. -/
theorem escapeDecodeGo_step_simple {bs : List UInt8} {i q k : Nat} {qs : List Nat}
    {out : List UInt8} {b e : UInt8}
    (hb : bs[q]? = some b) (hlt : q < bs.length) (hctl : IsControlB b = false)
    (hesc : escapeAt bs q = some ([e], 2)) :
    escapeDecodeGo bs i k (q :: qs) out =
      escapeDecodeGo bs (q + 2) (k + 1) qs
        (out ++ (bs.drop i).take (q - i) ++ [e]) := by
  simp [escapeDecodeGo, show ¬ bs.length ≤ q from by omega, hb, hctl, hesc]

/-- A `\u` escape whose code unit is its own: the walk continues six bytes on. -/
theorem escapeDecodeGo_step_six {bs : List UInt8} {i q k : Nat} {qs : List Nat}
    {out : List UInt8} {b : UInt8} {cp : Nat}
    (hb : bs[q]? = some b) (hlt : q < bs.length) (hctl : IsControlB b = false)
    (hesc : escapeAt bs q = some (utf8Encode cp, 6)) :
    escapeDecodeGo bs i k (q :: qs) out =
      escapeDecodeGo bs (q + 6) (k + 1) qs
        (out ++ (bs.drop i).take (q - i) ++ utf8Encode cp) := by
  simp [escapeDecodeGo, show ¬ bs.length ≤ q from by omega, hb, hctl, hesc]

/-- A surrogate pair: the walk continues twelve bytes on, consumes the second
position of the pair, and appends the pair's code point. -/
theorem escapeDecodeGo_step_pair {bs : List UInt8} {i q k : Nat} {qs : List Nat}
    {out : List UInt8} {b : UInt8} {cp' : Nat}
    (hb : bs[q]? = some b) (hlt : q < bs.length) (hctl : IsControlB b = false)
    (hesc : escapeAt bs q = some (utf8Encode cp', 12)) :
    escapeDecodeGo bs i k (q :: qs) out =
      escapeDecodeGo bs (q + 12) (k + 2) (qs.drop 1)
        (out ++ (bs.drop i).take (q - i) ++ utf8Encode cp') := by
  cases qs with
  | nil => simp [escapeDecodeGo, show ¬ bs.length ≤ q from by omega, hb, hctl, hesc]
  | cons q' qs' => simp [escapeDecodeGo, show ¬ bs.length ≤ q from by omega, hb, hctl, hesc]

/-! ### The invariant

The body's loop, as a state of the walk.  `i` is `%i.0295`'s byte cursor, `k` is the
position index `%k.1296` reads, `out` is the decoded prefix the store holds at
`%j.0294`, and `goal` is the outcome the caller's staging names.  The remaining
positions are `(escAt body st 0).drop k` — the document's list after `k` entries —
which is the list `escapeDecodeGo` itself walks.

The count is the position *index*, not a call-relative count, which is what the
measured signature carries: `*xj` enters at the caller's `k0` and leaves at the
index the last processed position reached.  A staging that resumes at `k0 > 0`
therefore seeds the invariant at `k = k0` with the list already dropped, and the
walk's own accumulated count is the `k0 + consumed` the record's `*xj` clause names.

The prefix is bounded by the cursor: `prefix_le_cursor` says the decoded bytes never
run past the bytes consumed, which is the relation a caller needs before it copies
the body's remainder after the prefix.  It is a field rather than a consequence of
`walk`, because a refusal drops the prefix and so satisfies `walk` with any prefix
at all; the clause therefore holds unconditionally or not at all. -/

structure DecodeInv (body : List UInt8) (st : ClassState) (M : Mem) (dst nps : Nat)
    (i k : Nat) (out : List UInt8) (goal : EscapeOutcome) : Prop where
  /-- The walk from here is the caller's outcome: this is the specification's own
  recursion, not a second vocabulary. -/
  walk : escapeDecodeGo body i k ((escAt body st 0).drop k) out = goal
  /-- The decoded prefix, in the store, at its own length. -/
  stored : readBytes M dst out.length = some out
  /-- The document's position list is `nps` long. -/
  length : (escAt body st 0).length = nps
  /-- **The decoded prefix never runs past the byte cursor.**  Every step appends at
  most the bytes it consumes, so a reachable state has written no more than it has
  read; the `Spaced` hypothesis carries the per-step inequality.

  It is a field rather than a consequence of `walk` because a refusal drops the
  prefix: `escapeDecodeGo` returns the same refused outcome for every `out` at a
  refusing position, so any prefix satisfies `walk` there
  (`escapeDecodeGo_refusal_ignores_prefix`).  The clause is therefore needed
  unconditionally, and it is the bound the copy at the latch reads as
  `out.length + (n - i) ≤ n` (`DecodeInv.capacity`). -/
  prefix_le_cursor : out.length ≤ i

/-- **The invariant's seed.**  The loop is entered with the byte cursor at zero and
nothing written, and with the position index at the caller's `k0`: the walk from
there is the staging's own outlined decode, so the relation is inhabited before the
first iteration whether the call is fresh or resumed. -/
theorem decodeInv_seed {body : List UInt8} {st : ClassState} {M : Mem} {dst nps k0 : Nat}
    (hlist : (escAt body st 0).length = nps) :
    DecodeInv body st M dst nps 0 k0 []
      (escapeDecodeGo body 0 k0 ((escAt body st 0).drop k0) []) where
  walk := rfl
  stored := rfl
  length := hlist
  prefix_le_cursor := Nat.zero_le _

/-- **The step at a refusal.**  The walk refuses at the same offset and with the
same count the body's `%err` and `%xj` stores carry. -/
theorem DecodeInv.step_refuse {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat} {b : UInt8}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false) (hesc : escapeAt body q = none) :
    goal = .refused q (k + 1) := by
  rw [← hinv.walk, hhead]
  exact escapeDecodeGo_step_refuse hb hlt hctl hesc

/-- The step at a control byte, which is the refusal with the control test's
condition. -/
theorem DecodeInv.step_control {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat} {b : UInt8}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = true) :
    goal = .refused q (k + 1) := by
  rw [← hinv.walk, hhead]
  exact escapeDecodeGo_step_control hb hlt hctl

/-- **The step at a two-character escape.**  The output prefix grows by the bytes
copied up to the position and the escape's own byte, and the walk continues two
bytes on with the index advanced by one. -/
theorem DecodeInv.step_simple {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat} {b c1 e : UInt8}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q+1]? = some c1) (hs : simpleEscape c1 = some e) :
    goal = escapeDecodeGo body (q + 2) (k + 1) ((escAt body st 0).drop (k + 1))
      (out ++ (body.drop i).take (q - i) ++ [e]) := by
  have hshape : escapeAt body q = some ([e], 2) := by
    simp [escapeAt, h1, hs]
  rw [← hinv.walk, hhead]
  exact escapeDecodeGo_step_simple hb hlt hctl hshape

/-- **The step at a `\u` escape whose unit stands alone.**  The walk continues six
bytes on and the index advances by one. -/
theorem DecodeInv.step_six {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat} {b : UInt8}
    {cp : Nat}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q+1]? = some 0x75) (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = none) :
    goal = escapeDecodeGo body (q + 6) (k + 1) ((escAt body st 0).drop (k + 1))
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp) := by
  have hu : simpleEscape (0x75 : UInt8) = none := by decide
  have hshape : escapeAt body q = some (utf8Encode cp, 6) := by
    simp [escapeAt, h1, hx, ht, hu]
  rw [← hinv.walk, hhead]
  exact escapeDecodeGo_step_six hb hlt hctl hshape

/-- **The step at a surrogate pair.**  The walk continues twelve bytes on, the
index advances by two — the second `\u` is a position of its own — and the remaining
list loses both entries. -/
theorem DecodeInv.step_pair {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat} {b : UInt8}
    {cp cp' : Nat}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q+1]? = some 0x75) (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = some (cp', 12)) :
    goal = escapeDecodeGo body (q + 12) (k + 2) ((escAt body st 0).drop (k + 2))
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp') := by
  have hu : simpleEscape (0x75 : UInt8) = none := by decide
  have hshape : escapeAt body q = some (utf8Encode cp', 12) := by
    simp [escapeAt, h1, hx, ht, hu]
  rw [← hinv.walk, hhead]
  rw [escapeDecodeGo_step_pair hb hlt hctl hshape, List.drop_drop]

/-- **The invariant at its exit, in the walk's vocabulary.**  With no positions
left the walk returns the prefix the store holds and the rest of the body copied
from the cursor.  The copy itself is the body's `us_run` stage, and the store half
of the record's post is that stage's lemma: the invariant's `stored` field is the
part the loop owns. -/
theorem DecodeInv.exit {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome}
    (hinv : DecodeInv body st M dst nps i k out goal) (hk : k = nps) :
    goal = .decoded (out ++ body.drop i) k := by
  have hlen : (escAt body st 0).length = k := by rw [hinv.length, hk]
  have hnil : (escAt body st 0).drop k = [] := List.drop_eq_nil_of_le (by omega)
  rw [← hinv.walk, hnil, escapeDecodeGo_nil]

/-! ### The position stream, read an entry at a time

The record states the list as one byte range and the body reads it four bytes at a
time at `%xp + 4 * %k` (`%arrayidx` in `land.rhs` and `%arrayidx7` in `while.body6`).
Splitting the range at an entry boundary is pure list arithmetic over
`positionsBytes`, and it is what lets those two blocks' traces name the word they
load: the value is the entry's own four bytes, which is the stream's meaning and not
a re-reading of it. -/

/-- A position stream is `w` bytes an entry. -/
theorem positionsBytes_length (w : Nat) (ps : List Nat) :
    (positionsBytes w ps).length = w * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      show (natToBytes p w ++ positionsBytes w ps).length = w * (ps.length + 1)
      rw [List.length_append, natToBytes_length, ih, Nat.mul_succ]
      omega

/-- The stream splits with its list: the entries of the two concatenated lists are
the two streams concatenated. -/
theorem positionsBytes_append_local (w : Nat) (a b : List Nat) :
    positionsBytes w (a ++ b) = positionsBytes w a ++ positionsBytes w b := by
  simp [positionsBytes, List.map_append, List.flatten_append]

/-- **The stream's entry at `k`.**  From the record's one read of the whole stream,
the four bytes the body loads at `%xp + 4 * %k` are entry `k`, provided `k` is an
entry index.  The value is truncated to four bytes, which is what the body's `i32`
load reads; a caller whose entry does not fit four bytes is the canonicality the
staging must carry, and this lemma does not assert it. -/
theorem readBytes_positionsBytes {m : Mem} {xp nps : Nat} {ps : List Nat}
    (h : readBytes m xp (4 * nps) = some (positionsBytes 4 ps)) (hn : nps = ps.length)
    {k : Nat} (hk : k < ps.length) :
    readBytes m (xp + 4 * k) 4 = some (natToBytes (ps[k]'hk) 4) := by
  subst hn
  have hstream : positionsBytes 4 ps =
      positionsBytes 4 (ps.take k) ++ positionsBytes 4 (ps.drop k) := by
    conv => lhs; rw [← List.take_append_drop k ps]
    rw [positionsBytes_append_local]
  have hlen : (positionsBytes 4 (ps.take k)).length = 4 * k := by
    rw [positionsBytes_length, List.length_take]
    omega
  have htail : readBytes m (xp + 4 * k) (4 * ps.length - 4 * k) =
      some (positionsBytes 4 (ps.drop k)) := by
    have hfull : readBytes m xp (4 * k + (4 * ps.length - 4 * k)) =
        some (positionsBytes 4 ps) := by
      rw [show 4 * k + (4 * ps.length - 4 * k) = 4 * ps.length from by omega]
      exact h
    obtain ⟨_, h2⟩ := readBytes_split m xp (4 * k) (4 * ps.length - 4 * k) hfull
    rw [hstream, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append] at h2
    exact h2
  have hdrop : ps.drop k = ps[k]'hk :: ps.drop (k + 1) := List.drop_eq_getElem_cons hk
  have hsplit : positionsBytes 4 (ps.drop k) =
      natToBytes (ps[k]'hk) 4 ++ positionsBytes 4 (ps.drop (k + 1)) := by
    rw [hdrop]
    rfl
  have hfour : readBytes m (xp + 4 * k) (4 + (4 * ps.length - 4 * k - 4)) =
      some (natToBytes (ps[k]'hk) 4 ++ positionsBytes 4 (ps.drop (k + 1))) := by
    rw [show 4 + (4 * ps.length - 4 * k - 4) = 4 * ps.length - 4 * k from by omega]
    rw [htail, hsplit]
  obtain ⟨h1, _⟩ := readBytes_split m (xp + 4 * k) 4 (4 * ps.length - 4 * k - 4) hfour
  have htake : (natToBytes (ps[k]'hk) 4 ++ positionsBytes 4 (ps.drop (k + 1))).take 4
      = natToBytes (ps[k]'hk) 4 := by
    simp [natToBytes_length]
  simpa only [htake] using h1

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.escapeDecodeGo_step_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeDecodeGo_step_simple

/-- info: 'LeanLLVM.Refinement.escapeDecodeGo_step_six' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeDecodeGo_step_six

/-- info: 'LeanLLVM.Refinement.escapeDecodeGo_step_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeDecodeGo_step_pair

/-- info: 'LeanLLVM.Refinement.decodeInv_seed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decodeInv_seed

/-- info: 'LeanLLVM.Refinement.DecodeInv.step_refuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_refuse

/-- info: 'LeanLLVM.Refinement.DecodeInv.step_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_control

/-- info: 'LeanLLVM.Refinement.DecodeInv.step_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_simple

/-- info: 'LeanLLVM.Refinement.DecodeInv.step_six' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_six

/-- info: 'LeanLLVM.Refinement.DecodeInv.step_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_pair

/-- info: 'LeanLLVM.Refinement.positionsBytes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms positionsBytes_length

/-- info: 'LeanLLVM.Refinement.readBytes_positionsBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_positionsBytes

/-- info: 'LeanLLVM.Refinement.DecodeInv.exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.exit

end LeanLLVM.Refinement
