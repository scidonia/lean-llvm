/-
The run, the window-driven scan and the tail: the block model's string scan, and the
statement that its window step is the byte rule's run.

`bodyRun` is the **reference** — the byte rule stepped one byte at a time from an index
with the single `BodyState` threaded — and the scan does not call it: `scanStringAt`
reads a window, takes its decision from the window's first stop and its next cursor
from the block operation, and `scanWindow_stop` is the statement that the two are one
step.  `tailRun` is the same run with exactly the input's remainder as fuel, so an
`open` run there stopped because the input ended and is reported as `.ended`.

`RunEnd.open` carries the position at which the run stopped **with no byte to read**, so
the two reasons a run can end without deciding anything — the fuel was exhausted, or the
input ended — are not one event: the caller tells them apart by comparing that position
with the fuel's end.
-/
import LeanLLVM.JSON.ScanWindow

namespace LeanLLVM.JSON

open ByteString

/-! ### The reference run -/

/-- The body run's outcome.  `open` records **where the run stopped with no byte to
read** — the fuel was exhausted, or the input ended — so the two events are not
confused; the caller knows which by comparing that index with the fuel's end.  The
refusal carries its reason and the position that raised it.  The field is named `pos`,
not `at`: `at` is a Lean token and does not elaborate as a binder or a field name. -/
inductive RunEnd where
  | closed (stop : Nat)
  | open (st : BodyState) (pos : Nat)
  | refused (stop : BodyStop) (pos : Nat)
deriving DecidableEq, Repr

/-- The body's run over `fuel` bytes from `i`: the **reference**, threaded by the
single state.  The scan itself does not call this; the window fold does the same work
and `scanWindow_stop` is the statement that the two agree. -/
def bodyRun (bs : Bytes) (fuel i : Nat) (st : BodyState) : RunEnd :=
  match fuel with
  | 0 => .open st i
  | fuel + 1 =>
      match bs[i]? with
      | none => .open st i
      | some b =>
          match bodyStep st b with
          | .cont st' => bodyRun bs fuel (i + 1) st'
          | .closed => .closed (i + 1)
          | .refused s => .refused s i

/-- The run at zero fuel reads no byte and stands where it was given. -/
private theorem bodyRun_zero (bs : Bytes) (i : Nat) (st : BodyState) :
    bodyRun bs 0 i st = .open st i := rfl

/-- The run at positive fuel reads the byte at its position, or stops there when the
input has none. -/
private theorem bodyRun_succ (bs : Bytes) (fuel i : Nat) (st : BodyState) :
    bodyRun bs (fuel + 1) i st =
      (match bs[i]? with
       | none => .open st i
       | some b =>
           match bodyStep st b with
           | .cont st' => bodyRun bs fuel (i + 1) st'
           | .closed => .closed (i + 1)
           | .refused s => .refused s i) := rfl

/-- With no byte at its position, the run stops there with the state it held. -/
private theorem bodyRun_succ_none {bs : Bytes} {fuel i : Nat} {st : BodyState}
    (h : bs[i]? = none) : bodyRun bs (fuel + 1) i st = .open st i := by
  simp only [bodyRun_succ, h]

/-- A continuing byte is one step of the run. -/
private theorem bodyRun_step_cont {bs : Bytes} {fuel i : Nat} {st st' : BodyState}
    {b : UInt8} (hb : bs[i]? = some b) (hs : bodyStep st b = .cont st') :
    bodyRun bs (fuel + 1) i st = bodyRun bs fuel (i + 1) st' := by
  simp only [bodyRun_succ, hb, hs]

/-- A closing byte is the run's last step, and it stops after that byte. -/
private theorem bodyRun_step_closed {bs : Bytes} {fuel i : Nat} {st : BodyState}
    {b : UInt8} (hb : bs[i]? = some b) (hs : bodyStep st b = .closed) :
    bodyRun bs (fuel + 1) i st = .closed (i + 1) := by
  simp only [bodyRun_succ, hb, hs]

/-- A refused byte is the run's last step, and the refusal carries that position. -/
private theorem bodyRun_step_refused {bs : Bytes} {fuel i : Nat} {st : BodyState}
    {b : UInt8} {s : BodyStop} (hb : bs[i]? = some b) (hs : bodyStep st b = .refused s) :
    bodyRun bs (fuel + 1) i st = .refused s i := by
  simp only [bodyRun_succ, hb, hs]

/-! ### The window step

`bodyRun` and the window fold do the same work: the fold reads the window's lanes once
and records the first lane the byte rule does not continue past, and the run steps the
same bytes one at a time.  `scanWindow_stop` is the statement that the two agree, and it
is an induction over the lanes rather than a comparison of two computations: the run
reaches lane `n` with the fold's carry at that lane, so a stop at lane `k` is the run's
step `k` and the position it reports is `k` lanes past the window's start.

The carry's two decompositions below are what the induction transfers: one lane, then
the rest — the sum `carryAt_append` is for, at the single lane a window step consumes.
-/

/-- The carry after one more lane: it advances on a continuing step and stands still on
any other. -/
private theorem carryAt_succ (bs : List UInt8) (st : BodyState) (k : Nat) :
    carryAt bs st (k + 1) =
      (match bs[k]? with
       | some b =>
           (match bodyStep (carryAt bs st k) b with
            | .cont st' => st'
            | _ => carryAt bs st k)
       | none => carryAt bs st k) := by
  unfold carryAt
  rw [List.take_add_one, List.foldl_append]
  cases h : bs[k]? with
  | none => simp
  | some b => rfl

/-- A continuing lane at the head leaves the state its step produced. -/
private theorem carryAt_one {b : UInt8} {t : List UInt8} {st st' : BodyState}
    (h : bodyStep st b = .cont st') : carryAt (b :: t) st 1 = st' := by
  have hs := carryAt_succ (b :: t) st 0
  rw [show (0 : Nat) + 1 = 1 from rfl, show (b :: t)[0]? = some b from by simp] at hs
  rw [hs]
  show (match bodyStep (carryAt (b :: t) st 0) b with
        | .cont s => s
        | _ => carryAt (b :: t) st 0) = st'
  rw [show carryAt (b :: t) st 0 = st from rfl, h]

/-- The carry splits at the head's lane: the state after the first lane, then the rest
of the list. -/
private theorem carryAt_cons (b : UInt8) (t : List UInt8) (st : BodyState) (k : Nat) :
    carryAt (b :: t) st (k + 1) = carryAt t (carryAt (b :: t) st 1) k := by
  have h := carryAt_append [b] t st k
  rw [show [b].length = 1 from rfl, show 1 + k = k + 1 from by omega,
    show ([b] ++ t) = (b :: t) from rfl,
    show carryAt [b] st 1 = carryAt (b :: t) st 1 from rfl] at h
  exact h

/-- **The run reads its first `k` lanes as the fold does.**  While the lanes before `k`
continue, the run's remaining fuel is the fuel less those lanes, its position is `k`
lanes past the start, and its state is the fold's carry at lane `k`. -/
private theorem bodyRun_split {bs : Bytes} :
    ∀ (l : List UInt8) (k n i : Nat) (st : BodyState),
      (∀ j, j < n → bs[i + j]? = l[j]?) →
      n ≤ l.length →
      k ≤ n →
      (∀ j, j < k → ∀ {b : UInt8}, l[j]? = some b →
        ∃ st', bodyStep (carryAt l st j) b = .cont st') →
      bodyRun bs n i st = bodyRun bs (n - k) (i + k) (carryAt l st k) := by
  intro l
  induction l with
  | nil =>
      intro k n i st _ hlen hkn _
      have hn : n = 0 := by simpa using hlen
      have hk : k = 0 := by omega
      rw [hn, hk]
      rfl
  | cons b t ih =>
      intro k n i st hlane hlen hkn hcont
      cases k with
      | zero => rfl
      | succ k =>
          have hnpos : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos k) hkn
          obtain ⟨st', hst'⟩ := hcont 0 (Nat.succ_pos k) (show (b :: t)[0]? = some b from rfl)
          have hst'' : bodyStep st b = .cont st' := hst'
          have hb : bs[i]? = some b := by
            have h0 : bs[i + 0]? = (b :: t)[0]? := hlane 0 hnpos
            rw [show (b :: t)[0]? = some b from rfl, show i + 0 = i from rfl] at h0
            exact h0
          have hn1 : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos)
          rw [show bodyRun bs n i st = bodyRun bs (n - 1 + 1) i st from by rw [hn1],
            bodyRun_step_cont hb hst'']
          have hlanet : ∀ j, j < n - 1 → bs[(i + 1) + j]? = t[j]? := by
            intro j hj
            have hj' : bs[i + (j + 1)]? = (b :: t)[j + 1]? := hlane (j + 1) (by omega)
            rw [show (b :: t)[j + 1]? = t[j]? from by simp,
              show i + (j + 1) = (i + 1) + j from by omega] at hj'
            exact hj'
          have hlent : n - 1 ≤ t.length := by
            have : (b :: t).length = t.length + 1 := List.length_cons
            omega
          have hkt : k ≤ n - 1 := by omega
          have hcontt : ∀ j, j < k → ∀ {c : UInt8}, t[j]? = some c →
              ∃ st'', bodyStep (carryAt t st' j) c = .cont st'' := by
            intro j hj c hc
            have hc' : (b :: t)[j + 1]? = some c := by
              rw [show (b :: t)[j + 1]? = t[j]? from by simp]
              exact hc
            obtain ⟨st'', hst''2⟩ := hcont (j + 1) (by omega) hc'
            have hcarryt : carryAt (b :: t) st (j + 1) = carryAt t st' j := by
              rw [carryAt_cons b t st j, carryAt_one hst'']
            exact ⟨st'', by rw [← hcarryt]; exact hst''2⟩
          rw [ih k (n - 1) (i + 1) st' hlanet hlent hkt hcontt]
          have hcarryt : carryAt t st' k = carryAt (b :: t) st (k + 1) := by
            rw [carryAt_cons b t st k, carryAt_one hst'']
          rw [hcarryt, show (n - 1) - k = n - (k + 1) from by omega,
            show (i + 1) + k = i + (k + 1) from by omega]

/-- **The run reaches every lane the fold continues past** with the fold's carry there:
the `k`-lane form of `bodyRun_split` with no fuel left. -/
private theorem bodyRun_prefix {bs : Bytes} (l : List UInt8) (n i : Nat) (st : BodyState)
    (hlane : ∀ j, j < n → bs[i + j]? = l[j]?) (hlen : n ≤ l.length)
    (hcont : ∀ j, j < n → ∀ {b : UInt8}, l[j]? = some b →
      ∃ st', bodyStep (carryAt l st j) b = .cont st') :
    bodyRun bs n i st = .open (carryAt l st n) (i + n) := by
  rw [bodyRun_split l n n i st hlane hlen (Nat.le_refl n) hcont, Nat.sub_self]
  rfl

set_option maxRecDepth 10000 in
/-- **The window step.**  The window's first stop is the run's: a closing stop at
lane `k` closes at `i + k + 1`, a refusing stop at lane `k` refuses `s` at `i + k`,
and a window with no stop leaves the fold's carry.  Total in all three cases: the
refusal branch is part of the statement rather than an omission. -/
theorem scanWindow_stop (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) (st : BodyState) :
    bodyRun bs 32 i st =
      match (windowAt bs i h st).stop with
      | some (.close k) => .closed (i + k + 1)
      | some (.refuse k s) => .refused s (i + k)
      | none => .open (windowAt bs i h st).carry (i + 32) := by
  let l := List.ofFn (blockAt bs i h)
  have hl : l = List.ofFn (blockAt bs i h) := rfl
  have hlen : l.length = 32 := List.length_ofFn
  have hlane : ∀ j, j < 32 → bs[i + j]? = l[j]? := by
    intro j hj
    rw [hl]
    have hjlen : j < (List.ofFn (blockAt bs i h)).length := by
      rw [List.length_ofFn]
      exact hj
    have hs : i + j < bs.size := by omega
    have h1 : (List.ofFn (blockAt bs i h))[j]? = some (blockAt bs i h ⟨j, hj⟩) := by
      rw [List.getElem?_eq_getElem hjlen, List.getElem_ofFn]
    have h2 : bs[i + j]? = some (blockAt bs i h ⟨j, hj⟩) := by
      rw [ByteString.getElem?_eq_getElem (by rwa [ByteString.length_eq_size]), blockAt_apply]
      rfl
    rw [h1, h2]
  have hspec : (match (windowOf l st).stop with
      | none => ContinuesBefore l st 32
      | some (.close k) =>
          k < 32 ∧ (∃ b : UInt8, l[k]? = some b) ∧ ContinuesBefore l st k ∧
            ∀ {b : UInt8}, l[k]? = some b → bodyStep (carryAt l st k) b = .closed
      | some (.refuse k s) =>
          k < 32 ∧ (∃ b : UInt8, l[k]? = some b) ∧ ContinuesBefore l st k ∧
            ∀ {b : UInt8}, l[k]? = some b → bodyStep (carryAt l st k) b = .refused s) :=
    windowOf_stop_spec (bs := l) (st := st)
  have hstopw : (windowOf l st).stop = (windowAt bs i h st).stop := rfl
  cases hstop : (windowAt bs i h st).stop with
  | none =>
      rw [show (windowOf l st).stop = none from hstopw.trans hstop] at hspec
      have hcont : ContinuesBefore l st 32 := hspec
      rw [bodyRun_prefix l 32 i st hlane (by omega) hcont]
      rw [show carryAt l st 32 = (windowAt bs i h st).carry from (windowOf_carry l st).symm]
  | some s =>
      cases s with
      | close k =>
          rw [show (windowOf l st).stop = some (.close k) from hstopw.trans hstop] at hspec
          obtain ⟨hk32, ⟨b, hbk⟩, hcont, hlaneK⟩ := hspec
          have hb : bs[i + k]? = some b := by
            rw [hlane k hk32]
            exact hbk
          have hstep : bodyStep (carryAt l st k) b = .closed := hlaneK hbk
          rw [bodyRun_split l k 32 i st hlane (by omega) (by omega) hcont]
          rw [show 32 - k = 32 - k - 1 + 1 from by omega,
            bodyRun_step_closed hb hstep]
      | refuse k s =>
          rw [show (windowOf l st).stop = some (.refuse k s) from hstopw.trans hstop] at hspec
          obtain ⟨hk32, ⟨b, hbk⟩, hcont, hlaneK⟩ := hspec
          have hb : bs[i + k]? = some b := by
            rw [hlane k hk32]
            exact hbk
          have hstep : bodyStep (carryAt l st k) b = .refused s := hlaneK hbk
          rw [bodyRun_split l k 32 i st hlane (by omega) (by omega) hcont]
          rw [show 32 - k = 32 - k - 1 + 1 from by omega,
            bodyRun_step_refused hb hstep]

/-! ### The scan and the tail -/

/-- The tail rule: the bytes after the last full window are stepped one at a time,
because `scanBlock` reports `short` for them (`scanBlock_correct`'s second conjunct).
Its fuel is exactly the input's remainder, so `open` there means the input ran out. -/
def tailRun (bs : Bytes) (i : Nat) (st : BodyState) : Except Refusal Nat :=
  match bodyRun bs (bs.size - i) i st with
  | .closed k => .ok k
  | .open _ _ => .error (.ended, i)
  | .refused s pos => .error (s, pos)

/-- The scan: while thirty-two bytes are readable, **the window** — its `stop` and its
`carry` — and otherwise the tail rule.  The next window starts at the block
operation's cursor, so the fold, `scanBlock` and the byte rule are one advance. -/
def scanStringAt (bs : Bytes) (fuel i : Nat) (st : BodyState) : Except Refusal Nat :=
  match fuel with
  | 0 => tailRun bs i st
  | fuel + 1 =>
      if h : i + 32 ≤ bs.size then
        match (windowAt bs i h st).stop with
        | some (.close k) => .ok (i + k + 1)
        | some (.refuse k s) => .error (s, i + k)
        | none =>
            scanStringAt bs fuel (scanBlock ⟨i⟩ (blockAt bs i h) 32).1.pos
              (windowAt bs i h st).carry
      else tailRun bs i st

set_option maxRecDepth 10000 in
/-- **The scan's window branch, as an equation.**  At positive fuel and a readable
window the scan matches the window's `stop`; the `none` branch recurs at the block
operation's cursor with the fold's carry.  Pinned beside its siblings because it is the
one statement a wrong wiring fails: a `scanStringAt` that matched `bodyRun`, or that
computed its own `i + 32`, would satisfy every other pin, `example` and `#guard` while
no longer consuming the window. -/
theorem scanStringAt_succ (bs : Bytes) (fuel i : Nat) (st : BodyState) :
    scanStringAt bs (fuel + 1) i st =
      (if h : i + 32 ≤ bs.size then
        match (windowAt bs i h st).stop with
        | some (.close k) => .ok (i + k + 1)
        | some (.refuse k s) => .error (s, i + k)
        | none =>
            scanStringAt bs fuel (scanBlock ⟨i⟩ (blockAt bs i h) 32).1.pos
              (windowAt bs i h st).carry
      else tailRun bs i st) := by
  rfl

/-- The block model's string scan from the opening quote at `q`: the body's first byte
is at `q + 1` **and the state starts inside the body**, because the opening quote has
already been consumed.  Unaligned entry needs no rule of its own: `scanStringAt` reads
a window wherever the cursor is. -/
def scanStringBlocks (bs : Bytes) (q : Nat) : Except Refusal Nat :=
  scanStringAt bs (bs.size + 1) (q + 1) BodyState.body

/-- The scan advances by the block operation's cursor, so the boundary is `scanBlock`'s
and the model computes no advance of its own. -/
theorem scanStringAt_pos (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) :
    (scanBlock ⟨i⟩ (blockAt bs i h) 32).1.pos = i + 32 := by
  have hr := ((scanBlock_correct ⟨i⟩ (blockAt bs i h) 32 (Nat.le_refl 32)).1 rfl).1
  exact congrArg (fun r => r.1.pos) hr

/-! ### The run's bounds

The three bounds the tail rule and the scan's step depend on: a closing run stops
inside its own fuel and inside the input, an `open` run stops between where it started
and whichever of the fuel's end and the input's end comes first, and an `open` run that
stopped short of its fuel stopped because the input ended.
-/

/-- A run that closes stops inside its own fuel and inside the input. -/
theorem bodyRun_bound {bs : Bytes} {fuel i : Nat} {st : BodyState} {k : Nat}
    (h : bodyRun bs fuel i st = .closed k) : i < k ∧ k ≤ i + fuel ∧ k ≤ bs.size := by
  induction fuel generalizing i st with
  | zero =>
      rw [bodyRun_zero] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      cases hb : bs[i]? with
      | none =>
          rw [bodyRun_succ_none hb] at h
          exact absurd h (by simp)
      | some b =>
          have hisize : i < bs.size := (ByteString.getElem?_eq_some_iff.mp hb).1
          cases hs : bodyStep st b with
          | cont st' =>
              rw [bodyRun_step_cont hb hs] at h
              obtain ⟨h1, h2, h3⟩ := ih h
              exact ⟨by omega, by omega, h3⟩
          | closed =>
              rw [bodyRun_step_closed hb hs] at h
              simp only [RunEnd.closed.injEq] at h
              exact ⟨by omega, by omega, by omega⟩
          | refused s =>
              rw [bodyRun_step_refused hb hs] at h
              exact absurd h (by simp)

/-- An `open` run, started inside the input, stops at or after its start and at most
where its fuel or the input ends.  The start bound is load-bearing: with an empty `bs`
and `i = 5`, `fuel = 3`, the run is `open` at `5`, so without `i ≤ bs.size` the
conclusion `pos ≤ min (i + fuel) bs.size` is false. -/
theorem bodyRun_open_bound {bs : Bytes} {fuel i pos : Nat} {st st' : BodyState}
    (hstart : i ≤ bs.size) (h : bodyRun bs fuel i st = .open st' pos) :
    i ≤ pos ∧ pos ≤ min (i + fuel) bs.size := by
  induction fuel generalizing i st with
  | zero =>
      rw [bodyRun_zero] at h
      simp only [RunEnd.open.injEq] at h
      obtain ⟨hty, hpos⟩ := h
      subst hty
      subst hpos
      exact ⟨Nat.le_refl i, Nat.le_min.mpr ⟨by omega, hstart⟩⟩
  | succ fuel ih =>
      cases hb : bs[i]? with
      | none =>
          rw [bodyRun_succ_none hb] at h
          simp only [RunEnd.open.injEq] at h
          obtain ⟨hty, hpos⟩ := h
          subst hty
          subst hpos
          exact ⟨Nat.le_refl i, Nat.le_min.mpr ⟨by omega, hstart⟩⟩
      | some b =>
          have hisize : i < bs.size := (ByteString.getElem?_eq_some_iff.mp hb).1
          cases hs : bodyStep st b with
          | cont st'' =>
              rw [bodyRun_step_cont hb hs] at h
              obtain ⟨h1, h2⟩ := ih (i := i + 1) (st := st'') (by omega) h
              have h3 := Nat.le_trans h2 (Nat.min_le_left _ _)
              have h4 := Nat.le_trans h2 (Nat.min_le_right _ _)
              exact ⟨by omega, Nat.le_min.mpr ⟨by omega, h4⟩⟩
          | closed =>
              rw [bodyRun_step_closed hb hs] at h
              exact absurd h (by simp)
          | refused s =>
              rw [bodyRun_step_refused hb hs] at h
              exact absurd h (by simp)

/-- An `open` run that stopped early stopped because the input ended — again with the
start inside the input, which is what makes `pos ≤ bs.size` available. -/
theorem bodyRun_open_at_end {bs : Bytes} {fuel i pos : Nat} {st st' : BodyState}
    (hstart : i ≤ bs.size) (h : bodyRun bs fuel i st = .open st' pos)
    (hlt : pos < i + fuel) : pos = bs.size := by
  induction fuel generalizing i st with
  | zero =>
      rw [bodyRun_zero] at h
      simp only [RunEnd.open.injEq] at h
      obtain ⟨hty, hpos⟩ := h
      subst hty
      subst hpos
      omega
  | succ fuel ih =>
      cases hb : bs[i]? with
      | none =>
          rw [bodyRun_succ_none hb] at h
          simp only [RunEnd.open.injEq] at h
          obtain ⟨hty, hpos⟩ := h
          subst hty
          subst hpos
          have hge := ge_of_getElem?_eq_none hb
          omega
      | some b =>
          have hisize : i < bs.size := (ByteString.getElem?_eq_some_iff.mp hb).1
          cases hs : bodyStep st b with
          | cont st'' =>
              rw [bodyRun_step_cont hb hs] at h
              exact ih (i := i + 1) (st := st'') (by omega) h (by omega)
          | closed =>
              rw [bodyRun_step_closed hb hs] at h
              exact absurd h (by simp)
          | refused s =>
              rw [bodyRun_step_refused hb hs] at h
              exact absurd h (by simp)

/-- Inside a readable window the run consumes all thirty-two bytes, so `open` there
means exactly `i + 32`: the guard `i + 32 ≤ bs.size` is what makes the window step a
step rather than a stop. -/
theorem bodyRun_open_window {bs : Bytes} {i pos : Nat} {st st' : BodyState}
    (hw : i + 32 ≤ bs.size) (h : bodyRun bs 32 i st = .open st' pos) : pos = i + 32 := by
  obtain ⟨-, h2⟩ := bodyRun_open_bound (fuel := 32) (i := i) (st := st) (by omega) h
  have h3 : pos ≤ i + 32 := Nat.le_trans h2 (Nat.min_le_left _ _)
  have h4 : pos ≤ bs.size := Nat.le_trans h2 (Nat.min_le_right _ _)
  rcases Nat.lt_or_eq_of_le h3 with hlt | heq
  · have hend := bodyRun_open_at_end (fuel := 32) (i := i) (st := st) (by omega) h hlt
    omega
  · exact heq

/-- The tail's `open` is the input's end: with a start inside the input, the run stops
at `bs.size` whichever way it stopped, which is what justifies `tailRun`'s `.ended`. -/
theorem tailRun_open_at {bs : Bytes} {i pos : Nat} {st st' : BodyState} (hstart : i ≤ bs.size)
    (h : bodyRun bs (bs.size - i) i st = .open st' pos) : pos = bs.size := by
  obtain ⟨-, h2⟩ := bodyRun_open_bound (fuel := bs.size - i) (i := i) (st := st) hstart h
  have hle : pos ≤ i + (bs.size - i) := Nat.le_trans h2 (Nat.min_le_left _ _)
  have hsum : i + (bs.size - i) = bs.size := Nat.add_sub_cancel' hstart
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have := bodyRun_open_at_end (fuel := bs.size - i) (i := i) (st := st) hstart h hlt
    omega
  · omega

end LeanLLVM.JSON
