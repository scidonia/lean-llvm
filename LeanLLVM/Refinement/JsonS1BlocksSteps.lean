/-
The fast mask pass's composition, against the specification's masks.

The contracted block unit's loop body computes the entry word from **three** of
the classifier's words rather than four: the unescaped quote, the delimiter
word, the in-string word, and the *neither* word — the lanes that are neither a
structural byte nor a whitespace byte.  The scalar word it does not compute is

  `S = neither & ~quote & ~in_string`,

which is the same complement `specScalar64` is: `neither` is `~(delim | space)`,
so `S` is `~(quote | delim | space | in_string)`.  This module states that
identity (`scalar_eq_neither`) and the composition that consumes it
(`entry_eq_compose`), plus the clamp the peeled final block applies
(`entry_clamp`).  The six per-mask identities, the escape arithmetic and the
in-string word are the mask unit's (`JsonS1MasksSteps`); this module only joins
them at the word level.

The block unit's body also carries the UTF-8 stage's Keiser-Lemire DFA, fused
into the same loop.  `JsonUtf8Fused` states the loop's state and proves the
step is `klStep`'s and the accumulated word is `klAll`; this module reads that
word through the body's bit 1 and states the verdict clause against
`utf8WinPrefix` at the staged window.  The emitted body's own DFA blocks are
pinned by `JsonS1BlocksIR`; their refinement is `JsonUtf8Steps`'s loop
invariant, applied at the host's registers.

The instruction trace over the emitted body — the per-block `denoteCode`
composition, the loop induction, the DFA arm and the escape-list calls — is not
stated here.
-/
import LeanLLVM.Refinement.JsonS1MasksSteps
import LeanLLVM.Refinement.JsonEntSpec
import LeanLLVM.Refinement.JsonEntryIR
import LeanLLVM.Refinement.JsonEscapeSteps
import LeanLLVM.Refinement.JsonUtf8IR
import LeanLLVM.Refinement.CallsFootprint

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window utf8WinPrefix)
open LeanLLVM.Refinement (HasBytes UnchangedOutside wordBytes positionsBytes
  carryPair flagBytes batchReserve)

/-! ### The reduction to two masks -/

/-- The neither word's lanes are the complement of the delimiter and whitespace
masks: a byte's table entry is zero exactly when it carries neither the
structural bits nor the whitespace bits.  This is the boolean fact the fast
pass turns on, and it is what lets the composition drop the whitespace word. -/
theorem scalar_eq_neither (q d s im : BitVec 64) :
    (~~~ (d ||| s)) &&& ~~~ q &&& ~~~ im = ~~~ (q ||| d ||| s ||| im) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and,
    BitLanes.getLsbD_not_of_lt _ hk, BitLanes.getLsbD_not_of_lt _ hk,
    BitLanes.getLsbD_not_of_lt _ hk,
    BitLanes.getLsbD_not_of_lt _ hk,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_or]
  cases hq : q.getLsbD k <;> cases hd : d.getLsbD k <;>
    cases hs : s.getLsbD k <;> cases hi : im.getLsbD k <;> rfl

/-- The scalar word in the fast body's spelling is the specification's: with
`neither = ~(delimiter | whitespace)` substituted, the body's
`neither & ~quote & ~in_string` is `specScalar64`. -/
theorem specScalar64_eq_neither (lo hi : LeanLLVM.JSON.Block32) (st : ClassState) :
    (~~~ (specDelimiter64 lo hi st ||| specSpace64 lo hi st)) &&&
        ~~~ specQuote64 lo hi st &&& ~~~ specInString64 lo hi st
      = specScalar64 lo hi st := by
  rw [scalar_eq_neither, specScalar64]
  congr 1
  ac_rfl

/-- The composition, at the specification's words: the body's
`quote | (delim & ~im) | (S & ~((S << 1) | prevS))` is `entryMask64`.  The
first two terms are `structuralOnly64`, the third is `scalarStarts64` at
`specScalar64`, and `entryMask64` is their join. -/
theorem entry_eq_compose (lo hi : LeanLLVM.JSON.Block32) (st : ClassState) (prevS : Bool) :
    (specQuote64 lo hi st |||
      (specDelimiter64 lo hi st &&& ~~~ specInString64 lo hi st) |||
      (specScalar64 lo hi st &&&
        ~~~ ((specScalar64 lo hi st <<< 1) ||| (if prevS then 1 else 0))))
      = entryMask64 lo hi st prevS := by
  unfold entryMask64 structuralOnly64 scalarStarts64
  rfl

/-- **The peel's clamp.**  The final partial block masks its word with the all-ones
shift the body computes, and that word is `limMask` at the block's remaining
bytes. -/
theorem entry_clamp (w : BitVec 64) (lim : Nat) (h : lim < 2 ^ 64) :
    w &&& clampWord lim = w &&& limMask lim := by
  rw [clampWord_eq_limMask lim h]

theorem entry_clamp_eq (lo hi : LeanLLVM.JSON.Block32) (st : ClassState) (prevS : Bool) (lim : Nat)
    (h : lim < 2 ^ 64) :
    entryMask64 lo hi st prevS &&& clampWord lim =
      entryMask64 lo hi st prevS &&& limMask lim :=
  entry_clamp _ lim h


/-! ### The unit's boundary claim

The post below is the plan's contract at the emitted body's arguments: the entry
words are `stage1Words`, the return word's bit 0 is the ASCII probe and bit 1 the
UTF-8 stage's error word, the escape list is claimed only on the gate's arm, and
everything outside the four objects the unit may write is unchanged.  It is
stated as a definition because the record and its `Satisfies` instance are
stated over it; the theorem relating it to the run is `s1_blocks_refines`. -/

/-- **The contracted block unit's post.**  From the caller's staging the run
returns a two-bit word: bit 0 is the ASCII probe (`1` exactly when every
document byte is below `0x80`) and bit 1 is the UTF-8 stage's error word (`0`
exactly when the staged window is a valid prefix, `utf8WinPrefix` at the three
zero bytes, the document and its zero padding), with no higher bit set.  `ent`
holds the document's entry words; the escape list's clause is present only when
`arm & 2`; and every byte outside `ent`, `xp`, the count slot and the carry is
the caller's. -/
def s1BlocksPost (args : List Value) (mem : Mem) (_next : Nat) (o : Outcome) : Prop :=
  match o with
  | .ub => False
  | .ret (some (.int 64 r)) m =>
      match args with
      | [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm] =>
          ∃ (bs : List UInt8) (xn nxp' : Nat) (ps : List Nat),
            n = BitVec.ofNat 64 bs.length ∧
            readBytes mem b (64 * blocksOf bs.length) = some (padded bs) ∧
            readBytes mem nxp 8 = some (wordBytes 8 xn) ∧
            r &&& 3 = r ∧
            (r &&& 1 = 1 ↔ ∀ x ∈ bs, x.toNat < 0x80) ∧
            (r &&& 2 = 0 ↔
              utf8WinPrefix (utf8Window bs bs.length (blocksOf bs.length))) ∧
            readBytes m ent (8 * blocksOf bs.length) =
              some (wordsOf (stage1Words bs)) ∧
            (arm &&& 2 = (0 : BitVec 64) →
              readBytes m nxp 8 = some (wordBytes 8 xn) ∧
              readBytes m xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)) =
                readBytes mem xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)) ∧
              readBytes m xcarry 16 = some (flagBytes false ++ flagBytes false)) ∧
            (arm &&& 2 ≠ (0 : BitVec 64) →
              readBytes m nxp 8 = some (wordBytes 8 nxp') ∧
              readBytes m xp (4 * nxp') = some (positionsBytes 4 ps) ∧
              (∃ (st : ClassState) (prevb prevs : Bool),
                carryPair m xcarry st prevb prevs)) ∧
            UnchangedOutside mem m
              [(ent, 8 * blocksOf bs.length),
               (xp, 4 * (nxp' + batchReserve)), (nxp, 8), (xcarry, 16)]
      | _ => False
  | _ => False

end LeanLLVM.Refinement.JsonS1BlocksSteps

/-! ### Axiom footprints

The reduction and the composition are boolean and definitional; none of them
reads a choice principle. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.scalar_eq_neither
#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.specScalar64_eq_neither
#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.entry_eq_compose
#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.entry_clamp
