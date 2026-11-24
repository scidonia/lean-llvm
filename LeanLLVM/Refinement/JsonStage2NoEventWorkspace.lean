/-
The no-event entry's caller-domain workspace clause.

`stage2NoEventStagedPre` (`JsonStage2NoEventContract`) is the adapter's staging of
the four objects the flattening appends — the container stack, the refusal record,
the cursor record and the number path's output slot.  It decomposes the twelve-slot
argument list inside an existential to name the caller's region list against
which the four objects must be separate.  `stage2NoEventWorkspace` states the same
staging over an explicit caller region list, so a caller that has already fixed the
decomposition can name the clause without the existential.

**The clause is caller-domain.**  `Γ_stage2_noevent.pre` does not imply it: the
precondition names the twelve ABI arguments and the regions they stage, and the
four objects `stk`, `e`, `c` and `d` appear nowhere in it.  No model of the
pipeline supplies it either: the emitted caller passes those four pointers as
extra arguments the twelve-slot record cannot name, and nothing in this tree
stages them.  `toStagedPre` therefore projects a hypothesis and derives nothing:
it turns a workspace the caller supplies into the adapter's staging, and it is
not a proof that any workspace exists.
-/
import LeanLLVM.Refinement.JsonStage2NoEventContract

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanLLVM.Refinement

open LeanLLVM

/-- **The caller's workspace for the no-event entry**: the four appended objects
are staged, they are separate from every region the caller names, and both the
caller's regions and the four objects end at or below the allocator cursor the
call is made at. -/
def stage2NoEventWorkspace (caller : List (Nat × Nat)) (stk e c d : Nat)
    (mem : Mem) (next : Nat) : Prop :=
  (∀ r ∈ stage2NoEventStagedRegions stk e c d, HasBytes mem r.1 r.2) ∧
  DisjointRegions (caller ++ stage2NoEventStagedRegions stk e c d) ∧
  (∀ r ∈ caller, r.1 + r.2 ≤ next) ∧
  (∀ r ∈ stage2NoEventStagedRegions stk e c d, r.1 + r.2 ≤ next)

/-- **The workspace supplies the adapter's staging.**  At a fixed decomposition of
the twelve-slot argument list and its four count-word bounds, the workspace's four
clauses are the staged-pre's: presence, the same region list's separation, and the
two watermarks.  The hypothesis is the caller's; the projection is not a
derivation that a workspace exists. -/
theorem stage2NoEventWorkspace.toStagedPre (args : List Value) (mem : Mem) (next : Nat)
    (stk e c d : Nat)
    (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat)
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap),
      .ptr tokensOut, .ptr valuesOut, .ptr sumOut, .ptr err])
    (hbound : n < 2 ^ 64 ∧ scratchcap < 2 ^ 64 ∧ nep < 2 ^ 64 ∧ nxp < 2 ^ 64)
    (hws : stage2NoEventWorkspace
      (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err)
      stk e c d mem next) :
    stage2NoEventStagedPre args mem next stk e c d :=
  ⟨hws.1, b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut, sumOut, err,
    hargs, hbound.1, hbound.2.1, hbound.2.2.1, hbound.2.2.2,
    hws.2.1, hws.2.2.1, hws.2.2.2⟩

/-- **The workspace at the precondition's own decomposition**: the twelve-slot
list is the ABI's, the four count words are the pre's values, and the workspace
holds at the caller regions that decomposition names.  This is the shape a rows
premise takes when it carries the workspace instead of the adapter's staging; it
is caller-domain in the same sense, the decomposition being the caller's. -/
def stage2NoEventWorkspaceAt (args : List Value) (stk e c d : Nat) (mem : Mem)
    (next : Nat) : Prop :=
  ∃ (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap),
      .ptr tokensOut, .ptr valuesOut, .ptr sumOut, .ptr err] ∧
    n < 2 ^ 64 ∧ scratchcap < 2 ^ 64 ∧ nep < 2 ^ 64 ∧ nxp < 2 ^ 64 ∧
    stage2NoEventWorkspace
      (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err)
      stk e c d mem next

/-- The workspace at its decomposition supplies the adapter's staging. -/
theorem stage2NoEventWorkspaceAt.toStagedPre {args : List Value} {mem : Mem} {next : Nat}
    {stk e c d : Nat} (h : stage2NoEventWorkspaceAt args stk e c d mem next) :
    stage2NoEventStagedPre args mem next stk e c d := by
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut, sumOut, err,
    hargs, hn, hsc, hne, hnx, hws⟩ := h
  exact stage2NoEventWorkspace.toStagedPre args mem next stk e c d
    b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err
    hargs ⟨hn, hsc, hne, hnx⟩ hws

/-- The adapter's staging is the workspace at its own decomposition. -/
theorem stage2NoEventStagedPre.workspaceAt {args : List Value} {mem : Mem} {next : Nat}
    {stk e c d : Nat} (h : stage2NoEventStagedPre args mem next stk e c d) :
    stage2NoEventWorkspaceAt args stk e c d mem next := by
  obtain ⟨hpres, b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut, sumOut,
    err, hargs, hn, hsc, hne, hnx, hdisj, hwat, hwats⟩ := h
  exact ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut, sumOut, err,
    hargs, hn, hsc, hne, hnx, ⟨hpres, hdisj, hwat, hwats⟩⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWorkspace.toStagedPre
#print axioms stage2NoEventWorkspaceAt.toStagedPre
#print axioms stage2NoEventStagedPre.workspaceAt

end LeanLLVM.Refinement
