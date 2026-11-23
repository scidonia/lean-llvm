/-
The per-document entry selector, as a bounded prefix scan.

`leanllvm_json_pipeline_fast_best` reads at most the document's first 128 bytes
— the first 64-byte block whenever the document is non-empty, and the second
only when it is longer than 64 — and returns one of three classes: a high byte
in the prefix, a backslash in the prefix, or neither.  Each class names an
entry, and the entry is called with the caller's arguments unchanged, so the
selected entry's own post is the choice's post.

The model here states three things the selector owes:

* **It is a pure function of a bounded prefix.**  `pfClass` reads `b.take 128`
  (or `b.take 64`) and has no memory in its type; `pfSelect` is the same scan
  with the read made explicit, and `pfSelect_leaves_mem` proves its output
  memory is its input memory.
* **The read is inside the staging window.**  `selector_extent_le_routeBlocks`
  bounds the read by `routeBlocks doc`: a non-empty document has at least one
  block, and one longer than 64 bytes has at least two, so the four 32-byte
  loads never leave the document's padded window.
* **Every branch's entry is one whose post the branch satisfies.**
  `pfEntry_branch_post` maps a post for each candidate entry to a post for the
  selection, and `pfEntry_dense_table` names the dense branch's one real
  precondition: its entry is POS8, which reads the entry unit's static table
  (`entry.h`).  The adapter's `route_init` fills that table before the first
  call, which is why the staged memory's table region is the model's witness.

The class boundaries are a performance separation, not a specification: the
99-document corpus's first backslash at offset 74-115 and first high byte at
offset 7-28 are why 128 bytes was chosen, and a document mixing the classes
falls to the class of its prefix.  Nothing here depends on those numbers; the
output is the chosen entry's whatever the class is, which is why the scan needs
no promise about where a document's first special byte lies.
-/
import LeanLLVM.JsonCallRoute

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR

set_option maxHeartbeats 1000000

/-! ### The classes and the entries -/

/-- The three classes the prefix scan separates: no special byte, a backslash,
a high byte.  A high byte wins over a backslash because the C test is taken
first. -/
inductive PfClass where
  | dense
  | strings
  | utf8
deriving DecidableEq, Repr

/-- The entries the classes name. -/
inductive PfEntry where
  | plainPos8
  | fast
  | fastList
deriving DecidableEq, Repr

/-- Whether a byte run carries a byte at or above `0x80`. -/
def hasHigh (bs : List UInt8) : Bool := bs.any (fun b => 0x80 ≤ b.toNat)

/-- Whether a byte run carries a backslash. -/
def hasBackslash (bs : List UInt8) : Bool := bs.any (fun b => b = (0x5C : UInt8))

/-- **The selector's class.**  A zero-length document is dense without a load;
a document longer than one block is classified by its first 128 bytes and a
shorter one by its first 64.  The high-byte test precedes the backslash test,
matching the C body's `testz`-then-`bm` order. -/
def pfClass (b : List UInt8) (n : Nat) : PfClass :=
  if n = 0 then .dense
  else if n > 64 then
    let p := b.take 128
    if hasHigh p then .utf8
    else if hasBackslash p then .strings
    else .dense
  else
    let p := b.take 64
    if hasHigh p then .utf8
    else if hasBackslash p then .strings
    else .dense

/-- **The selected entry.**  Dense documents take the plain POS8 pipeline; a
UTF-8 prefix takes the fused list-free entry; a strings prefix takes the fused
entry at or below 64 KiB and the list entry above it. -/
def pfEntry (n : Nat) : PfClass → PfEntry
  | .dense => .plainPos8
  | .utf8 => .fast
  | .strings => if n > 65536 then .fastList else .fast

/-! ### The scan as a read and no write -/

/-- One selector step: read the prefix the C body reads, classify it, and leave
the memory as it was.  The `n = 0` branch reads no byte, as the C body does. -/
def pfSelect (mem : Mem) (base n : Nat) : Option (PfClass × Mem) :=
  if n = 0 then some (.dense, mem)
  else if n > 64 then
    match readBytes mem base 128 with
    | some bs => some (pfClass bs n, mem)
    | none => none
  else
    match readBytes mem base 64 with
    | some bs => some (pfClass bs n, mem)
    | none => none

/-- **The selector writes nothing.**  Whatever it returns, the memory it leaves
is the memory it read. -/
theorem pfSelect_leaves_mem {mem : Mem} {base n : Nat} {c : PfClass} {mem' : Mem}
    (h : pfSelect mem base n = some (c, mem')) : mem' = mem := by
  unfold pfSelect at h
  by_cases h0 : n = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · rw [if_neg h0] at h
    by_cases h64 : n > 64
    · rw [if_pos h64] at h
      cases hb : readBytes mem base 128 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
    · rw [if_neg h64] at h
      cases hb : readBytes mem base 64 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm

/-! ### The read is inside the staging window -/

/-- A non-empty document has at least one 64-byte block, and one longer than a
block has at least two: the selector's read never leaves the padded window. -/
theorem selector_extent_le_routeBlocks (doc : List UInt8) (hn : 0 < doc.length) :
    (if doc.length > 64 then 128 else 64) ≤ routeBlocks doc := by
  by_cases h64 : doc.length > 64
  · rw [if_pos h64]
    have hk : 2 ≤ pipelineBlocks doc.length := by
      unfold pipelineBlocks
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 64)).mpr (by omega)
    simp only [routeBlocks]
    omega
  · rw [if_neg h64]
    have hk : 1 ≤ pipelineBlocks doc.length := by
      unfold pipelineBlocks
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 64)).mpr (by omega)
    simp only [routeBlocks]
    omega

/-- **The selector reads the staged window and nothing else.**  The read it
performs succeeds, and its bytes are the document's padded prefix at the
window's base. -/
theorem stagedSelector_read {l : RouteLayout} {doc : List UInt8}
    (hsep : DisjointRegions (stagedExtents l doc)) (hb3 : 3 ≤ l.base)
    (hn : 0 < doc.length) :
    pfSelect (stagedMem l doc) l.base doc.length =
      some (pfClass
        (((windowBytes doc).drop 3).take (if doc.length > 64 then 128 else 64))
        doc.length, stagedMem l doc) := by
  unfold pfSelect
  rw [if_neg (by omega : ¬ doc.length = 0)]
  by_cases h64 : doc.length > 64
  · rw [if_pos h64]
    have hlen : 128 ≤ routeBlocks doc := by
      have h := selector_extent_le_routeBlocks doc hn
      rwa [if_pos h64] at h
    have hread : readBytes (stagedMem l doc) l.base 128 =
        some (((windowBytes doc).drop 3).take 128) := by
      have h := readBytes_store_at (m := []) (mem_window l doc) hsep 3 128 (by
        rw [windowBytes_length]; omega)
      rwa [show l.base - 3 + 3 = l.base from by omega] at h
    rw [hread, if_pos h64]
  · rw [if_neg h64]
    have hlen : 64 ≤ routeBlocks doc := by
      have h := selector_extent_le_routeBlocks doc hn
      rwa [if_neg h64] at h
    have hread : readBytes (stagedMem l doc) l.base 64 =
        some (((windowBytes doc).drop 3).take 64) := by
      have h := readBytes_store_at (m := []) (mem_window l doc) hsep 3 64 (by
        rw [windowBytes_length]; omega)
      rwa [show l.base - 3 + 3 = l.base from by omega] at h
    rw [hread, if_neg h64]

/-! ### The branches and their posts -/

/-- **Every branch satisfies the chosen entry's post.**  Given a post for each
candidate entry — the three entries' own refinement statements, whatever they
are — the selection satisfies the chosen one's.  The selector adds no clause of
its own: it reads a prefix, writes nothing, and calls the entry unchanged. -/
theorem pfEntry_branch_post {P : PfEntry → Prop}
    (hPos8 : P .plainPos8) (hFast : P .fast) (hList : P .fastList)
    (n : Nat) (c : PfClass) : P (pfEntry n c) := by
  cases c with
  | dense => exact hPos8
  | utf8 => exact hFast
  | strings =>
      dsimp only [pfEntry]
      split <;> assumption

/-- The staged POS8 table, read at the routing's model address. -/
theorem stagedPos8Table_read (l : RouteLayout) (doc : List UInt8)
    (hsep : DisjointRegions (stagedExtents l doc)) :
    readBytes (stagedMem l doc) l.tab 8192 = some pos8Table := by
  simpa only [stagedMem, pos8Table_extent] using
    (store_read_full (m := []) (mem_table l doc) hsep)

/-- **The dense branch's one precondition.**  The dense class selects POS8,
whose call reads the entry unit's static table; the staged memory holds that
table, which is the model of the adapter's `route_init` filling the unit's
table before the first call (`entry.h`).  The b8 and fused entries read no
table, so this is the only branch that carries the obligation. -/
theorem pfEntry_dense_table (l : RouteLayout) (doc : List UInt8)
    (hsep : DisjointRegions (stagedExtents l doc)) :
    pfEntry doc.length .dense = .plainPos8 ∧
      readBytes (stagedMem l doc) l.tab 8192 = some pos8Table :=
  ⟨rfl, stagedPos8Table_read l doc hsep⟩

/-! ### The model's boundaries -/

/-- A backslash past the scanned prefix does not move the class: the scan is a
prefix read, and the class is the chosen entry's, not a property of the whole
document. -/
example : pfClass (List.replicate 200 (0x20 : UInt8) ++ [(0x5C : UInt8)]) 201
    = .dense := by decide

/-- A backslash inside the prefix selects the strings class. -/
example : pfClass
  (List.replicate 100 (0x20 : UInt8) ++ (0x5C : UInt8) ::
    List.replicate 100 (0x20 : UInt8)) 201 = .strings := by decide

/-- A high byte inside the prefix selects the UTF-8 class, ahead of a backslash
also inside it. -/
example : pfClass
  (List.replicate 7 (0x20 : UInt8) ++ (0x80 : UInt8) ::
    (0x5C : UInt8) :: List.replicate 100 (0x20 : UInt8)) 109 = .utf8 := by decide

/-- The empty document is dense without a read. -/
example : pfClass [] 0 = .dense := by decide

end LeanLLVM.Refinement
