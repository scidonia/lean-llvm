/-
The JSON pipeline's call route: the wrapper's contract, the domain the record
excludes, and the native entry point.

`JsonPipelineContract` states `Γ_pipeline_units` — the record
`pipeline_satisfies_at_stage2_of_exitStage2` proves the pinned body satisfies —
and `JsonPipelineSpec.pipelineSpecPre` states the record's domain: the staging
above, the parser's input bound, and the two limit exclusions.  Both are
statements about `Mem`, the proof layer's association list, and about
`List Value` arguments.  Neither is a caller's contract: a caller has bytes and
buffers, not an association list, and a caller that hands the pipeline a
document it has not staged is outside the record without being told so.

This module states the wrapper's contract in the pipeline's own vocabulary:

* `RouteLayout` and `stagedStore` are what the wrapper *builds* — the padded
  document window with its three zero-prefix bytes and thirty-two byte
  read-past tail, the POS8 table, the four scratch objects, the two escape-list
  objects, the arena and the event stream, and the five cursor slots;
* `routePre` is what the wrapper *requires* of its caller: a non-empty document
  inside `Limits.default.maxInput`, the parser's two limit exclusions and its
  character policy, a base with room for the prefix, the capacities the four
  growing buffers need, the two cursors' 64-bit room, and the pairwise
  separation of the staged regions;
* `routeStaging` proves that the built staging *is* `pipelineStaging` at the
  route's arguments — so a route that establishes `routePre` discharges
  `Γ_pipeline_units`'s precondition by construction rather than by assertion;
* `routePost` is `pipelineUnitsPost` read at those arguments, and
  `routePost_observe` is its caller-visible projection: the verdict word, the
  four cursor values, the refusal offset, the entry stream, the escape list,
  the arena and the event stream.

# What the wrapper refuses, and why it refuses loudly

Three classes of input are outside the record, and none may fall through to a
simulated call:

* **the empty document** — `pipelineStaging` carries `0 < bs.length` because
  `Γ_utf8.pre` and its post both require it, while the entry test sends a
  zero-length document past the loop and still calls the UTF-8 stage.  The
  record claims nothing about length zero, not even a refusal;
* **depth and token exhaustion** — the pipeline's twenty-argument ABI carries
  no depth or token limit, so it may accept a document the reference parser
  refuses with `.depthExceeded` or `.outOfCapacity`.  `pipelineSpecPre` excludes
  those documents; the route therefore asks `parseBytes` and refuses with the
  parser's own reason;
* **the reference's character policy** — RFC 8259 requires neither of the two
  restrictions the reference enforces: a surrogate escape must form a
  well-formed pair, and no code point may be a noncharacter (RFC 7493 §2.1).
  The ABI has no policy slot, so the object accepts those RFC texts, while the
  reference refuses them with `unpairedSurrogate` or `noncharacter`.  That is a
  weaker replacement, not an equivalent one: the route asks `parseBytes`, reads
  the reference's own reason and byte, and refuses them.  `documentRefusal` is
  the one place the class is recognised, so the wrapper's policy is the
  reference's and not a second guess at it.

`documentRefusal` names each of those, and `layoutRefusal` names the caller-side
layout failures the record's clauses read (prefix room, reserved arm bits, the
four capacities, the two cursors' room, the 32-bit document bound, separation).
`checkRoute` is the pair, in the order the reasons are reported; `routePre` is
the conjunction the two checks accept, and `routePre_iff_checkRoute` is the
statement that the checks accept exactly that domain.  A refusal is an
`Except RouteRefusal`, so `RouteRefusal.message` is the reason a caller sees.

# The executable route, and what it observed

`probes/json/route/` is the route: `RouteMain.lean` stages the document in this
module's shape, `shim.c` is the adapter, and `build.sh` compiles the kernel,
links the object and asserts the symbol is imported.  `check.sh` compares the
Lean route's output with a C driver that stages the document identically: all
122 default-profile corpus rows agree, so the wrapper's staging is the record's
and its outputs are the object's.  The same run refuses the fourteen documents
the reference refuses under its policy (unpaired surrogates and noncharacters)
with the reference's own reason and byte, and reports no remaining divergence:
the object still accepts those RFC texts, which is why `Sigma_pipeline` remains
a statement about the object rather than a theorem of this module, but the
wrapper's caller sees the reference's verdict.

# The native entry point, and what is missing for a Lean program to call it

`pipeline.h`'s symbol is `leanllvm_json_pipeline`, and `nativePipeline` below
declares it at the ABI's address level.  That declaration is not a route: a
Lean program cannot obtain the address of a `ByteArray`'s bytes, because the
only accessor is the runtime's C API (`lean_sarray_cptr`), and no term in
`Init` or `Std` exposes it.  `nativeAdapterSymbol` names the adapter a Lean
caller needs — a C shim taking `ByteArray` arguments, extracting their data
pointers, staging them, and returning the output bytes — and
`kernel/json/README.md` states the other half: "`lake` does not build the
kernel: it is a C unit of the identity, route and bench scripts, not of the
Lean library."  So the missing pieces are named rather than assumed, in
`missingBridgePieces`.

The executable route lives in `probes/json/route/` as a probe: a standalone
Lean module (the kernel is outside Lake, so the route cannot be a `lake` target)
plus the C adapter, built with `lean -c`, `leanc` and `clang` through the flake,
exactly as `probes/app/` drives the comma-mask seam.  Its `check.sh` asserts
that the route's output equals a C driver's on all 122 default-profile corpus
rows — the wrapper builds the record's staging and reports the object's outputs
— that the shell refuses the empty document and an over-bound document with
their reasons before any call, and that it refuses the fourteen documents the
object accepts and the reference refuses under its policy, with the reference's
reason and byte, so no default-profile row diverges from the reference.  The
probe's scan reads the document's string bodies the way the reference's
`scanChars` does; it is applied only to documents the object accepted, which is
the class where the wrapper's verdict can differ, and its one limitation is
stated in the probe's README.  The parser's depth and token exclusions need the
reference parser and are the library's `checkRoute`, exercised by
`DomainCheck.lean`.  What the probe does not establish is the step from the
semantics to the object; see `missingBridgePieces` and the docstring of
`nativePipeline`.
-/
import LeanLLVM.Refinement.JsonPipelineSpec

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEntryIR (pos8Table pos8Table_length)
open LeanLLVM.Refinement.JsonS1MasksIR (carrySlot)

/-! ### A staged byte store

The wrapper builds a memory by writing the bytes it stages at the addresses the
caller's layout names.  `StagedRegion` is one such write; `store` is the memory
it builds; `extents` is the list of `(address, length)` pairs the record's
separation and read sets are stated over. -/
structure StagedRegion where
  /-- The base address the bytes are written at. -/
  addr : Nat
  /-- The bytes the wrapper stages there; its length is the region's extent. -/
  bytes : List UInt8
deriving Repr, DecidableEq

namespace StagedRegion

/-- The memory a list of staged writes builds.  The fold's order does not
matter at separated addresses; the lemmas below only use that the region they
read is one of the writes and every other write is disjoint from it. -/
def store (rs : List StagedRegion) (m : Mem) : Mem :=
  rs.foldr (fun r m => writeBytes m r.addr r.bytes) m

/-- One staged region's `(address, length)` pair. -/
def extent (r : StagedRegion) : Nat × Nat := (r.addr, r.bytes.length)

/-- The staged regions' extents, in order. -/
def extents (rs : List StagedRegion) : List (Nat × Nat) := rs.map extent

/-- The separation `DisjointRegions` states, at two staged regions. -/
def sep (r s : StagedRegion) : Prop :=
  r.addr + r.bytes.length ≤ s.addr ∨ s.addr + s.bytes.length ≤ r.addr

theorem sep_comm {r s : StagedRegion} (h : sep r s) : sep s r := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

end StagedRegion

/-! ### Reads through a store

Two facts carry every read the staging's clauses need: a write at `start` leaves
a range outside `[start, start + bs.length)` alone, and a read inside a written
range returns the written bytes from the requested offset. -/

/-- A write leaves a read whose range is entirely below or above it unchanged. -/
theorem readBytes_writeBytes_outside (m : Mem) (bs : List UInt8) :
    ∀ {start a k : Nat}, start + bs.length ≤ a ∨ a + k ≤ start →
      readBytes (writeBytes m start bs) a k = readBytes m a k
  | start, a, 0, _ => by simp only [readBytes]
  | start, a, k + 1, h => by
      have ha : a < start ∨ start + bs.length ≤ a := by
        rcases h with h | h
        · exact Or.inr h
        · exact Or.inl (by omega)
      simp only [readBytes]
      rw [readByte_writeBytes_outside m bs ha]
      cases hr : readByte m a with
      | none => rfl
      | some b =>
          have h' : start + bs.length ≤ a + 1 ∨ (a + 1) + k ≤ start := by
            rcases h with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          rw [readBytes_writeBytes_outside m bs (start := start) (a := a + 1) (k := k) h']

/-- A read inside a written range returns the written bytes from the requested
offset.  This is the byte-level content of a staged region: the write is the
last one applied at its own address, so the bytes below it shadow whatever the
memory held. -/
theorem readBytes_writeBytes_from (m : Mem) (bs : List UInt8) (a j k : Nat)
    (h : j + k ≤ bs.length) :
    readBytes (writeBytes m a bs) (a + j) k = some ((bs.drop j).take k) := by
  have hsame : readBytes (writeBytes m a bs) a bs.length = some bs :=
    readBytes_writeBytes_same m bs
  have hsplit : bs.length = j + (bs.length - j) := by omega
  rw [hsplit] at hsame
  obtain ⟨-, h2⟩ := readBytes_split (writeBytes m a bs) a j (bs.length - j) hsame
  have hk : bs.length - j = k + (bs.length - j - k) := by omega
  rw [hk] at h2
  obtain ⟨h3, -⟩ :=
    readBytes_split (writeBytes m a bs) (a + j) k (bs.length - j - k) h2
  exact h3

/-- Every write in the list is outside the read's range, so the read is the
underlying memory's. -/
theorem readBytes_store_outside {rs : List StagedRegion} {m : Mem} {a k : Nat}
    (h : ∀ r ∈ rs, r.addr + r.bytes.length ≤ a ∨ a + k ≤ r.addr) :
    readBytes (StagedRegion.store rs m) a k = readBytes m a k := by
  induction rs generalizing m with
  | nil => simp only [StagedRegion.store, List.foldr_nil]
  | cons r rest ih =>
      show readBytes (writeBytes (StagedRegion.store rest m) r.addr r.bytes) a k =
        readBytes m a k
      rw [readBytes_writeBytes_outside (StagedRegion.store rest m) r.bytes
        (start := r.addr) (a := a) (k := k) (h r (List.mem_cons_self ..))]
      exact ih (fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- A read of a region's own bytes through the store: the region is one of the
writes, and the write's bytes are the last thing at its own address, so the read
inside it returns them. -/
theorem readBytes_store_at {rs : List StagedRegion} {m : Mem} {r : StagedRegion}
    (hmem : r ∈ rs) (hsep : DisjointRegions (StagedRegion.extents rs))
    (j k : Nat) (hjk : j + k ≤ r.bytes.length) :
    readBytes (StagedRegion.store rs m) (r.addr + j) k =
      some ((r.bytes.drop j).take k) := by
  induction rs generalizing m with
  | nil => simp at hmem
  | cons s rest ih =>
      show readBytes (writeBytes (StagedRegion.store rest m) s.addr s.bytes)
        (r.addr + j) k = some ((r.bytes.drop j).take k)
      simp only [DisjointRegions, StagedRegion.extents, List.map_cons,
        List.pairwise_cons] at hsep
      obtain ⟨hsx, hsrest⟩ := hsep
      by_cases hsr : s = r
      · subst hsr
        exact readBytes_writeBytes_from (StagedRegion.store rest m) s.bytes s.addr j k hjk
      · have hmem' : r ∈ rest := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hsr
          · exact h
        have hsep_sr : s.addr + s.bytes.length ≤ r.addr ∨
            r.addr + r.bytes.length ≤ s.addr := by
          have := hsx (StagedRegion.extent r) (List.mem_map_of_mem hmem')
          simpa only [StagedRegion.extent] using this
        rw [readBytes_writeBytes_outside (StagedRegion.store rest m) s.bytes
          (start := s.addr) (a := r.addr + j) (k := k) ?_]
        · exact ih hmem' hsrest
        · rcases hsep_sr with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)

/-- The region's own extent is present: a read of any prefix length returns the
staged bytes' prefix. -/
theorem hasBytes_store_of_mem {rs : List StagedRegion} {m : Mem} {r : StagedRegion}
    (hmem : r ∈ rs) (hsep : DisjointRegions (StagedRegion.extents rs))
    (k : Nat) (hk : k ≤ r.bytes.length) :
    HasBytes (StagedRegion.store rs m) r.addr k :=
  ⟨(r.bytes.take k), by
    have := readBytes_store_at (m := m) hmem hsep 0 k (by omega)
    simpa using this⟩

/-- A store read of a region's whole staged bytes. -/
theorem store_read_full {rs : List StagedRegion} {m : Mem} {r : StagedRegion}
    (hmem : r ∈ rs) (hsep : DisjointRegions (StagedRegion.extents rs)) :
    readBytes (StagedRegion.store rs m) r.addr r.bytes.length = some r.bytes := by
  have h := readBytes_store_at (m := m) hmem hsep 0 r.bytes.length (by omega)
  rw [Nat.add_zero, List.drop_zero, List.take_length] at h
  exact h

/-! ### The route's layout and the staging it builds

Addresses and capacities are the caller's; the bytes are the wrapper's. -/
structure RouteLayout where
  base : Nat
  tab : Nat
  sc : Nat
  mkSlot : Nat
  entw : Nat
  ep : Nat
  nk : Nat
  xp : Nat
  nxp : Nat
  xcarry : Nat
  dst : Nat
  ndst : Nat
  ev : Nat
  nev : Nat
  err : Nat
  epcap : Nat
  xpcap : Nat
  dstcap : Nat
  evcap : Nat
  arm : Nat
  nxp0 : Nat
  ndst0 : Nat
  nev0 : Nat
deriving Repr, DecidableEq

/-- The padded document window's block count, in bytes: the document's
`pipelineBlocks` blocks of sixty-four bytes. -/
def routeBlocks (doc : List UInt8) : Nat := 64 * pipelineBlocks doc.length

/-- The document's padded window: the three zero bytes `Γ_utf8.pre` reads below
the base, the document, and the zero padding the mask unit's last block reads. -/
def windowBytes (doc : List UInt8) : List UInt8 :=
  List.replicate 3 0 ++ doc ++ List.replicate (routeBlocks doc - doc.length) 0

/-- The staged regions, exactly the sixteen `pipelineRegions` names, at the
extents it names.  The document's window and its read-past tail are two writes
because they are two regions; the tail is presence only, which is why it is
zeros. -/
def stagedStore (l : RouteLayout) (doc : List UInt8) : List StagedRegion :=
  [ { addr := l.base - 3, bytes := windowBytes doc },
    { addr := l.base + routeBlocks doc, bytes := List.replicate 32 0 },
    { addr := l.tab, bytes := pos8Table },
    { addr := l.sc, bytes := carrySlot false false false },
    { addr := l.mkSlot, bytes := List.replicate 48 0 },
    { addr := l.entw, bytes := List.replicate 8 0 },
    { addr := l.ep, bytes := List.replicate (4 * (routeBlocks doc + 9)) 0 },
    { addr := l.nk, bytes := wordBytes 8 0 },
    { addr := l.xp, bytes := List.replicate (4 * (l.nxp0 + routeBlocks doc + 8)) 0 },
    { addr := l.nxp, bytes := wordBytes 8 l.nxp0 },
    { addr := l.xcarry, bytes := List.replicate 16 0 },
    { addr := l.dst, bytes := List.replicate l.dstcap 0 },
    { addr := l.ndst, bytes := wordBytes 8 l.ndst0 },
    { addr := l.ev, bytes := List.replicate l.evcap 0 },
    { addr := l.nev, bytes := wordBytes 8 l.nev0 },
    { addr := l.err, bytes := List.replicate 8 0 } ]

/-- The memory the wrapper stages. -/
def stagedMem (l : RouteLayout) (doc : List UInt8) : Mem :=
  StagedRegion.store (stagedStore l doc) []

/-- The staged extents, which is what `routePre` separates. -/
def stagedExtents (l : RouteLayout) (doc : List UInt8) : List (Nat × Nat) :=
  StagedRegion.extents (stagedStore l doc)

/-- The pipeline's twenty-argument ABI at the route's layout (`pipeline.h`'s
`leanllvm_json_pipeline`). -/
def routeArgs (l : RouteLayout) (doc : List UInt8) : List Value :=
  [.ptr l.base, .int 64 (BitVec.ofNat 64 doc.length), .ptr l.sc, .ptr l.mkSlot,
   .ptr l.entw, .ptr l.ep, .int 64 (BitVec.ofNat 64 l.epcap), .ptr l.nk,
   .ptr l.xp, .int 64 (BitVec.ofNat 64 l.xpcap), .ptr l.nxp, .ptr l.xcarry,
   .ptr l.dst, .int 64 (BitVec.ofNat 64 l.dstcap), .ptr l.ndst, .ptr l.ev,
   .int 64 (BitVec.ofNat 64 l.evcap), .ptr l.nev, .ptr l.err,
   .int 64 (BitVec.ofNat 64 l.arm)]

/-! ### The route's precondition

The document sign is the reference parser's own: the two limit exclusions the
ABI does not carry, and the character policy the reference enforces on top of
RFC 8259.  The layout sign is read from the record's own staging.  Every clause
is named here so a caller can check it before any call. -/

/-- The reference parser's character policy: the two `Reject` reasons whose input
is still an RFC 8259 text.  RFC 8259 admits a lone surrogate escape and every
noncharacter; RFC 7493 §2.1's character restriction is the reference's own,
stronger policy, and `parseBytes` reports which restriction refused the text and
at which byte. -/
def PolicyRefusal (e : ParseError) : Prop :=
  ∃ k, e = .invalid (.unpairedSurrogate k) ∨ e = .invalid (.noncharacter k)

/-- `routePre` is what the wrapper requires of its caller. -/
def routePre (l : RouteLayout) (doc : List UInt8) : Prop :=
  -- the document is in the record's domain: non-empty, inside the input bound,
  -- not a limit refusal on either count the ABI does not carry, and not a
  -- character-policy refusal: the reference is stricter than RFC 8259, and the
  -- wrapper must refuse what it refuses
  0 < doc.length ∧
  doc.length ≤ Limits.default.maxInput ∧
  (∀ e : ParseError,
    parseBytes Limits.default (ByteString.literal doc) = .error e →
      e ≠ .depthExceeded ∧ e ≠ .outOfCapacity ∧ ¬ PolicyRefusal e) ∧
  -- the base has room for the UTF-8 stage's three prefix bytes
  3 ≤ l.base ∧
  -- the capacities, at 64-bit widths
  l.epcap < 2 ^ 64 ∧ l.xpcap < 2 ^ 64 ∧
  l.dstcap < 2 ^ 64 ∧ l.evcap < 2 ^ 64 ∧
  64 * pipelineBlocks doc.length + 9 ≤ l.epcap ∧
  -- the arena and the event stream: the reached extent and the write room
  l.ndst0 + doc.length + 64 ≤ l.dstcap ∧
  l.nev0 + 13 * doc.length ≤ l.evcap ∧
  -- the two growing cursors' room, and the 32-bit document bound
  cursorRoom 0 (pipelineBlocks doc.length) 9 ∧
  cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 ∧
  64 * pipelineBlocks doc.length + 63 < 2 ^ 32 ∧
  -- the arm selector's reserved bits
  l.arm < 8 ∧
  -- every staged object is separate
  DisjointRegions (stagedExtents l doc)

/-! ### Reads at the route's regions

The four facts below are the regions the record reads by name, at the bytes the
wrapper stages.  Each is `readBytes_store_at` or `hasBytes_store_of_mem` at one
member of `stagedStore`. -/

theorem mem_window (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.base - 3, bytes := windowBytes doc } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_self ..

theorem mem_tail (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.base + routeBlocks doc, bytes := List.replicate 32 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem mem_table (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.tab, bytes := pos8Table } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem mem_sc (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.sc, bytes := carrySlot false false false } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem mem_mkSlot (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.mkSlot, bytes := List.replicate 48 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem mem_entw (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.entw, bytes := List.replicate 8 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

theorem mem_ep (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.ep, bytes := List.replicate (4 * (routeBlocks doc + 9)) 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))

theorem mem_nk (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.nk, bytes := wordBytes 8 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))

theorem mem_xp (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.xp, bytes := List.replicate (4 * (l.nxp0 + routeBlocks doc + 8)) 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))

theorem mem_nxp (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.nxp, bytes := wordBytes 8 l.nxp0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))

theorem mem_xcarry (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.xcarry, bytes := List.replicate 16 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))

theorem mem_dst (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.dst, bytes := List.replicate l.dstcap 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))

theorem mem_ndst (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.ndst, bytes := wordBytes 8 l.ndst0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))

theorem mem_ev (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.ev, bytes := List.replicate l.evcap 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))

theorem mem_nev (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.nev, bytes := wordBytes 8 l.nev0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))

theorem mem_err (l : RouteLayout) (doc : List UInt8) :
    ({ addr := l.err, bytes := List.replicate 8 0 } : StagedRegion) ∈ stagedStore l doc := by
  simp only [stagedStore]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))

/-- The document is at most its block count's bytes: a corner of every window
arithmetic below. -/
theorem length_le_routeBlocks (doc : List UInt8) : doc.length ≤ routeBlocks doc := by
  have h := Nat.div_add_mod (doc.length + 63) 64
  have hr := Nat.mod_lt (doc.length + 63) (by decide : 0 < 64)
  have : doc.length ≤ 64 * ((doc.length + 63) / 64) := by omega
  simpa only [routeBlocks, pipelineBlocks] using this

/-- The staged window's bytes have the window's length. -/
theorem windowBytes_length (doc : List UInt8) :
    (windowBytes doc).length = 3 + routeBlocks doc := by
  simp only [windowBytes, List.length_append, List.length_replicate]
  have := length_le_routeBlocks doc
  omega

/-- The window's document read: the padded window from the caller's base. -/
theorem windowBytes_drop (doc : List UInt8) :
    (windowBytes doc).drop 3 =
      doc ++ List.replicate (routeBlocks doc - doc.length) 0 := by
  rw [windowBytes, List.append_assoc]
  exact List.drop_left' (by simp)

/-- The window's three prefix bytes. -/
theorem windowBytes_take (doc : List UInt8) :
    (windowBytes doc).take 3 = List.replicate 3 0 := by
  rw [windowBytes, List.append_assoc]
  exact List.take_left' (by simp)

/-- A rounded block count covers the document. -/
theorem routeBlocks_eq (doc : List UInt8) :
    routeBlocks doc = 64 * pipelineBlocks doc.length := rfl

/-- The table's bytes have the table's length. -/
theorem pos8Table_extent : pos8Table.length = 8192 := pos8Table_length

/-! ### The route's discharge of the record's precondition -/

/-- `(BitVec.ofNat 64 x).toNat = x` below the width. -/
theorem bitVecOfNat_toNat {x : Nat} (h : x < 2 ^ 64) :
    (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The document window the record reads, from the staged store. -/
theorem stagedWindow_read (l : RouteLayout) (doc : List UInt8)
    (hsep : DisjointRegions (stagedExtents l doc)) (hb3 : 3 ≤ l.base) :
    readBytes (stagedMem l doc) l.base (routeBlocks doc) =
      some (doc ++ List.replicate (routeBlocks doc - doc.length) 0) := by
  have h := readBytes_store_at (m := []) (mem_window l doc) hsep 3 (routeBlocks doc)
    (by rw [windowBytes_length]; omega)
  have hbase : l.base - 3 + 3 = l.base := by omega
  have hlen : (doc ++ List.replicate (routeBlocks doc - doc.length) 0).length =
      routeBlocks doc := by
    have := length_le_routeBlocks doc
    simp only [List.length_append, List.length_replicate]
    omega
  have htake : ((windowBytes doc).drop 3).take (routeBlocks doc) =
      doc ++ List.replicate (routeBlocks doc - doc.length) 0 := by
    rw [windowBytes_drop]
    exact List.take_of_length_le (by simp [hlen])
  have h' : readBytes (stagedMem l doc) (l.base - 3 + 3) (routeBlocks doc) =
      some (((windowBytes doc).drop 3).take (routeBlocks doc)) := h
  rw [hbase, htake] at h'
  exact h'

/-- The three prefix bytes the UTF-8 stage reads below the base. -/
theorem stagedPrefix_read (l : RouteLayout) (doc : List UInt8)
    (hsep : DisjointRegions (stagedExtents l doc)) :
    readBytes (stagedMem l doc) (l.base - 3) 3 = some (List.replicate 3 0) := by
  have h := readBytes_store_at (m := []) (mem_window l doc) hsep 0 3
    (by rw [windowBytes_length]; omega)
  have htake : (windowBytes doc).take 3 = List.replicate 3 0 := windowBytes_take doc
  rw [show l.base - 3 + 0 = l.base - 3 from by omega, List.drop_zero, htake] at h
  exact h

/-- The record's region list is the store's extents: the wrapper stages exactly
the sixteen objects `pipelineRegions` names, at the extents it names. -/
theorem pipelineRegions_eq_stagedExtents (l : RouteLayout) (doc : List UInt8)
    (h : doc.length < 2 ^ 64) (hdst : l.dstcap < 2 ^ 64) (hev : l.evcap < 2 ^ 64) :
    pipelineRegions l.base l.tab 0 l.nxp0 (routeArgs l doc) = stagedExtents l doc := by
  simp only [pipelineRegions, routeArgs, stagedExtents, stagedStore,
    StagedRegion.extents, routeBlocks, bitVecOfNat_toNat h,
    bitVecOfNat_toNat hdst, bitVecOfNat_toNat hev, Nat.zero_add,
    List.map_cons, List.map_nil, StagedRegion.extent, List.length_replicate,
    pos8Table_length, windowBytes_length, wordBytes, natToBytes_length]
  have hcarry : (carrySlot false false false).length = 24 := by
    simp [carrySlot, flagBytes, natToBytes_length]
  simpa only [hcarry]

/-- The record's read set, at the route's arguments, is the thirteen staged
objects it names. -/
theorem pipelineReads_eq (l : RouteLayout) (doc : List UInt8)
    (h : doc.length < 2 ^ 64) :
    pipelineReads l.base l.tab 0 l.nxp0 (routeArgs l doc) =
      [ (l.base - 3, 3 + routeBlocks doc), (l.tab, 8192), (l.sc, 24),
        (l.mkSlot, 48), (l.entw, 8), (l.ep, 4 * (routeBlocks doc + 9)),
        (l.nk, 8), (l.xp, 4 * (l.nxp0 + routeBlocks doc + 8)), (l.nxp, 8),
        (l.xcarry, 16), (l.ndst, 8), (l.nev, 8), (l.err, 8) ] := by
  simp only [pipelineReads, routeArgs, routeBlocks, bitVecOfNat_toNat h, Nat.zero_add]

/-- Every region the record's read set names is present at the staged extent. -/
theorem stagedReads_hasBytes (l : RouteLayout) (doc : List UInt8)
    (h : doc.length < 2 ^ 64) (hsep : DisjointRegions (stagedExtents l doc)) :
    ∀ r ∈ pipelineReads l.base l.tab 0 l.nxp0 (routeArgs l doc),
      HasBytes (stagedMem l doc) r.1 r.2 := by
  intro r hr
  rw [pipelineReads_eq l doc h] at hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with h1|h1|h1|h1|h1|h1|h1|h1|h1|h1|h1|h1|h1 <;> subst h1
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_window l doc) hsep (3 + routeBlocks doc)
        (by rw [windowBytes_length]; omega)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_table l doc) hsep 8192 (by rw [pos8Table_extent]; omega)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_sc l doc) hsep 24
        (by simp [carrySlot, flagBytes, natToBytes_length])
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_mkSlot l doc) hsep 48 (by simp)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_entw l doc) hsep 8 (by simp)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_ep l doc) hsep (4 * (routeBlocks doc + 9)) (by simp)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_nk l doc) hsep 8 (by simp [wordBytes, natToBytes_length])
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_xp l doc) hsep
        (4 * (l.nxp0 + routeBlocks doc + 8)) (by simp)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_nxp l doc) hsep 8 (by simp [wordBytes, natToBytes_length])
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_xcarry l doc) hsep 16 (by simp)
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_ndst l doc) hsep 8 (by simp [wordBytes, natToBytes_length])
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_nev l doc) hsep 8 (by simp [wordBytes, natToBytes_length])
  · simpa only [stagedMem] using
      hasBytes_store_of_mem (mem_err l doc) hsep 8 (by simp)

/-- **The wrapper's contract discharges the record's precondition.**  A caller
that establishes `routePre` and hands the wrapper its document and layout has
staged `pipelineStaging` at the route's own arguments: every clause of the
record's staging is one of the reads, capacities, or separations the wrapper
built.  The proof is the construction, not an assumption. -/
theorem routeStaging (l : RouteLayout) (doc : List UInt8)
    (h : routePre l doc) :
    pipelineStaging l.tab l.base (routeArgs l doc) (stagedMem l doc) := by
  obtain ⟨hpos, hlim, hdom, hb3, hep64, hxp64, hdst64, hev64, hepcap, hdst, hev,
    hroom0, hroomx, h32, harm, hsep⟩ := h
  have hdoc64 : doc.length < 2 ^ 64 := by
    have : doc.length ≤ 1048576 := by simpa [Limits.default] using hlim
    omega
  have hlen := length_le_routeBlocks doc
  have hblocks : (BitVec.ofNat 64 doc.length).toNat = doc.length :=
    bitVecOfNat_toNat hdoc64
  have hepcap' : (BitVec.ofNat 64 l.epcap).toNat = l.epcap := bitVecOfNat_toNat hep64
  have hxpcap' : (BitVec.ofNat 64 l.xpcap).toNat = l.xpcap := bitVecOfNat_toNat hxp64
  have hdst64' : (BitVec.ofNat 64 l.dstcap).toNat = l.dstcap := bitVecOfNat_toNat hdst64
  have hev64' : (BitVec.ofNat 64 l.evcap).toNat = l.evcap := bitVecOfNat_toNat hev64
  have harm' : (BitVec.ofNat 64 l.arm).toNat = l.arm :=
    bitVecOfNat_toNat (by omega)
  refine ⟨l.sc, l.mkSlot, l.entw, l.ep, l.nk, l.xp, l.nxp, l.xcarry, l.dst, l.ndst,
    l.ev, l.nev, l.err, l.nxp0, l.ndst0, l.nev0, _, _, _, _, _, _, doc,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- n.toNat = bs.length
    simpa only [hblocks]
  · -- the input bound
    exact hlim
  · -- the padded document window
    simpa only [routeBlocks_eq] using stagedWindow_read l doc hsep hb3
  · -- the read-past tail
    exact hasBytes_store_of_mem (mem_tail l doc) hsep 32 (by simp)
  · exact hb3
  · -- the three zero bytes below the base
    exact stagedPrefix_read l doc hsep
  · exact hpos
  · -- the table
    simpa only [stagedMem, pos8Table_extent] using store_read_full (m := []) (mem_table l doc) hsep
  · -- the mask unit's carry slot
    simpa only [stagedMem, show (carrySlot false false false).length = 24 from by
      simp [carrySlot, natToBytes_length]] using
      store_read_full (m := []) (mem_sc l doc) hsep
  · -- the escape list's carry pair
    have hread := store_read_full (m := []) (mem_xcarry l doc) hsep
    have hlen16 : (List.replicate 16 (0 : UInt8)).length = 16 := by simp
    have hflags : List.replicate 16 (0 : UInt8) = flagBytes false ++ flagBytes false := by
      decide
    rw [hlen16, hflags] at hread
    exact ⟨by simpa only [stagedMem] using hread, rfl⟩
  · -- the entry count slot
    simpa only [stagedMem, wordBytes, natToBytes_length] using store_read_full (m := []) (mem_nk l doc) hsep
  · -- the escape count slot
    simpa only [stagedMem, wordBytes, natToBytes_length] using store_read_full (m := []) (mem_nxp l doc) hsep
  · -- the entry stream's capacity
    simpa only [hepcap']
  · -- the escape list's capacity
    simpa only [stagedMem, routeBlocks] using hasBytes_store_of_mem (m := []) (mem_xp l doc) hsep
      (4 * (l.nxp0 + routeBlocks doc + 8)) (by simp)
  · -- the arena's reached extent inside its capacity
    simpa only [hblocks, hdst64'] using hdst
  · -- the arena's presence
    simpa only [stagedMem, hdst64'] using
      hasBytes_store_of_mem (m := []) (mem_dst l doc) hsep l.dstcap (by simp)
  · -- the event stream's presence
    simpa only [stagedMem, hev64'] using
      hasBytes_store_of_mem (m := []) (mem_ev l doc) hsep l.evcap (by simp)
  · -- the event stream's write room
    simpa only [hblocks, hev64'] using hev
  · -- the arena cursor
    simpa only [stagedMem, wordBytes, natToBytes_length] using store_read_full (m := []) (mem_ndst l doc) hsep
  · -- the event cursor
    simpa only [stagedMem, wordBytes, natToBytes_length] using store_read_full (m := []) (mem_nev l doc) hsep
  · simpa only [hblocks] using hroom0
  · simpa only [hblocks] using hroomx
  · simpa only [hblocks] using h32
  · simpa only [harm']
  · -- the read set
    exact stagedReads_hasBytes l doc hdoc64 hsep
  · -- separation
    rw [pipelineRegions_eq_stagedExtents l doc hdoc64 hdst64 hev64]
    exact hsep

/-- The document's exact-length read at the caller's base, which is
`pipelineSpecPre`'s input relation and not a clause of `pipelineStaging`. -/
theorem stagedDoc_read (l : RouteLayout) (doc : List UInt8)
    (hsep : DisjointRegions (stagedExtents l doc)) (hb3 : 3 ≤ l.base) :
    readBytes (stagedMem l doc) l.base doc.length = some doc := by
  have hlen := length_le_routeBlocks doc
  have h := readBytes_store_at (m := []) (mem_window l doc) hsep 3 doc.length
    (by rw [windowBytes_length]; omega)
  have hbase : l.base - 3 + 3 = l.base := by omega
  have hdrop : (windowBytes doc).drop 3 =
      doc ++ List.replicate (routeBlocks doc - doc.length) 0 := windowBytes_drop doc
  have htake : ((windowBytes doc).drop 3).take doc.length = doc := by
    rw [hdrop, List.take_left]
  have h' : readBytes (stagedMem l doc) (l.base - 3 + 3) doc.length =
      some (((windowBytes doc).drop 3).take doc.length) := h
  rw [hbase, htake] at h'
  exact h'

/-- **The wrapper discharges the specification's precondition.**  `routePre`
establishes `pipelineSpecPre` at the route's arguments: the units staging, the
document's exact-length read, the ABI projections, the event cursor, and the
parser's two limit exclusions.  A caller that the check accepts can be handed
to `Γ_pipeline`'s domain without a further premise. -/
theorem routeSpecPre (l : RouteLayout) (doc : List UInt8)
    (h : routePre l doc) :
    pipelineSpecPre l.tab l.base (routeArgs l doc) (stagedMem l doc) 0 := by
  obtain ⟨hpos, hlim, hdom, hb3, hep64, hxp64, hdst64, hev64, hepcap, hdst, hev,
    hroom0, hroomx, h32, harm, hsep⟩ := h
  have hdoc64 : doc.length < 2 ^ 64 := by
    have : doc.length ≤ 1048576 := by simpa [Limits.default] using hlim
    omega
  have hblocks : (BitVec.ofNat 64 doc.length).toNat = doc.length :=
    bitVecOfNat_toNat hdoc64
  have hev64' : (BitVec.ofNat 64 l.evcap).toNat = l.evcap := bitVecOfNat_toNat hev64
  -- `pipelineSpecPre` states the two limit exclusions; the policy exclusion is
  -- the wrapper's own, and is not a clause of the record's precondition.
  have hdom' : ∀ e : ParseError,
      parseBytes Limits.default (ByteString.literal doc) = .error e →
        e ≠ .depthExceeded ∧ e ≠ .outOfCapacity :=
    fun e he => ⟨(hdom e he).1, (hdom e he).2.1⟩
  refine ⟨routeStaging l doc ⟨hpos, hlim, hdom, hb3, hep64, hxp64, hdst64, hev64,
    hepcap, hdst, hev, hroom0, hroomx, h32, harm, hsep⟩, doc, l.nev0, l.evcap,
    l.nev, ?_, ?_, ?_, stagedDoc_read l doc hsep hb3, ?_, hdom'⟩
  · simp only [pipelineDocLength, routeArgs, hblocks]
  · simp only [pipelineEvCapacity, routeArgs, hev64']
  · simp only [pipelineNevSlot, routeArgs]
  · have h := store_read_full (m := []) (mem_nev l doc) hsep
    simpa only [stagedMem, wordBytes, natToBytes_length] using h

/-! ### The domain the record excludes -/

/-- The record has no term for an empty document, no depth or token limit, and no
character-policy slot, and a caller that hands the route any of those is outside
the domain rather than in a failure case.  The refusals below name the reason,
so the route never falls through to a call the record does not cover. -/
inductive RouteRefusal where
  | emptyInput
  | inputTooLong (bound : Nat)
  | depthExceeded
  | tokenExhausted
  | unpairedSurrogate (pos : Nat)
  | noncharacter (pos : Nat)
  | noPrefixRoom (base : Nat)
  | armReserved (arm : Nat)
  | entryCapacity (required cap : Nat)
  | arenaCapacity (required cap : Nat)
  | eventCapacity (room cap : Nat)
  | capacityWidth (cap : Nat)
  | cursorRoom (count : Nat)
  | documentBound (required : Nat)
  | overlappingRegions
deriving DecidableEq, Repr

/-- The reason a refused caller sees.  Every refusal names the clause it failed;
none reports a generic error. -/
def RouteRefusal.message : RouteRefusal → String
  | .emptyInput =>
      "empty input: the pipeline record's domain requires a non-empty document"
  | .inputTooLong bound =>
      s!"input too long: the record's bound is {bound} bytes"
  | .depthExceeded =>
      "out of domain: the reference parser refuses this document with depthExceeded, \
       and the pipeline ABI carries no depth limit"
  | .tokenExhausted =>
      "out of domain: the reference parser refuses this document with outOfCapacity, \
       and the pipeline ABI carries no token limit"
  | .unpairedSurrogate pos =>
      s!"out of domain: the reference parser refuses an unpaired surrogate at byte {pos}, \
       and the pipeline ABI carries no character-policy slot"
  | .noncharacter pos =>
      s!"out of domain: the reference parser refuses a noncharacter at byte {pos}, \
       and the pipeline ABI carries no character-policy slot"
  | .noPrefixRoom base =>
      s!"no prefix room: the base {base} has fewer than three bytes below it"
  | .armReserved arm =>
      s!"reserved arm bits: the arm word {arm} has a bit at or above three set"
  | .entryCapacity required cap =>
      s!"entry stream capacity {cap} is below the required {required} words"
  | .arenaCapacity required cap =>
      s!"arena capacity {cap} is below the required {required} bytes"
  | .eventCapacity room cap =>
      s!"event stream capacity {cap} is below the required write room {room} bytes"
  | .capacityWidth cap =>
      s!"capacity {cap} does not fit the ABI's 64-bit word"
  | .cursorRoom count =>
      s!"cursor room: a growing cursor at {count} leaves the 64-bit domain"
  | .documentBound required =>
      s!"document bound: {required} bytes overflow the 32-bit entry positions"
  | .overlappingRegions =>
      "overlapping staged regions: the record requires pairwise separation"

/-- The document's own domain check: the empty document, the input bound, the
two limits the ABI does not carry, and the reference parser's character policy.
`parseBytes` is the reference parser's own predicate, so every exclusion is the
parser's policy rather than a second guess at it, and each refusal names the
byte `parseBytes` named. -/
def documentRefusal (doc : List UInt8) : Option RouteRefusal :=
  if doc.length = 0 then some .emptyInput
  else if Limits.default.maxInput < doc.length then
    some (.inputTooLong Limits.default.maxInput)
  else
    match parseBytes Limits.default (ByteString.literal doc) with
    | .error .depthExceeded => some .depthExceeded
    | .error .outOfCapacity => some .tokenExhausted
    | .error (.invalid (.unpairedSurrogate k)) => some (.unpairedSurrogate k)
    | .error (.invalid (.noncharacter k)) => some (.noncharacter k)
    | _ => none

/-- `cursorRoom` is arithmetic, so its check is decidable. -/
instance cursorRoomDecidable (count blocks reserve : Nat) : Decidable (cursorRoom count blocks reserve) := by
  unfold cursorRoom
  infer_instance

/-- `DisjointRegions` is a pairwise separation, so its check is decidable. -/
instance disjointRegionsDecidable (rs : List (Nat × Nat)) : Decidable (DisjointRegions rs) := by
  unfold DisjointRegions
  infer_instance

/-- The caller-side layout check: the prefix room, the arm's reserved bits, the
four capacities, the two cursors' room, the 32-bit document bound, the 64-bit
width of each capacity, and the staged regions' separation. -/
def layoutRefusal (l : RouteLayout) (doc : List UInt8) : Option RouteRefusal :=
  if l.base < 3 then some (.noPrefixRoom l.base)
  else if 8 ≤ l.arm then some (.armReserved l.arm)
  else if l.epcap < 64 * pipelineBlocks doc.length + 9 then
    some (.entryCapacity (64 * pipelineBlocks doc.length + 9) l.epcap)
  else if l.dstcap < l.ndst0 + doc.length + 64 then
    some (.arenaCapacity (l.ndst0 + doc.length + 64) l.dstcap)
  else if l.evcap < l.nev0 + 13 * doc.length then
    some (.eventCapacity (l.nev0 + 13 * doc.length) l.evcap)
  else if ¬ cursorRoom 0 (pipelineBlocks doc.length) 9 then
    some (.cursorRoom 0)
  else if ¬ cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 then
    some (.cursorRoom l.nxp0)
  else if 2 ^ 32 ≤ 64 * pipelineBlocks doc.length + 63 then
    some (.documentBound (64 * pipelineBlocks doc.length + 63))
  else if ¬ (l.epcap < 2 ^ 64 ∧ l.xpcap < 2 ^ 64 ∧
      l.dstcap < 2 ^ 64 ∧ l.evcap < 2 ^ 64) then
    some (.capacityWidth (max (max l.epcap l.xpcap) (max l.dstcap l.evcap)))
  else if ¬ DisjointRegions (stagedExtents l doc) then
    some .overlappingRegions
  else none

/-- The route's whole domain check, in the order the reasons are reported. -/
def checkRoute (l : RouteLayout) (doc : List UInt8) : Except RouteRefusal Unit :=
  match documentRefusal doc with
  | some r => .error r
  | none =>
      match layoutRefusal l doc with
      | some r => .error r
      | none => .ok ()

/-- The empty document is refused by its own reason, before any layout is read. -/
theorem checkRoute_empty (l : RouteLayout) :
    checkRoute l [] = .error .emptyInput := rfl

/-- A document over the input bound is refused with the bound it broke. -/
theorem checkRoute_tooLong (l : RouteLayout) (doc : List UInt8)
    (h : Limits.default.maxInput < doc.length) :
    checkRoute l doc = .error (.inputTooLong Limits.default.maxInput) := by
  have hne : doc.length ≠ 0 := by
    have : 0 < Limits.default.maxInput := by decide
    omega
  simp only [checkRoute, documentRefusal, if_neg hne, if_pos h]

/-- A document the reference parser refuses for depth is refused with that
reason. -/
theorem checkRoute_depth (l : RouteLayout) (doc : List UInt8)
    (h : 0 < doc.length) (hlim : ¬ Limits.default.maxInput < doc.length)
    (hparse : parseBytes Limits.default (ByteString.literal doc) = .error .depthExceeded) :
    checkRoute l doc = .error .depthExceeded := by
  have hne : ¬ doc.length = 0 := by omega
  simp only [checkRoute, documentRefusal, if_neg hne, if_neg hlim, hparse]

/-- A document the reference parser refuses for token capacity is refused with
that reason. -/
theorem checkRoute_tokens (l : RouteLayout) (doc : List UInt8)
    (h : 0 < doc.length) (hlim : ¬ Limits.default.maxInput < doc.length)
    (hparse : parseBytes Limits.default (ByteString.literal doc) = .error .outOfCapacity) :
    checkRoute l doc = .error .tokenExhausted := by
  have hne : ¬ doc.length = 0 := by omega
  simp only [checkRoute, documentRefusal, if_neg hne, if_neg hlim, hparse]

/-- A document whose first policy refusal is an unpaired surrogate is refused
with that reason and the reference parser's position. -/
theorem checkRoute_unpairedSurrogate (l : RouteLayout) (doc : List UInt8)
    (h : 0 < doc.length) (hlim : ¬ Limits.default.maxInput < doc.length) (pos : Nat)
    (hparse : parseBytes Limits.default (ByteString.literal doc) =
      .error (.invalid (.unpairedSurrogate pos))) :
    checkRoute l doc = .error (.unpairedSurrogate pos) := by
  have hne : ¬ doc.length = 0 := by omega
  simp only [checkRoute, documentRefusal, if_neg hne, if_neg hlim, hparse]

/-- A document whose first policy refusal is a noncharacter is refused with that
reason and the reference parser's position. -/
theorem checkRoute_noncharacter (l : RouteLayout) (doc : List UInt8)
    (h : 0 < doc.length) (hlim : ¬ Limits.default.maxInput < doc.length) (pos : Nat)
    (hparse : parseBytes Limits.default (ByteString.literal doc) =
      .error (.invalid (.noncharacter pos))) :
    checkRoute l doc = .error (.noncharacter pos) := by
  have hne : ¬ doc.length = 0 := by omega
  simp only [checkRoute, documentRefusal, if_neg hne, if_neg hlim, hparse]

/-- **The document check's clauses.**  A `none` from `documentRefusal` is the
record's document domain: non-empty, inside the input bound, not a limit refusal
on either count the ABI does not carry, and not a character-policy refusal of the
reference parser's. -/
theorem documentRefusal_none {doc : List UInt8}
    (hd : documentRefusal doc = none) :
    0 < doc.length ∧ doc.length ≤ Limits.default.maxInput ∧
    (∀ e : ParseError,
      parseBytes Limits.default (ByteString.literal doc) = .error e →
        e ≠ .depthExceeded ∧ e ≠ .outOfCapacity ∧ ¬ PolicyRefusal e) := by
  have hne : doc.length ≠ 0 := by
    intro h0
    rw [documentRefusal, if_pos h0] at hd
    cases hd
  have hbound : ¬ Limits.default.maxInput < doc.length := by
    intro hb
    rw [documentRefusal, if_neg hne, if_pos hb] at hd
    cases hd
  refine ⟨Nat.pos_of_ne_zero hne, by omega, ?_⟩
  intro e he
  refine ⟨?_, ?_, ?_⟩
  · intro hee
    have : documentRefusal doc = some .depthExceeded := by
      rw [documentRefusal, if_neg hne, if_neg hbound, he, hee]
    rw [this] at hd
    cases hd
  · intro hee
    have : documentRefusal doc = some .tokenExhausted := by
      rw [documentRefusal, if_neg hne, if_neg hbound, he, hee]
    rw [this] at hd
    cases hd
  · intro hpr
    rcases hpr with ⟨k, hk | hk⟩
    · have : documentRefusal doc = some (.unpairedSurrogate k) := by
        rw [documentRefusal, if_neg hne, if_neg hbound, he, hk]
      rw [this] at hd
      cases hd
    · have : documentRefusal doc = some (.noncharacter k) := by
        rw [documentRefusal, if_neg hne, if_neg hbound, he, hk]
      rw [this] at hd
      cases hd

/-- **The layout check's clauses.**  A `none` from `layoutRefusal` is every
caller-side clause `routePre` asks for, in the order the check tests them. -/
theorem layoutRefusal_none {l : RouteLayout} {doc : List UInt8}
    (hl : layoutRefusal l doc = none) :
    3 ≤ l.base ∧ l.arm < 8 ∧
    l.epcap < 2 ^ 64 ∧ l.xpcap < 2 ^ 64 ∧
    l.dstcap < 2 ^ 64 ∧ l.evcap < 2 ^ 64 ∧
    64 * pipelineBlocks doc.length + 9 ≤ l.epcap ∧
    l.ndst0 + doc.length + 64 ≤ l.dstcap ∧
    l.nev0 + 13 * doc.length ≤ l.evcap ∧
    cursorRoom 0 (pipelineBlocks doc.length) 9 ∧
    cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 ∧
    64 * pipelineBlocks doc.length + 63 < 2 ^ 32 ∧
    DisjointRegions (stagedExtents l doc) := by
  have hbase : 3 ≤ l.base := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc = some (.noPrefixRoom l.base) := by
      simp only [layoutRefusal, if_pos (show l.base < 3 by omega)]
    rw [this] at hl
    cases hl
  have harm : l.arm < 8 := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc = some (.armReserved l.arm) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_pos (show 8 ≤ l.arm by omega)]
    rw [this] at hl
    cases hl
  have hepcap : 64 * pipelineBlocks doc.length + 9 ≤ l.epcap := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc =
        some (.entryCapacity (64 * pipelineBlocks doc.length + 9) l.epcap) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_pos (show l.epcap < 64 * pipelineBlocks doc.length + 9 by omega)]
    rw [this] at hl
    cases hl
  have hdst : l.ndst0 + doc.length + 64 ≤ l.dstcap := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc =
        some (.arenaCapacity (l.ndst0 + doc.length + 64) l.dstcap) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_pos (show l.dstcap < l.ndst0 + doc.length + 64 by omega)]
    rw [this] at hl
    cases hl
  have hev : l.nev0 + 13 * doc.length ≤ l.evcap := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc =
        some (.eventCapacity (l.nev0 + 13 * doc.length) l.evcap) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_neg (show ¬ l.dstcap < l.ndst0 + doc.length + 64 by omega),
        if_pos (show l.evcap < l.nev0 + 13 * doc.length by omega)]
    rw [this] at hl
    cases hl
  have hroom0 : cursorRoom 0 (pipelineBlocks doc.length) 9 := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc = some (.cursorRoom 0) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_neg (show ¬ l.dstcap < l.ndst0 + doc.length + 64 by omega),
        if_neg (show ¬ l.evcap < l.nev0 + 13 * doc.length by omega),
        if_pos h]
    rw [this] at hl
    cases hl
  have hroomx : cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc = some (.cursorRoom l.nxp0) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_neg (show ¬ l.dstcap < l.ndst0 + doc.length + 64 by omega),
        if_neg (show ¬ l.evcap < l.nev0 + 13 * doc.length by omega),
        if_neg (show ¬ ¬ cursorRoom 0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroom0),
        if_pos h]
    rw [this] at hl
    cases hl
  have h32 : 64 * pipelineBlocks doc.length + 63 < 2 ^ 32 := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc =
        some (.documentBound (64 * pipelineBlocks doc.length + 63)) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_neg (show ¬ l.dstcap < l.ndst0 + doc.length + 64 by omega),
        if_neg (show ¬ l.evcap < l.nev0 + 13 * doc.length by omega),
        if_neg (show ¬ ¬ cursorRoom 0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroom0),
        if_neg (show ¬ ¬ cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroomx),
        if_pos (show 2 ^ 32 ≤ 64 * pipelineBlocks doc.length + 63 by omega)]
    rw [this] at hl
    cases hl
  have hwidths : l.epcap < 2 ^ 64 ∧ l.xpcap < 2 ^ 64 ∧
      l.dstcap < 2 ^ 64 ∧ l.evcap < 2 ^ 64 := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc =
        some (.capacityWidth (max (max l.epcap l.xpcap) (max l.dstcap l.evcap))) := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_neg (show ¬ l.dstcap < l.ndst0 + doc.length + 64 by omega),
        if_neg (show ¬ l.evcap < l.nev0 + 13 * doc.length by omega),
        if_neg (show ¬ ¬ cursorRoom 0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroom0),
        if_neg (show ¬ ¬ cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroomx),
        if_neg (show ¬ 2 ^ 32 ≤ 64 * pipelineBlocks doc.length + 63 by omega),
        if_pos h]
    rw [this] at hl
    cases hl
  have hsep : DisjointRegions (stagedExtents l doc) := by
    apply Classical.byContradiction
    intro h
    have : layoutRefusal l doc = some .overlappingRegions := by
      simp only [layoutRefusal, if_neg (show ¬ l.base < 3 by omega),
        if_neg (show ¬ 8 ≤ l.arm by omega),
        if_neg (show ¬ l.epcap < 64 * pipelineBlocks doc.length + 9 by omega),
        if_neg (show ¬ l.dstcap < l.ndst0 + doc.length + 64 by omega),
        if_neg (show ¬ l.evcap < l.nev0 + 13 * doc.length by omega),
        if_neg (show ¬ ¬ cursorRoom 0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroom0),
        if_neg (show ¬ ¬ cursorRoom l.nxp0 (pipelineBlocks doc.length) 9 by
          intro h; exact h hroomx),
        if_neg (show ¬ 2 ^ 32 ≤ 64 * pipelineBlocks doc.length + 63 by omega),
        if_neg (show ¬ ¬ (l.epcap < 2 ^ 64 ∧ l.xpcap < 2 ^ 64 ∧
          l.dstcap < 2 ^ 64 ∧ l.evcap < 2 ^ 64) by
          intro h; exact h hwidths),
        if_pos h]
    rw [this] at hl
    cases hl
  exact ⟨hbase, harm, hwidths.1, hwidths.2.1, hwidths.2.2.1, hwidths.2.2.2,
    hepcap, hdst, hev, hroom0, hroomx, h32, hsep⟩

/-- **Acceptance implies the record's precondition.**  A `checkRoute` that
accepts has established every clause of `routePre`; this is the bridge a route
uses so that no call reaches the native entry point outside the record's
domain. -/
theorem routePre_of_checkRoute_ok {l : RouteLayout} {doc : List UInt8}
    (h : (checkRoute l doc).isOk = true) : routePre l doc := by
  unfold checkRoute at h
  cases hd : documentRefusal doc with
  | some r => simp [hd, Except.isOk, Except.toBool] at h
  | none =>
      cases hl : layoutRefusal l doc with
      | some r => simp [hd, hl, Except.isOk, Except.toBool] at h
      | none =>
          obtain ⟨hpos, hbound, hdom⟩ := documentRefusal_none hd
          obtain ⟨hbase, harm, hep64, hxp64, hdst64, hev64, hepcap, hdst,
            hev, hroom0, hroomx, h32, hsep⟩ := layoutRefusal_none hl
          exact ⟨hpos, hbound, hdom, hbase, hep64, hxp64, hdst64, hev64,
            hepcap, hdst, hev, hroom0, hroomx, h32, harm, hsep⟩

/-- **The route's domain excludes the reference's character policy.**  A document
`routePre` admits is not one the reference parser refuses with
`unpairedSurrogate` or `noncharacter`: the exclusion is the reference's own
verdict read from `parseBytes`, so a call the check accepts is not a document the
reference refuses under its policy. -/
theorem routePre_not_policy {l : RouteLayout} {doc : List UInt8}
    (h : routePre l doc) {e : ParseError}
    (hparse : parseBytes Limits.default (ByteString.literal doc) = .error e) :
    ¬ PolicyRefusal e :=
  (h.2.2.1 e hparse).2.2

/-- **Acceptance implies the reference's policy admits the document.**  A
`checkRoute` that accepts cannot be a document the reference refuses with
`unpairedSurrogate` or `noncharacter`; the class the object accepted and the
reference refused is outside the route's domain, and a caller that passed the
check is not in it. -/
theorem checkRoute_ok_not_policy {l : RouteLayout} {doc : List UInt8}
    (h : (checkRoute l doc).isOk = true) :
    ∀ e : ParseError,
      parseBytes Limits.default (ByteString.literal doc) = .error e →
        ¬ PolicyRefusal e :=
  fun e he => routePre_not_policy (routePre_of_checkRoute_ok h) he

/-! ### The post a caller observes -/

/-- What a caller reads off a returning run: the verdict word and the four
cursor slots' bytes, as the record's post reads them.  The semantic content
(acceptance against the reference parser, the event stream's token relation) is
`Sigma_pipeline`'s and not restated here. -/
structure RouteResult where
  verdict : Nat
  nkWord : List UInt8
  nxpWord : List UInt8
  ndstWord : List UInt8
  nevWord : List UInt8
deriving Repr, DecidableEq

/-- The caller-visible projection of the record's post, at the route's arguments. -/
def routeResult (args : List Value) (o : Outcome) : Option RouteResult :=
  match o with
  | .ret (some (.int 64 v)) m =>
      match args with
      | [.ptr _, .int 64 _, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 _, .ptr nk,
         .ptr _, .int 64 _, .ptr nxp, .ptr _, .ptr _, .int 64 _, .ptr ndst,
         .ptr _, .int 64 _, .ptr nev, .ptr _, .int 64 _] =>
          (readBytes m nk 8).bind fun w1 =>
            (readBytes m nxp 8).bind fun w2 =>
              (readBytes m ndst 8).bind fun w3 =>
                (readBytes m nev 8).map fun w4 =>
                  { verdict := v.toNat, nkWord := w1, nxpWord := w2,
                    ndstWord := w3, nevWord := w4 }
      | _ => none
  | _ => none

/-- The route's post: the recorded pipeline's post at the route's arguments and
the wrapper's staging.  This is the consumer side of `routeStaging`. -/
def routePost (l : RouteLayout) (doc : List UInt8) (next : Nat) (o : Outcome) : Prop :=
  pipelineUnitsPost (routeArgs l doc) (stagedMem l doc) next o

/-- **The post's caller-visible projection.**  A run that returns the ABI's
64-bit verdict satisfies the record's post only if its four cursor slots hold the
words this result reads, and its verdict is the two-valued word.  The projection
is a consequence of the post, not a second statement of it. -/
theorem routePost_result {l : RouteLayout} {doc : List UInt8} {next : Nat}
    {verdict : BitVec 64} {m : Mem}
    (h : routePost l doc next (.ret (some (.int 64 verdict)) m)) :
    ∃ (nk' nxp' ndst' nev' : Nat),
      routeResult (routeArgs l doc) (.ret (some (.int 64 verdict)) m) =
        some { verdict := verdict.toNat, nkWord := wordBytes 8 nk',
               nxpWord := wordBytes 8 nxp', ndstWord := wordBytes 8 ndst',
               nevWord := wordBytes 8 nev' } ∧
      (verdict.toNat = 0 ∨ verdict.toNat = 1) := by
  simp only [routePost, pipelineUnitsPost, routeArgs] at h
  obtain ⟨hv, nk', nxp', ndst', nev', ent, ps, out, evs,
    -, -, -, -, -, -, -, hout, hnk, hnxp, -, -, -, -, -, -, -⟩ := h
  simp only [pipelineOutputExtents, routeArgs] at hout
  obtain ⟨-, -, hndst, hnev⟩ := hout
  refine ⟨nk', nxp', ndst', nev', ?_, ?_⟩
  · simp only [routeResult, routeArgs, hnk, hnxp, hndst, hnev,
      Option.bind_some, Option.map_some]
  · rcases hv with hv | hv <;> rw [hv] <;> decide

/-! ### The native entry point, and the bridge that is missing

`pipeline.h`'s symbol is `leanllvm_json_pipeline`; `kernel/json/pipeline.c`
defines it, and `probes/install/ir/json-pipeline.candidate.ll` is the emitted
candidate the pinned body is parsed from.  The declaration below is the symbol at
the ABI's address level — twenty machine words for the twenty arguments, the
pointers as address-sized integers — which is exactly what the object's C
signature passes on this target.  It is **not** a route: a Lean program cannot
supply an address, because `ByteArray`'s data pointer is the runtime's C API
(`lean_sarray_cptr` in `lean.h`) and no term in `Init` or `Std` exposes it. -/
@[extern "leanllvm_json_pipeline"]
opaque nativePipeline (b n sc mk entw ep epcap nk xp xpcap nxp xcarry dst dstcap
  ndst ev evcap nev err arm : USize) : USize

/-- The adapter symbol a Lean caller would need.  A C function under this name
would take the caller's `ByteArray`s, extract their data pointers with the
runtime's own API, stage them into the object's ABI, call
`leanllvm_json_pipeline`, and return the output bytes.  No such function exists
in this tree. -/
def nativeAdapterSymbol : String := "leanllvm_json_route"

/-- **What is missing between a Lean program and the native object**, each with
the evidence that it is missing.  The executable route in `probes/json/route/`
supplies the adapter and the link step outside `lake`; the semantics-to-object
step remains the documented trust boundary. -/
def missingBridgePieces : List String :=
  [ "an FFI adapter: `ByteArray`'s data pointer is the runtime's C API \
(`lean_sarray_cptr` in `lean.h`), and no Lean term exposes it; the adapter must \
take the caller's `ByteArray`s and pass their pointers",
    "a staging copy: the adapter must copy the wrapper's bytes into the object's \
buffers; a native write into a Lean-owned `ByteArray` is outside Lean's semantics, \
and the compiler may share two equal `ByteArray` literals",
    "a link step: `kernel/json/README.md` states that `lake` does not build the \
kernel, and no `extern_lib`, `moreLinkArgs` or JSON `@[extern]` exists in \
`lakefile.toml`; `probes/json/route/build.sh` is the link step, and it is \
outside `lake`",
    "the table initialisation: the native POS8 emitter reads its own `xl_pos8`, so \
the route must call `leanllvm_json_entry_table`; the record's `tab` region is a \
caller buffer the object never reads, and the two tables' identity is the entry \
route's observed one (`tests/json-entry`), not a theorem of this module",
    "the semantics-to-object step: `pipeline_satisfies_at_stage2_of_exitStage2` \
is about the pinned AST and `Mem`, and nothing connects a run of the linked \
object to `pipelineUnitsPost`; that is the compiler/FFI trust boundary \
(`docs/contract.md` row 9)" ]

/-! ### Axiom footprints

Every declaration is choice-free or carries the same carrier the record's proofs
do; the staging construction adds no axiom of its own. -/

/-- info: 'LeanLLVM.Refinement.routeStaging' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms routeStaging

/-- info: 'LeanLLVM.Refinement.checkRoute_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_empty

/-- info: 'LeanLLVM.Refinement.checkRoute_tooLong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_tooLong

/-- info: 'LeanLLVM.Refinement.checkRoute_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_depth

/-- info: 'LeanLLVM.Refinement.checkRoute_tokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_tokens

/-- info: 'LeanLLVM.Refinement.checkRoute_unpairedSurrogate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_unpairedSurrogate

/-- info: 'LeanLLVM.Refinement.checkRoute_noncharacter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_noncharacter

/-- info: 'LeanLLVM.Refinement.routePre_not_policy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms routePre_not_policy

/-- info: 'LeanLLVM.Refinement.checkRoute_ok_not_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkRoute_ok_not_policy

/-- info: 'LeanLLVM.Refinement.documentRefusal_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms documentRefusal_none

/-- info: 'LeanLLVM.Refinement.layoutRefusal_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layoutRefusal_none

/-- info: 'LeanLLVM.Refinement.routePre_of_checkRoute_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routePre_of_checkRoute_ok

/-- info: 'LeanLLVM.Refinement.routeSpecPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms routeSpecPre

/-- info: 'LeanLLVM.Refinement.routePost_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms routePost_result

/-- info: 'LeanLLVM.Refinement.nativePipeline' does not depend on any axioms -/
#guard_msgs in
#print axioms nativePipeline

end LeanLLVM.Refinement
