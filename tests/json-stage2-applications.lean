/-
The §9 regression applications, run through the pinned stage-2 body.

Each check stages the document, its entry stream and its escape list, seeds the
body's own entry state (`EntryState stage2Body (stage2Args …) mem next`), runs
`runFuel (stage2Calls stage2SubCalls) (stage2Budget …) stage2Body`, and reads the
returned memory at the record's observable boundary:

* the verdict word (`0` refusal, `1` acceptance);
* the arena cursor word, and the decoded prefix at the **used** extent;
* the arena bytes at the **reserved** extent, `n + stage2ArenaReserve`, which is
  where presence and the decoder's slack are stated — the two extents are
  separate, and an escaped input reports a used extent shorter than the window
  it reserved;
* the event cursor word and the event bytes, compared with
  `JsonStage2Spec`'s own record encoding (`tagRecord`, `strRecordBytes`,
  `numberRecordBytes`);
* the refusal word on refusal, and that it is untouched on acceptance;
* the document, entry stream and escape list unchanged;
* the reported used extent at most the document's length, and the event extent
  at most one record per input byte.

The body calls the six forwarded helpers through
`stage2Calls stage2SubCalls`, the call environment the walk's obligation names;
the checks are therefore of the real seed and the real dispatch, not of a helper
model in isolation.

**What is checked, and what is not.**  The checked clauses are the boundary's
observable ones: the verdict value and its `0`/`1` range, the two staged cursor
reads, the two reported words and their append bounds, the capacity widths and
the arena reserve, the arena read at the reserved extent and the decoded prefix
at the used extent, the event read, the refusal word and its absence on
acceptance, the document, entry stream and escape list unchanged, and the two
extent bounds.  The clauses not checked here are the `UnchangedOutside` frame
over arbitrary addresses, the seven scratch objects' presence, the seventeen-
object `DisjointRegions` and `dSep`; those are the walk's region obligations and
are not discharged by an executable observation.  Their producer tier is the
remaining work, so this file claims the returning run and the observable
boundary, not the full `stage2Boundary` frame.

| §9 row | evidence here |
|---|---|
| `0`, `null`, `true`, `false` | complete applications |
| `""`, `"abc"`, `"\u0041"` | complete applications; the escaped one is the used/reserved witness |
| `0 `, `null` + 80 spaces | complete applications |
| `["a"]`, `{"a":"b"}` | complete applications; `["a"]` is the nested-string run |
| `[]`, `{}`, `[0]`, `{"a":1}`, `[[0]]` | complete applications |
| empty, whitespace-only, `}`, lone quote, malformed numerics | complete applications |
| near the nesting cap | **branch-level**: the 520-deep run did not finish inside the check's evaluation budget; `openAtCap_last_at_deep_document` / `openAtCap_cont_at_deep_document` are the arm's document regressions |
| 32/64-byte boundaries, escaped and multibyte tails | complete applications |

Branch-level evidence supplements these applications and is not replaced by
them: the per-class regressions live in `JsonStage2Walk*Domain` and are the
documents at which each `HcontArm`/`LastEntryArm` dispatches through the real
arm.  The `#print axioms` block at the end names the ones this file's documents
overlap (`0`, `"01"`, the depth-one delimiters and the closers), with their
footprints.

At least the escaped-string, the long-trailing-whitespace and the nested-string
cases are complete returning runs: the seed, the dispatch and the finalisation
all execute to `.ret` and the postcondition above is read at the returned
memory.  The application checks are `#guard`s over the compiled semantics: a
`by decide` at `4 · 10 ^ 6` heartbeats and a `by rfl` at `150` s each failed to
close one escaped-string case, so the run is executable evidence and no proof
term is claimed for these three.  The branch-level theorems' footprints are
printed below.

Run: `nix develop -c lake env lean tests/json-stage2-applications.lean`.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosersDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain
import LeanLLVM.Refinement.JsonStage2WalkHcontDomain
import LeanLLVM.Refinement.JsonStage2WalkHlastDomain
import LeanLLVM.Refinement.JsonStage2Spec

set_option autoImplicit false
set_option maxRecDepth 200000

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

namespace Stage2Applications

/-! ### The staged memory -/

/-- The document's base.  The entry block reads `%3 - 1` (`%invariant.gep`), so
the byte below the base is staged too. -/
def b : Nat := 0x1000
/-- The entry stream. -/
def ep : Nat := 0x2000
/-- The escape-position list. -/
def xp : Nat := 0x3000
/-- The arena. -/
def dst : Nat := 0x4000
/-- The arena cursor slot. -/
def ndst : Nat := 0x5000
/-- The event stream. -/
def ev : Nat := 0x6000
/-- The event cursor slot. -/
def nev : Nat := 0x7000
/-- The refusal slot. -/
def err : Nat := 0x8000
/-- `%d.i`, the number path's output slot. -/
def dSlot : Nat := 0x9000
/-- `%c.i`, the cursor record: its base at `+0` and its error pointer at `+1112`. -/
def cSlot : Nat := 0xa000
/-- `%ctype.i`. -/
def ctype : Nat := 0xb000
/-- `%cst.i`. -/
def cst : Nat := 0xc000
/-- `%t352.i`. -/
def tok : Nat := 0xd000
/-- `%s`. -/
def sSlot : Nat := 0xe000
/-- `%z`. -/
def zSlot : Nat := 0xf000
/-- `%e`. -/
def eSlot : Nat := 0x10000
/-- The allocator cursor the call is made at, above every staged object. -/
def next : Nat := 0x20000

/-- Four-byte little-endian lanes. -/
def laneWords (ps : List Nat) : List UInt8 :=
  ps.flatMap (fun p => natToBytes p 4)

/-- The log's fields the walk and its helpers read: the event buffer, its cursor
and capacity, the hash state, the arena's base, cursor and capacity. -/
def zStores (mem : Mem) (evcap dstcap : Nat) : Mem :=
  let m := writeBytes mem zSlot (wordBytes 8 ev)
  let m := writeBytes m (zSlot + 8) (wordBytes 8 0)
  let m := writeBytes m (zSlot + 16) (wordBytes 8 evcap)
  let m := writeBytes m (zSlot + 32) (List.replicate 32 (0 : UInt8))
  let m := writeBytes m (zSlot + 40) (wordBytes 8 dst)
  let m := writeBytes m (zSlot + 48) (wordBytes 8 0)
  writeBytes m (zSlot + 56) (wordBytes 8 dstcap)

/-- The caller's staging: the document with its readable tail, the entry and
escape streams, the arena, the event stream, the two cursor slots, the refusal
slot, and the eight appended objects.  The two capacities are the document's own
plus slack, so a run's writes fit the record's staging. -/
def stagedMem (bs : List UInt8) (ps escs : List Nat) : Mem :=
  let dstcap := bs.length + 512
  let evcap := 13 * bs.length + 256
  let m0 : Mem := []
  let m := writeBytes m0 (b - 1) (List.replicate 8 (0 : UInt8))
  let m := writeBytes m b bs
  let m := writeBytes m (b + bs.length) (List.replicate 128 (0 : UInt8))
  let m := writeBytes m ep (laneWords ps)
  let m := writeBytes m xp (laneWords escs)
  let m := writeBytes m dst (List.replicate dstcap (0 : UInt8))
  let m := writeBytes m ev (List.replicate evcap (0 : UInt8))
  let m := writeBytes m ndst (wordBytes 8 0)
  let m := writeBytes m nev (wordBytes 8 0)
  let m := writeBytes m err (wordBytes 8 0)
  let m := writeBytes m dSlot (List.replicate 8 (0 : UInt8))
  let m := writeBytes (writeBytes m cSlot (List.replicate 1120 (0 : UInt8))) cSlot
    (wordBytes 8 b)
  let m := writeBytes m (cSlot + 1112) (wordBytes 8 eSlot)
  let m := writeBytes m ctype (List.replicate 520 (0 : UInt8))
  let m := writeBytes m cst (List.replicate 520 (0 : UInt8))
  let m := writeBytes m tok (List.replicate 24 (0 : UInt8))
  let m := writeBytes m sSlot (List.replicate 120 (0 : UInt8))
  let m := writeBytes m eSlot (List.replicate 24 (0 : UInt8))
  zStores m evcap dstcap

/-- `stage2.h`'s thirteen arguments, then the eight the flattening appends. -/
def stagedArgs (bs : List UInt8) (ps escs : List Nat) : List LeanLLVM.Value :=
  stage2Args
    [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ep,
     .int 64 (BitVec.ofNat 64 ps.length), .ptr xp,
     .int 64 (BitVec.ofNat 64 escs.length), .ptr dst,
     .int 64 (BitVec.ofNat 64 (bs.length + 512)), .ptr ndst, .ptr ev,
     .int 64 (BitVec.ofNat 64 (13 * bs.length + 256)), .ptr nev, .ptr err]
    dSlot cSlot ctype cst tok sSlot zSlot eSlot

/-- The real seed: the body's entry state at the staged thirteen ABI arguments
and their eight appended objects. -/
def seed (bs : List UInt8) (ps escs : List Nat) : State :=
  EntryState stage2Body (stagedArgs bs ps escs) (stagedMem bs ps escs) next

/-- The run at the record's budget, through the pinned body and
`stage2Calls stage2SubCalls`. -/
def runAt (bs : List UInt8) (ps escs : List Nat) : Option Outcome :=
  let a := stagedArgs bs ps escs
  let B := stage2Budget (a.take 13) (stagedMem bs ps escs)
  runFuel (stage2Calls stage2SubCalls) B stage2Body (seed bs ps escs)

/-! ### Expected values -/

/-- A number lexeme's record: `T_NUM` and `strtodSpec`'s eight bytes. -/
def numEvent (d : Decimal) : List UInt8 :=
  numberRecordBytes ((strtodSpec d).toBits)

/-- The decimal `0`'s decomposition. -/
def decZero : Decimal :=
  { neg := false, ip := ByteString.literal [0x30], fr := none, ex := none }

/-- The decimal `1`'s decomposition. -/
def decOne : Decimal :=
  { neg := false, ip := ByteString.literal [0x31], fr := none, ex := none }

/-- What one application asserts at the returned memory. -/
structure Expected where
  /-- The verdict word: `1` accepted, `0` refused. -/
  verdict : Nat
  /-- The used arena extent the cursor slot reports. -/
  used : Nat
  /-- The decoded arena prefix at the used extent. -/
  arena : List UInt8
  /-- The event stream's prefix. -/
  events : List UInt8
  /-- The refusal word (zero on acceptance). -/
  off : Nat
  deriving Repr

/-- The observable postcondition: the returning outcome's verdict, the two
cursor words, the decoded arena at the **used** extent and the arena at the
**reserved** extent, the event prefix, the refusal word, the three inputs
unchanged, and the two extent bounds. -/
def check (bs : List UInt8) (ps escs : List Nat) (e : Expected) : Bool :=
  match runAt bs ps escs with
  | some (.ret (some (.int 64 v)) m) =>
      v = BitVec.ofNat 64 e.verdict &&
        readBytes m ndst 8 = some (wordBytes 8 e.used) &&
        readBytes m dst e.used = some e.arena &&
        readBytes m dst (bs.length + stage2ArenaReserve) =
          some (e.arena ++ List.replicate
            (bs.length + stage2ArenaReserve - e.arena.length) 0) &&
        readBytes m nev 8 = some (wordBytes 8 e.events.length) &&
        readBytes m ev e.events.length = some e.events &&
        readBytes m err 8 = some (wordBytes 8 e.off) &&
        readBytes m b bs.length = some bs &&
        readLanes32 m ep ps.length = some ps &&
        readBytes m xp (4 * escs.length) = some (laneWords escs) &&
        decide (e.used ≤ bs.length) &&
        decide (e.events.length ≤ 13 * bs.length)
  | _ => false

/-- A one-entry document whose entry is at position zero. -/
def one (bs : List UInt8) (escs : List Nat) (e : Expected) : Bool :=
  check bs [0] escs e

/-! ### Scalars and literals

`0`, `null`, `true`, `false`: the scalar/literal dispatch and terminal
execution, at the record's own event tags. -/

#guard one [48] [] ⟨1, 0, [], numEvent decZero, 0⟩
#guard one [110,117,108,108] [] ⟨1, 0, [], tagRecord 10, 0⟩
#guard one [116,114,117,101] [] ⟨1, 0, [], tagRecord 8, 0⟩
#guard one [102,97,108,115,101] [] ⟨1, 0, [], tagRecord 9, 0⟩

/-! ### Strings

`""`, `"abc"`, `"\u0041"`: plain strings are span-addressed in the document and
write nothing to the arena; the escaped string is the **used/reserved**
witness — it reports used extent `1`, decodes `A` into the arena, and the
reserved extent `n + 64` reads back the decoded prefix followed by slack. -/

#guard check [34,34] [0,1] [] ⟨1, 0, [], strRecordBytes false 0 (plainSpan 1), 0⟩
#guard check [34,97,98,99,34] [0,4] []
  ⟨1, 0, [], strRecordBytes false 3 (plainSpan 1), 0⟩
#guard check [34,92,117,48,48,52,49,34] [0,7] [1]
  ⟨1, 1, [65], strRecordBytes false 1 0, 0⟩

/-! ### Trailing whitespace

`0 ` and `null` followed by eighty spaces: valid terminal execution under the
record's budget, with the event stream the literal's or the number's. -/

#guard one [48,32] [] ⟨1, 0, [], numEvent decZero, 0⟩
#guard check ([110,117,108,108] ++ List.replicate 80 32) [0] []
  ⟨1, 0, [], tagRecord 10, 0⟩

/-! ### Containers and nesting

`[]`, `{}`, `[0]`, `{"a":1}`: container transitions and closing delimiters.
`["a"]` and `{"a":"b"}` add positive-depth string paths; `["a"]` is the
**nested-string** complete returning run. -/

#guard check [91,93] [0,1] [] ⟨1, 0, [], tagRecord 3 ++ tagRecord 4, 0⟩
#guard check [123,125] [0,1] [] ⟨1, 0, [], tagRecord 1 ++ tagRecord 2, 0⟩
#guard check [91,48,93] [0,1,2] []
  ⟨1, 0, [], tagRecord 3 ++ numEvent decZero ++ tagRecord 4, 0⟩
#guard check [123,34,97,34,58,49,125] [0,1,3,4,5,6] []
  ⟨1, 0, [], tagRecord 1 ++ strRecordBytes true 1 (plainSpan 2) ++
    numEvent decOne ++ tagRecord 2, 0⟩
#guard check [91,34,97,34,93] [0,1,3,4] []
  ⟨1, 0, [], tagRecord 3 ++ strRecordBytes false 1 (plainSpan 2) ++ tagRecord 4, 0⟩
#guard check [123,34,97,34,58,34,98,34,125] [0,1,3,4,5,7,8] []
  ⟨1, 0, [], tagRecord 1 ++ strRecordBytes true 1 (plainSpan 2) ++
    strRecordBytes false 1 (plainSpan 6) ++ tagRecord 2, 0⟩

/-! ### Refusals

Empty and whitespace-only input, `}`, a lone quote, and the malformed numeric
lexemes: the implemented refusal paths, the verdict word, and the offset the
refusal slot actually holds.  The arena and event stream are untouched, so the
returned memory is the staged one outside the two cursor words and the refusal
slot. -/

#guard check [] [] [] ⟨0, 0, [], [], 0⟩
#guard check (List.replicate 64 32) [] [] ⟨0, 0, [], [], 64⟩
#guard check [125] [0] [] ⟨0, 0, [], [], 0⟩
#guard check [34] [0] [] ⟨0, 0, [], [], 1⟩
#guard check [48,49] [0] [] ⟨0, 0, [], [], 1⟩
#guard check [49,101] [0] [] ⟨0, 0, [], [], 2⟩
#guard check [49,46] [0] [] ⟨0, 0, [], [], 2⟩
#guard check [45] [0] [] ⟨0, 0, [], [], 1⟩
#guard check [43,49] [0] [] ⟨0, 0, [], [], 0⟩

/-! ### The nesting cap

The stack's capacity is `stage2StackExtent = 520`, and the push at depth `520`
is the arm `openAtCap` refuses.  A `520`-deep document is a thousand-entry run
over a sixteen-kilobyte staging; the compiled evaluation of this file including
that case did not finish in `200` s under the `6 GiB` ceiling, so the cap is
evidenced at the branch level by the arm's own document regressions rather than
by an application here.  The same split covers
the reserve: `openAtCap_last_at_deep_document` and
`openAtCap_cont_at_deep_document` dispatch the refusal at a deep document, and
their footprints are printed below.

`[[0]]` keeps a small positive-depth container transition as an application. -/

#guard check [91,91,48,93,93] [0,1,2,3,4] []
  ⟨1, 0, [], tagRecord 3 ++ tagRecord 3 ++ numEvent decZero ++ tagRecord 4 ++ tagRecord 4, 0⟩

/-! ### The 32/64-byte boundaries and escaped/multibyte tails

Plain strings of body lengths `61`, `62`, `63` stage documents of 63, 64 and 65
bytes; the escaped `\u00e9` tail decodes to the two UTF-8 bytes, and the plain
multibyte tail keeps its document bytes and span. -/

#guard check (34 :: List.replicate 61 97 ++ [34]) [0, 62] []
  ⟨1, 0, [], strRecordBytes false 61 (plainSpan 1), 0⟩
#guard check (34 :: List.replicate 62 97 ++ [34]) [0, 63] []
  ⟨1, 0, [], strRecordBytes false 62 (plainSpan 1), 0⟩
#guard check (34 :: List.replicate 63 97 ++ [34]) [0, 64] []
  ⟨1, 0, [], strRecordBytes false 63 (plainSpan 1), 0⟩
#guard check (34 :: List.replicate 60 97 ++ [92,117,48,48,101,57] ++ [34])
  [0, 67] [61] ⟨1, 62, List.replicate 60 97 ++ [0xC3, 0xA9],
    strRecordBytes false 62 0, 0⟩
#guard check (34 :: List.replicate 60 97 ++ [0xC3, 0xA9] ++ [34]) [0, 63] []
  ⟨1, 0, [], strRecordBytes false 62 (plainSpan 1), 0⟩

/-! ### The reference parser's own verdicts

The expected values above are the reference specification's, so the same
documents are read by `parseBytes` and compared: an accepted document decodes to
the value its bytes spell, and a refused one is refused.

**The two refusal policies are not the same policy, and this relation is a
mapping rather than an equality.**

* The reference parser reports the **offending token's start**: `rejectPos` reads
  the `pos` field of the `Reject` constructor, and `.byteOrderMark` is the one
  constructor with no position.
* The emitted body reports the **position its refusal path stopped at**, in the
  word it stores at `%e + 8`: the number scan's stop from `num_fast_el1`
  (`numLexScan lexeme).1`, relative to the token), the string body's
  body-relative offset (plus the token position the walk adds), or the token
  start on the generic and structural refusal paths (`if.then418.i` stores
  `%idxprom.i`).

The measured pairs, all at UTF-8-valid ASCII input:

| input | parser `rejectPos` | body word | mapping on this path |
|---|---|---|---|
| empty | `0` | `0` | equal (`unexpectedEnd`) |
| 64 spaces | `64` | `64` | equal (`unexpectedEnd`) |
| `}` | `0` | `0` | equal (generic/structural) |
| `+1` | `0` | `0` | equal (generic/structural; the one-byte-token `+1` rule has this exception) |
| lone quote | `0` | `1` | token start + 1 (string body) |
| `-` | `0` | `1` | token start + `numLexScan` stop |
| `01` | `0` | `1` | token start + `numLexScan` stop |
| `1e` | `0` | `2` | token start + `numLexScan` stop |
| `1.` | `0` | `2` | token start + `numLexScan` stop |

So `refusalOffset_walk`, which identifies the walk's word with `rejectPos`, is
**false** at the malformed tokens; it holds at the empty, whitespace-only and `}`
controls.  The applications above assert the body's actual word, as §9 asks, and
the guards below assert each side separately and the mapping row by row.  The
semantic relation is therefore **not** instantiated at the malformed tokens under
the identity form; stating it as this mapping is the repair, and it is recorded
here rather than derived as an equality. -/

/-- The emitted body's refusal word, read from the returning outcome. -/
def bodyErr (bs : List UInt8) (ps escs : List Nat) : Nat :=
  match runAt bs ps escs with
  | some (.ret (some (.int 64 _)) m) =>
      match readBytes m err 8 with
      | some w => bytesToNat w
      | none => 0
  | _ => 0

/-- The reference parser accepts the document and decodes the expected value. -/
def refAccept (bs : List UInt8) (v : LeanLLVM.JSON.Value) : Bool :=
  match parseBytes Limits.default (ByteString.literal bs) with
  | .ok t => decide (t.input = ByteString.literal bs ∧ decodeTape t = some v)
  | _ => false

/-- The reference parser refuses the document. -/
def refRefuses (bs : List UInt8) : Bool :=
  match parseBytes Limits.default (ByteString.literal bs) with
  | .error (.invalid _) => true
  | _ => false

/-- The reference parser's refusal position, where it has one. -/
def refRefuseAt (bs : List UInt8) (off : Nat) : Bool :=
  match parseBytes Limits.default (ByteString.literal bs) with
  | .error (.invalid r) => rejectPos r = some off
  | _ => false

/-- The JSON number token for one ASCII digit. -/
def numLex (c : Nat) : ByteString := ByteString.literal [UInt8.ofNat c]

#guard refAccept [48] (.number (numLex 48))
#guard refAccept [110,117,108,108] .null
#guard refAccept [116,114,117,101] (.bool true)
#guard refAccept [102,97,108,115,101] (.bool false)
#guard refAccept [34,34] (.string [])
#guard refAccept [34,97,98,99,34] (.string [97, 98, 99])
#guard refAccept [34,92,117,48,48,52,49,34] (.string [65])
#guard refAccept [48,32] (.number (numLex 48))
#guard refAccept ([110,117,108,108] ++ List.replicate 80 32) .null
#guard refAccept [91,93] (.array [])
#guard refAccept [123,125] (.object [])
#guard refAccept [91,48,93] (.array [.number (numLex 48)])
#guard refAccept [123,34,97,34,58,49,125] (.object [([97], .number (numLex 49))])
#guard refAccept [91,34,97,34,93] (.array [.string [97]])
#guard refAccept [123,34,97,34,58,34,98,34,125] (.object [([97], .string [98])])
#guard refAccept [91,91,48,93,93] (.array [.array [.number (numLex 48)]])
#guard refAccept (34 :: List.replicate 60 97 ++ [92,117,48,48,101,57] ++ [34])
  (.string (List.replicate 60 97 ++ [233]))
-- The equal controls: the two policies coincide where the refusal is the
-- document's end or a generic/structural token start.
#guard refRefuseAt [] 0
#guard bodyErr [] [] [] = 0
#guard refRefuseAt (List.replicate 64 32) 64
#guard bodyErr (List.replicate 64 32) [] [] = 64
#guard refRefuseAt [125] 0
#guard bodyErr [125] [0] [] = 0
#guard refRefuseAt [43,49] 0
#guard bodyErr [43,49] [0] [] = 0

-- The string body's path: the parser names the quote's start, the body the
-- position after it.
#guard refRefuseAt [34] 0
#guard refRefuses [34]
#guard bodyErr [34] [0] [] = 1

-- The number scan's path: the parser names the token's start, the body the
-- scan's stop (`numLexScan`'s first component).
#guard refRefuseAt [45] 0
#guard bodyErr [45] [0] [] = (numLexScan [45]).1
#guard refRefuseAt [48,49] 0
#guard bodyErr [48,49] [0] [] = (numLexScan [48,49]).1
#guard refRefuseAt [49,101] 0
#guard bodyErr [49,101] [0] [] = (numLexScan [49,101]).1
#guard refRefuseAt [49,46] 0
#guard bodyErr [49,46] [0] [] = (numLexScan [49,46]).1

/-! ### The branch-level supplements

These are the domain regressions whose documents this file also runs.  They are
not replaced by the applications: each is a class's arm dispatched by the real
`HcontArm`/`LastEntryArm` at a staged document. -/

#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_domain
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_regression
#print axioms LeanLLVM.Refinement.WalkScope.commaAboveZero_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.colonAboveZero_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeBracketMerge_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeBraceMerge_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.openAtCap_last_at_deep_document
#print axioms LeanLLVM.Refinement.WalkScope.openAtCap_cont_at_deep_document

-- The executable route's own footprint: both are definitions over the model.
-- Their footprint is `[propext, Quot.sound]` — no `Classical.choice` and no
-- `sorryAx` — and the check itself is the compiled `#guard` above, not a
-- kernel-reduced proof term.
#print axioms Stage2Applications.runAt
#print axioms Stage2Applications.check

end Stage2Applications
