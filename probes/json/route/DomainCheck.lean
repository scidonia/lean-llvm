/-
The library shell's domain checks, elaborated from source:

  nix develop -c bash probes/install/lake-locked.sh env lean \
    probes/json/route/DomainCheck.lean

`documentRefusal` and `layoutRefusal` are the two halves of `checkRoute`; these
guards exercise each refusal the record's domain requires, and one accepted
layout, so a shell that stopped refusing (or stopped accepting) is a red here.
-/
import LeanLLVM.JsonCallRoute

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement

/-- A concrete layout whose sixteen regions are pairwise separate. -/
def sampleLayout : RouteLayout :=
  { base := 100, tab := 1000, sc := 20000, mkSlot := 21000, entw := 22000,
    ep := 10000, nk := 23000, xp := 24000, nxp := 25000, xcarry := 26000,
    dst := 30000, ndst := 40000, ev := 50000, nev := 60000, err := 61000,
    epcap := 73, xpcap := 72, dstcap := 4096, evcap := 4096, arm := 2,
    nxp0 := 0, ndst0 := 0, nev0 := 0 }

-- The empty document is refused by its own reason.
#guard documentRefusal [] = some .emptyInput
#guard (checkRoute sampleLayout []).isOk = false

-- One byte over the input bound is refused with the bound.
#guard documentRefusal (List.replicate 1048577 (0 : UInt8)) =
  some (.inputTooLong 1048576)

-- The depth boundary's two sides.  128 nested arrays are inside the reference's
-- bound (`Limits.default.maxDepth`), so the reference accepts them and the shell
-- does not refuse them; 129 exhaust them, and because the ABI carries no depth
-- limit the shell refuses that class rather than falling through to the object.
#guard match parseBytes Limits.default
    (ByteString.literal (List.replicate 128 (0x5B : UInt8) ++
      List.replicate 128 (0x5D : UInt8))) with
  | .ok _ => true
  | .error _ => false
#guard documentRefusal (List.replicate 128 (0x5B : UInt8) ++
    List.replicate 128 (0x5D : UInt8)) = none
#guard parseBytes Limits.default
    (ByteString.literal (List.replicate 129 (0x5B : UInt8) ++
      List.replicate 129 (0x5D : UInt8))) = .error .depthExceeded
#guard documentRefusal (List.replicate 129 (0x5B : UInt8) ++
    List.replicate 129 (0x5D : UInt8)) = some .depthExceeded

-- A well-formed document at a separated layout is accepted.
#guard (checkRoute sampleLayout "{}".toUTF8.toList).isOk = true
#guard (checkRoute sampleLayout "[1,2]".toUTF8.toList).isOk = true

-- The layout checks: a base below three is refused, a reserved arm bit is
-- refused, and an under-sized entry stream is refused at its required size.
#guard layoutRefusal { sampleLayout with base := 2 } "{}".toUTF8.toList =
  some (.noPrefixRoom 2)
#guard layoutRefusal { sampleLayout with arm := 8 } "{}".toUTF8.toList =
  some (.armReserved 8)
#guard layoutRefusal { sampleLayout with epcap := 10 } "{}".toUTF8.toList =
  some (.entryCapacity 73 10)
#guard layoutRefusal { sampleLayout with dstcap := 10 } "{}".toUTF8.toList =
  some (.arenaCapacity 66 10)
#guard layoutRefusal { sampleLayout with evcap := 10 } "{}".toUTF8.toList =
  some (.eventCapacity 26 10)
-- an overlapping pair of regions is refused
#guard layoutRefusal { sampleLayout with mkSlot := 10000 } "{}".toUTF8.toList =
  some .overlappingRegions

-- The divergent corpus rows are the parser's policy refusals: a lone surrogate
-- escape and a noncharacter are RFC texts the reference refuses, and the native
-- object accepts them.  The route refuses them with the reference's reason, so
-- the class is pinned here: each row carries the document's bytes, exactly as
-- `tests/json/corpus/<name>` holds them, and the refusal `documentRefusal`
-- reports.  `check.sh` asserts the executable route's refusals against the same
-- fourteen names.

/-- The reference's policy class, as the corpus names it: the document's bytes
and the refusal the route must report for them. -/
def policyRows : List (String × List UInt8 × RouteRefusal) :=
  [ ("lone-dead.json", [0x22, 0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22],
      .unpairedSurrogate 1),
    ("lone-d800.json", [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22],
      .unpairedSurrogate 1),
    ("lone-dc00.json", [0x22, 0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x22],
      .unpairedSurrogate 1),
    ("double-high.json",
      [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x5C, 0x75, 0x44, 0x38, 0x30,
        0x30, 0x22], .unpairedSurrogate 1),
    ("high-char.json", [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x61, 0x22],
      .unpairedSurrogate 1),
    ("reversed-pair.json",
      [0x22, 0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x5C, 0x75, 0x44, 0x38, 0x30,
        0x30, 0x22], .unpairedSurrogate 1),
    ("nc-fdd0.json", [0x22, 0x5C, 0x75, 0x46, 0x44, 0x44, 0x30, 0x22],
      .noncharacter 1),
    ("nc-fffe.json", [0x22, 0x5C, 0x75, 0x46, 0x46, 0x46, 0x45, 0x22],
      .noncharacter 1),
    ("nc-ffff.json", [0x22, 0x5C, 0x75, 0x46, 0x46, 0x46, 0x46, 0x22],
      .noncharacter 1),
    ("nc-pair-max.json",
      [0x22, 0x5C, 0x75, 0x44, 0x42, 0x46, 0x46, 0x5C, 0x75, 0x44, 0x46, 0x46,
        0x46, 0x22], .noncharacter 1),
    ("nc-raw-fdd0.json", [0x22, 0xEF, 0xB7, 0x90, 0x22], .noncharacter 1),
    ("nc-raw-fffe.json", [0x22, 0xEF, 0xBF, 0xBE, 0x22], .noncharacter 1),
    ("nc-raw-10ffff.json", [0x22, 0xF4, 0x8F, 0xBF, 0xBF, 0x22], .noncharacter 1),
    ("nc-raw-1fffe.json", [0x22, 0xF0, 0x9F, 0xBF, 0xBE, 0x22], .noncharacter 1) ]

/-- `checkRoute` refuses `doc` with exactly `r`. -/
def refusedWith (l : RouteLayout) (doc : List UInt8) (r : RouteRefusal) : Bool :=
  match checkRoute l doc with
  | .error r' => r' == r
  | .ok _ => false

/-- The reference parser itself names exactly `r`'s reason and byte. -/
def referenceRefusalIs (doc : List UInt8) (r : RouteRefusal) : Bool :=
  match parseBytes Limits.default (ByteString.literal doc), r with
  | .error (.invalid (.unpairedSurrogate k)), .unpairedSurrogate k' => k == k'
  | .error (.invalid (.noncharacter k)), .noncharacter k' => k == k'
  | _, _ => false

-- The class is fourteen rows, every one refused with its reason and byte, and
-- the reference parser's own verdict agrees — the refusal is the reference's,
-- not a blanket rule.
#guard policyRows.length = 14
#guard policyRows.all (fun (_, doc, r) => documentRefusal doc == some r)
#guard policyRows.all (fun (_, doc, r) => refusedWith sampleLayout doc r)
#guard policyRows.all (fun (_, doc, r) => referenceRefusalIs doc r)

-- Control for the detector: a document the reference accepts is not refused
-- with any policy reason, so the guards above distinguish the class.
#guard policyRows.all (fun (_, _, r) =>
  documentRefusal "{}".toUTF8.toList != some r ∧
  !refusedWith sampleLayout "{}".toUTF8.toList r)
