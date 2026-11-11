/-
The library shell's domain checks, elaborated from source:

  nix develop -c bash probes/install/lake-locked.sh env lean \
    probes/json/route/DomainCheck.lean

`documentDecision` is the domain decision and `checkRoute` is the shell around
it: the document first, and the caller's layout only for a document the pipeline
will answer.  These guards exercise each admission clause and both fallback
outcomes, so a shell that stopped admitting, stopped falling back, or answered a
document on the wrong side is a red here.

The three outcomes are distinct: `admitted` is the fast path, `refused` is the
fallback's refusal with the reference's reason and byte, and `fallback` is the
fallback's acceptance with the tape it accepted.
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

-- The empty document is outside the domain, and the fallback answers it with
-- the reference's own refusal.
#guard decide (documentDecision [] = .refused (.invalid (.unexpectedEnd 0)))
#guard (checkRoute sampleLayout []).isOk = true

-- One byte over the input bound is outside the domain; the reference's answer
-- is its length refusal.
#guard decide (documentDecision (List.replicate 1048577 (0 : UInt8)) = .refused .inputTooLong)

-- The depth boundary's two sides.  128 nested arrays are inside the reference's
-- bound (`Limits.default.maxDepth`) and inside the admission predicate's opener
-- bound, so the pipeline answers them; 129 exhaust them, so the fallback answers
-- with the reference's own `depthExceeded`.
#guard decide (documentDecision (List.replicate 128 (0x5B : UInt8) ++
    List.replicate 128 (0x5D : UInt8)) = .admitted)
#guard decide (documentDecision (List.replicate 129 (0x5B : UInt8) ++
    List.replicate 129 (0x5D : UInt8)) = .refused .depthExceeded)
#guard match checkRoute sampleLayout (List.replicate 129 (0x5B : UInt8) ++
    List.replicate 129 (0x5D : UInt8)) with
  | .ok (.refused .depthExceeded) => true
  | _ => false

-- A well-formed document at a separated layout is admitted and the pipeline
-- answers it.
#guard decide (documentDecision "{}".toUTF8.toList = .admitted)
#guard decide (documentDecision "[1,2]".toUTF8.toList = .admitted)
#guard match checkRoute sampleLayout "{}".toUTF8.toList with
  | .ok .admitted => true
  | _ => false
#guard match checkRoute sampleLayout "[1,2]".toUTF8.toList with
  | .ok .admitted => true
  | _ => false

-- The depth clause is an opener *count*, so it is conservative: this document
-- is balanced and the reference accepts it, but it carries 129 opener bytes, so
-- `admission` does not admit it and the fallback answers it with the tape the
-- reference accepted.  The clause's conservatism is a narrowing of the domain,
-- never a wrong answer.
def openerRichDoc : List UInt8 :=
  "\"".toUTF8.toList ++ List.replicate 129 (0x5B : UInt8) ++ "\"".toUTF8.toList

#guard (match parseBytes Limits.default (ByteString.literal openerRichDoc) with
  | .ok _ => true
  | .error _ => false)
#guard match documentDecision openerRichDoc with
  | .fallback t => decide (decodeTape t).isSome
  | _ => false

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

-- A layout failure is a caller error, and it is reported only when the document
-- is admitted: a document the fallback answers is never staged, so its layout is
-- not read.
#guard match checkRoute { sampleLayout with base := 2 } "{}".toUTF8.toList with
  | .error (.noPrefixRoom 2) => true
  | _ => false
#guard match checkRoute { sampleLayout with base := 2 }
    (List.replicate 129 (0x5B : UInt8) ++ List.replicate 129 (0x5D : UInt8)) with
  | .ok (.refused .depthExceeded) => true
  | _ => false

-- The divergent corpus rows are the parser's policy refusals: a lone surrogate
-- escape and a noncharacter are RFC texts the reference refuses, and the native
-- object accepts them.  The route's fallback refuses them with the reference's
-- reason, so the class is pinned here: each row carries the document's bytes,
-- exactly as `tests/json/corpus/<name>` holds them, and the decision the shell
-- reports.  `check.sh` asserts the executable route's answers against the same
-- fourteen names.

/-- The reference's policy class, as the corpus names it: the document's bytes
and the fallback's refusal for them. -/
def policyRows : List (String × List UInt8 × ParseError) :=
  [ ("lone-dead.json", [0x22, 0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22],
      .invalid (.unpairedSurrogate 1)),
    ("lone-d800.json", [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22],
      .invalid (.unpairedSurrogate 1)),
    ("lone-dc00.json", [0x22, 0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x22],
      .invalid (.unpairedSurrogate 1)),
    ("double-high.json",
      [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x5C, 0x75, 0x44, 0x38, 0x30,
        0x30, 0x22], .invalid (.unpairedSurrogate 1)),
    ("high-char.json", [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x61, 0x22],
      .invalid (.unpairedSurrogate 1)),
    ("reversed-pair.json",
      [0x22, 0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x5C, 0x75, 0x44, 0x38, 0x30,
        0x30, 0x22], .invalid (.unpairedSurrogate 1)),
    ("nc-fdd0.json", [0x22, 0x5C, 0x75, 0x46, 0x44, 0x44, 0x30, 0x22],
      .invalid (.noncharacter 1)),
    ("nc-fffe.json", [0x22, 0x5C, 0x75, 0x46, 0x46, 0x46, 0x45, 0x22],
      .invalid (.noncharacter 1)),
    ("nc-ffff.json", [0x22, 0x5C, 0x75, 0x46, 0x46, 0x46, 0x46, 0x22],
      .invalid (.noncharacter 1)),
    ("nc-pair-max.json",
      [0x22, 0x5C, 0x75, 0x44, 0x42, 0x46, 0x46, 0x5C, 0x75, 0x44, 0x46, 0x46,
        0x46, 0x22], .invalid (.noncharacter 1)),
    ("nc-raw-fdd0.json", [0x22, 0xEF, 0xB7, 0x90, 0x22],
      .invalid (.noncharacter 1)),
    ("nc-raw-fffe.json", [0x22, 0xEF, 0xBF, 0xBE, 0x22],
      .invalid (.noncharacter 1)),
    ("nc-raw-10ffff.json", [0x22, 0xF4, 0x8F, 0xBF, 0xBF, 0x22],
      .invalid (.noncharacter 1)),
    ("nc-raw-1fffe.json", [0x22, 0xF0, 0x9F, 0xBF, 0xBE, 0x22],
      .invalid (.noncharacter 1)) ]

/-- The shell's decision is exactly `r`'s refusal for `doc`. -/
def refusedWith (doc : List UInt8) (e : ParseError) : Bool :=
  decide (documentDecision doc = .refused e)

-- The class is fourteen rows, every one outside the domain and refused with the
-- reference's own reason and byte.
#guard policyRows.length = 14
#guard policyRows.all (fun (_, doc, e) => refusedWith doc e)

-- Control for the detector: a document the shell admits is not refused with any
-- policy reason, so the guards above distinguish the class.
#guard policyRows.all (fun (_, _, e) => !refusedWith "{}".toUTF8.toList e)
