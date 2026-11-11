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

-- 129 nested arrays exhaust the parser's depth; the ABI carries no depth limit,
-- so the shell refuses it rather than falling through.
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
-- object accepts them (the route check reports the set).
#guard (match parseBytes Limits.default (ByteString.literal "\"\\uD800\"".toUTF8.toList) with
  | .error (.invalid (.unpairedSurrogate _)) => true
  | _ => false)
#guard (match parseBytes Limits.default (ByteString.literal "\"\\uFDD0\"".toUTF8.toList) with
  | .error (.invalid (.noncharacter _)) => true
  | _ => false)
