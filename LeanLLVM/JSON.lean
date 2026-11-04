/-
The JSON subtree's entrypoint: the RFC 8259 grammar and character policy as a
relation over bytes, the scanners that reflect it, the tape and its decoder, the
reference parser, and the correctness theorems that relate the three.

The import order is the dependency order, and it is the reason the semantics
cannot be defined in terms of the parser: `Spec` mentions no scanner, tape or
limit, `Tape` mentions no parser, and only `Correct` mentions both.  `ScanBlock`
is the block layer — the per-byte mask transition and the block operation that
reports it — and it reaches `Bytes` alone, so the parser's proof chain never
sees it.  The block model sits above both chains and neither chain imports it:
`ScanBody` is the carry and the byte rule, `ScanWindow` the one window fold and
its masks, `ScanString` the window-driven scan and the tail, and `ScanBlocks`
the whole-scan statement relating that scan to the parser's own string scanner.
`Parse.lean` imports none of them.  `ByteString` is the carrier: it is
`ByteArray`, and it holds the list-shaped operations and lemmas the proof layer
writes against.  `Bytes` abbreviates it, so every statement in this subtree is
written over the array, not over a list; `ByteString` imports nothing and
`Bytes` is its first user, so the carrier introduces no cycle.
-/
import LeanLLVM.JSON.Bytes
import LeanLLVM.JSON.Utf8
import LeanLLVM.JSON.Spec
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Tape
import LeanLLVM.JSON.Parse
import LeanLLVM.JSON.TapeCorrect
import LeanLLVM.JSON.Correct
import LeanLLVM.JSON.ScanBlock
import LeanLLVM.JSON.ScanBody
import LeanLLVM.JSON.ScanWindow
import LeanLLVM.JSON.ScanString
import LeanLLVM.JSON.ScanBlocks
