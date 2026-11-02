/-
The JSON subtree's entrypoint: the RFC 8259 grammar and character policy as a
relation over bytes, the scanners that reflect it, the tape and its decoder, the
reference parser, and the correctness theorems that relate the three.

The import order is the dependency order, and it is the reason the semantics
cannot be defined in terms of the parser: `Spec` mentions no scanner, tape or
limit, `Tape` mentions no parser, and only `Correct` mentions both.
-/
import LeanLLVM.JSON.Bytes
import LeanLLVM.JSON.Utf8
import LeanLLVM.JSON.Spec
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Tape
import LeanLLVM.JSON.Parse
import LeanLLVM.JSON.TapeCorrect
import LeanLLVM.JSON.Correct
