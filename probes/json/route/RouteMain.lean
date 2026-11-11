/-
The JSON pipeline's call route: a standalone Lean program that stages the
document the record demands, calls `leanllvm_json_pipeline` through the C
adapter in `shim.c`, and prints what the caller observes.

It is standalone because the kernel is outside Lake: `kernel/json/README.md`
says "`lake` does not build the kernel: it is a C unit of the identity, route
and bench scripts, not of the Lean library."  `build.sh` is the link step, in
the shape `probes/app/build.sh` uses for the comma-mask seam.

The staging is `LeanLLVM.JsonCallRoute.stagedStore`'s shape, in bytes: the
window is `[0,0,0] ++ doc ++ zero padding ++ 32` readable tail bytes, the table
is initialised by `leanllvm_json_entry_table`, and the four growing buffers are
sized at the record's capacities.  The shell refuses the two documents it can
recognise without the reference parser — the empty document and one over the
input bound — with the reason on stderr and exit 2.  The parser's depth and
token exclusions belong to `LeanLLVM.JsonCallRoute.checkRoute`, which needs the
reference parser and so is checked by `DomainCheck.lean` under `lake env lean`.
-/

/-- The adapter: it copies the caller's `ByteArray`s into the object's ABI,
calls `leanllvm_json_pipeline`, and returns the result bytes. -/
@[extern "leanllvm_json_route"]
opaque route (window : ByteArray) (n : UInt64)
  (sc mkSlot entw : ByteArray) (ep : ByteArray) (epcap : UInt64) (nk : ByteArray)
  (xp : ByteArray) (xpcap : UInt64) (nxp xcarry dst : ByteArray)
  (dstcap : UInt64) (ndst : ByteArray) (ev : ByteArray) (evcap : UInt64)
  (nev err : ByteArray) (arm : UInt64) : ByteArray

/-- Fills the caller's 8 KiB from the unit's own POS8 table, initialising it. -/
@[extern "leanllvm_json_route_table"]
opaque entryTable (dst : ByteArray) : UInt64

def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0 : UInt8))

def blocks (n : Nat) : Nat := (n + 63) / 64

def usage : String := "usage: leanllvm-json-route --doc <file>"

def hexByte (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length == 1 then "0" ++ s else s

def hex (bs : ByteArray) : String :=
  String.join (bs.toList.map hexByte)

def be64 (bs : ByteArray) (i : Nat) : Nat :=
  -- little-endian word at byte offset `i`
  let get (k : Nat) := (bs.toList.getD (i + k) 0).toNat
  get 0 + 256 * get 1 + 65536 * get 2 + 16777216 * get 3 +
    4294967296 * (get 4 + 256 * get 5 + 65536 * get 6 + 16777216 * get 7)

def run (path : String) : IO UInt32 := do
  let doc ← try
      IO.FS.readBinFile path
    catch e =>
      IO.eprintln s!"route: cannot read '{path}': {e}"
      return 2
  let n := doc.size
  if n = 0 then
    IO.eprintln "refused: empty input: the pipeline record's domain requires a non-empty document"
    return 2
  if 1048576 < n then
    IO.eprintln s!"refused: input too long: the record's bound is 1048576 bytes, the document is {n}"
    return 2
  let nb := blocks n
  let epcap := 64 * nb + 9
  let xpcap := 64 * nb + 8
  let dstcap := n + 64
  let evcap := 13 * n + 128
  let window := (zeros 3).append doc |>.append (zeros (64 * nb - n)) |>.append (zeros 32)
  let tab := zeros 8192
  -- the initialiser's result is used so a pure-call DCE cannot drop it
  if entryTable tab = 0 then
    IO.eprintln "route: the POS8 table initialiser failed"
    return 2
  let result := route window (UInt64.ofNat n)
    (zeros 24) (zeros 48) (zeros 8)
    (zeros (4 * epcap)) (UInt64.ofNat epcap) (zeros 8)
    (zeros (4 * xpcap)) (UInt64.ofNat xpcap) (zeros 8) (zeros 16)
    (zeros dstcap) (UInt64.ofNat dstcap) (zeros 8)
    (zeros evcap) (UInt64.ofNat evcap) (zeros 8) (zeros 8) 2
  let verdict := be64 result 0
  let nk := be64 result 8
  let nxp := be64 result 16
  let ndst := be64 result 24
  let nev := be64 result 32
  let err := be64 result 40
  IO.println s!"verdict={verdict} nk={nk} nxp={nxp} ndst={ndst} nev={nev} err={err}"
  let arena := ByteArray.mk (Array.mk ((result.toList.drop 48).take ndst))
  let events := ByteArray.mk (Array.mk ((result.toList.drop (48 + ndst)).take nev))
  IO.println s!"arena={hex arena}"
  IO.println s!"events={hex events}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--doc", path] => run path
  | _ =>
      IO.eprintln usage
      return 1
