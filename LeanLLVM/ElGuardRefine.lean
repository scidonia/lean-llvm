/-
Tier 2's guard, stated from the arithmetic `num_el_el1` performs, beside
`roundMag`'s decision at the same input.

`kernel/json/stage2.c`'s `num_el_el1` decides a decimal's magnitude from the
high 64 bits of `W * hi`, where `W = w << clz w` is the normalised mantissa and
`hi : lo` is the 128-bit significand of `10 ^ q` from
`kernel/json/measured/epow_table.h`.  `el_pack` shifts that high half by
`10 + ub` to a 53-bit significand and adds one when the dropped part `hp` is
above the half point `hh = 2 ^ (9 + ub)`; when `hp` is one of the three values
`hh - 2`, `hh - 1`, `hh`, a carry out of the *low* half can still move the
decision, so those three take `el_exact`, which reads the low words `Alo`, `L`
and the high word of `W * lo`.

This module is the statement.  It defines the emitted decision
(`elTier2Code`), the exact value in `roundMag`'s ticks (`valueTicks`) and the
obligation that the first is the second (`ElGuardRefinesOn`).  It proves that
the emitted slice test is the three-value window (`inWindow_iff`), that outside
that window no discarded bit can move the decision (`rem_lt_half`,
`half_le_rem`), and that everything the guard cannot see is worth less than one
unit and a sixty-fourth (`discarded_lt`).

It does not prove the obligation.  Nothing here relates `roundMag`'s
significand to the emitted slice: that is a tick-level identity between
`valueTicks`'s `(P, d)`, the binade's `ulp` and the product's remainder, and it
is absent from the tree.  `#eval` at the end reproduces the emitted kernel's own
output on the boundary witnesses, so the definitions are the emitted test
rather than a paraphrase of it.
-/
import LeanLLVM.JSON.Strtod

set_option autoImplicit false

namespace LeanLLVM.ElGuardRefine

open LeanLLVM.JSON

/-! ### The table

`10 ^ q = (hi * 2 ^ 64 + lo + f) * 2 ^ e` with `0 ≤ f < 1`: `f = 0` for
`q ≥ 0`, where the significand is the exact power of five, and `f > 0` only for
`q < 0`, where it is truncated.  The rows are `epow_table.h` entry for entry. -/

/-- One row: the normalised 128-bit significand of `10 ^ q` and its exponent. -/
structure EPow where
  /-- The high word, in `[2 ^ 63, 2 ^ 64)`. -/
  hi : Nat
  /-- The low word. -/
  lo : Nat
  /-- The exponent: `10 ^ q = (hi * 2 ^ 64 + lo + f) * 2 ^ e`. -/
  e : Int
deriving Repr, DecidableEq, Inhabited

/-- `EPOW` of `epow_table.h`, `q = -45 .. 45`. -/
def epow : Array EPow := #[
  ⟨13164036458569648337, 4422670725869800738, -277⟩,  -- 10^-45
  ⟨16455045573212060421, 10140024425764638826, -274⟩,  -- 10^-44
  ⟨10284403483257537763, 8643358275316593218, -270⟩,  -- 10^-43
  ⟨12855504354071922204, 6192511825718353619, -267⟩,  -- 10^-42
  ⟨16069380442589902755, 7740639782147942024, -264⟩,  -- 10^-41
  ⟨10043362776618689222, 2532056854628769813, -260⟩,  -- 10^-40
  ⟨12554203470773361527, 12388443105140738074, -257⟩,  -- 10^-39
  ⟨15692754338466701909, 10873867862998534689, -254⟩,  -- 10^-38
  ⟨9807971461541688693, 9102010423587778132, -250⟩,  -- 10^-37
  ⟨12259964326927110866, 15989199047912110569, -247⟩,  -- 10^-36
  ⟨15324955408658888583, 10763126773035362404, -244⟩,  -- 10^-35
  ⟨9578097130411805364, 13644483260788183358, -240⟩,  -- 10^-34
  ⟨11972621413014756705, 17055604075985229198, -237⟩,  -- 10^-33
  ⟨14965776766268445882, 7484447039699372786, -234⟩,  -- 10^-32
  ⟨9353610478917778676, 9289465418239495895, -230⟩,  -- 10^-31
  ⟨11692013098647223345, 11611831772799369869, -227⟩,  -- 10^-30
  ⟨14615016373309029182, 679731660717048624, -224⟩,  -- 10^-29
  ⟨18268770466636286477, 10073036612751086588, -221⟩,  -- 10^-28
  ⟨11417981541647679048, 8601490892183123069, -217⟩,  -- 10^-27
  ⟨14272476927059598810, 10751863615228903837, -214⟩,  -- 10^-26
  ⟨17840596158824498513, 4216457482181353988, -211⟩,  -- 10^-25
  ⟨11150372599265311570, 14164500972431816002, -207⟩,  -- 10^-24
  ⟨13937965749081639463, 8482254178684994195, -204⟩,  -- 10^-23
  ⟨17422457186352049329, 5991131704928854840, -201⟩,  -- 10^-22
  ⟨10889035741470030830, 15273672361649004035, -197⟩,  -- 10^-21
  ⟨13611294676837538538, 9868718415206479236, -194⟩,  -- 10^-20
  ⟨17014118346046923173, 3112525982153323237, -191⟩,  -- 10^-19
  ⟨10633823966279326983, 4251171748059520975, -187⟩,  -- 10^-18
  ⟨13292279957849158729, 702278666647013314, -184⟩,  -- 10^-17
  ⟨16615349947311448411, 5489534351736154547, -181⟩,  -- 10^-16
  ⟨10384593717069655257, 1125115960621402640, -177⟩,  -- 10^-15
  ⟨12980742146337069071, 6018080969204141204, -174⟩,  -- 10^-14
  ⟨16225927682921336339, 2910915193077788601, -171⟩,  -- 10^-13
  ⟨10141204801825835211, 17960223060169475539, -167⟩,  -- 10^-12
  ⟨12676506002282294014, 17838592806784456520, -164⟩,  -- 10^-11
  ⟨15845632502852867518, 13074868971625794843, -161⟩,  -- 10^-10
  ⟨9903520314283042199, 3560107088838733872, -157⟩,  -- 10^-9
  ⟨12379400392853802748, 18285191916330581053, -154⟩,  -- 10^-8
  ⟨15474250491067253436, 4409745821703674700, -151⟩,  -- 10^-7
  ⟨9671406556917033397, 11979463175419572495, -147⟩,  -- 10^-6
  ⟨12089258196146291747, 1139270913992301907, -144⟩,  -- 10^-5
  ⟨15111572745182864683, 15259146697772541096, -141⟩,  -- 10^-4
  ⟨9444732965739290427, 7231123676894144233, -137⟩,  -- 10^-3
  ⟨11805916207174113034, 4427218577690292387, -134⟩,  -- 10^-2
  ⟨14757395258967641292, 14757395258967641292, -131⟩,  -- 10^-1
  ⟨9223372036854775808, 0, -127⟩,  -- 10^0
  ⟨11529215046068469760, 0, -124⟩,  -- 10^1
  ⟨14411518807585587200, 0, -121⟩,  -- 10^2
  ⟨18014398509481984000, 0, -118⟩,  -- 10^3
  ⟨11258999068426240000, 0, -114⟩,  -- 10^4
  ⟨14073748835532800000, 0, -111⟩,  -- 10^5
  ⟨17592186044416000000, 0, -108⟩,  -- 10^6
  ⟨10995116277760000000, 0, -104⟩,  -- 10^7
  ⟨13743895347200000000, 0, -101⟩,  -- 10^8
  ⟨17179869184000000000, 0, -98⟩,  -- 10^9
  ⟨10737418240000000000, 0, -94⟩,  -- 10^10
  ⟨13421772800000000000, 0, -91⟩,  -- 10^11
  ⟨16777216000000000000, 0, -88⟩,  -- 10^12
  ⟨10485760000000000000, 0, -84⟩,  -- 10^13
  ⟨13107200000000000000, 0, -81⟩,  -- 10^14
  ⟨16384000000000000000, 0, -78⟩,  -- 10^15
  ⟨10240000000000000000, 0, -74⟩,  -- 10^16
  ⟨12800000000000000000, 0, -71⟩,  -- 10^17
  ⟨16000000000000000000, 0, -68⟩,  -- 10^18
  ⟨10000000000000000000, 0, -64⟩,  -- 10^19
  ⟨12500000000000000000, 0, -61⟩,  -- 10^20
  ⟨15625000000000000000, 0, -58⟩,  -- 10^21
  ⟨9765625000000000000, 0, -54⟩,  -- 10^22
  ⟨12207031250000000000, 0, -51⟩,  -- 10^23
  ⟨15258789062500000000, 0, -48⟩,  -- 10^24
  ⟨9536743164062500000, 0, -44⟩,  -- 10^25
  ⟨11920928955078125000, 0, -41⟩,  -- 10^26
  ⟨14901161193847656250, 0, -38⟩,  -- 10^27
  ⟨9313225746154785156, 4611686018427387904, -34⟩,  -- 10^28
  ⟨11641532182693481445, 5764607523034234880, -31⟩,  -- 10^29
  ⟨14551915228366851806, 11817445422220181504, -28⟩,  -- 10^30
  ⟨18189894035458564758, 5548434740920451072, -25⟩,  -- 10^31
  ⟨11368683772161602973, 17302829768357445632, -21⟩,  -- 10^32
  ⟨14210854715202003717, 7793479155164643328, -18⟩,  -- 10^33
  ⟨17763568394002504646, 14353534962383192064, -15⟩,  -- 10^34
  ⟨11102230246251565404, 4359273333062107136, -11⟩,  -- 10^35
  ⟨13877787807814456755, 5449091666327633920, -8⟩,  -- 10^36
  ⟨17347234759768070944, 2199678564482154496, -5⟩,  -- 10^37
  ⟨10842021724855044340, 1374799102801346560, -1⟩,  -- 10^38
  ⟨13552527156068805425, 1718498878501683200, 2⟩,  -- 10^39
  ⟨16940658945086006781, 6759809616554491904, 5⟩,  -- 10^40
  ⟨10587911840678754238, 6530724019560251392, 9⟩,  -- 10^41
  ⟨13234889800848442797, 17386777061305090048, 12⟩,  -- 10^42
  ⟨16543612251060553497, 7898413271349198848, 15⟩,  -- 10^43
  ⟨10339757656912845935, 16465723340661719040, 19⟩,  -- 10^44
  ⟨12924697071141057419, 15970468157399760896, 22⟩,  -- 10^45
]

/-- The row for exponent `q`, or `none` outside `[-45, 45]`. -/
def epowAt (q : Int) : Option EPow :=
  if -45 ≤ q ∧ q ≤ 45 then epow[(q + 45).toNat]? else none

/-! ### The emitted arithmetic

Every field is a `Nat` read where the C reads a 64-bit or 128-bit word: the
truncations are the divisions and remainders by `2 ^ 64`, `2 ^ 63` and
`2 ^ sh`, and `EL_MASK ub` is `2 ^ (10 + ub) - 1`. -/

/-- `__builtin_clzll w` for `w ≠ 0`: the shift that puts `w`'s leading bit at
`2 ^ 63`. -/
def lz (w : Nat) : Nat := 63 - Nat.log2 w

/-- `W = w << lz`, in `[2 ^ 63, 2 ^ 64)` for `w ≠ 0`. -/
def Wnorm (w : Nat) : Nat := w * 2 ^ lz w

/-- The high 64 bits of a 128-bit product: `(uint64_t)(A >> 64)`. -/
def hi64 (a b : Nat) : Nat := a * b / 2 ^ 64

/-- The low 64 bits of a 128-bit product: `(uint64_t)A`. -/
def lo64 (a b : Nat) : Nat := a * b % 2 ^ 64

/-- `el_pack`'s arguments: the 53-bit significand, the round-up bit, the binade
bit, the table exponent and the normalising shift. -/
structure Pack where
  m : Nat
  up : Nat
  ub : Nat
  e : Int
  lz : Nat

/-- `el_pack`: the encoded fields, or `none` where `eu` is outside
`[-1022, 1023]` and the emitted code hands the value to the slower tier.
`mm = m + up` is the significand after the round-up, and a carry out of it
moves the exponent by one. -/
def elPack (p : Pack) : Option Code :=
  let mm := p.m + p.up
  let ov := mm / 2 ^ 53
  let sh := 10 + p.ub + ov
  let eu : Int := 180 + (sh : Int) + p.e - (p.lz : Int)
  if -1022 ≤ eu ∧ eu ≤ 1023 then
    some { expField := (eu + 1023).toNat, mant := 2 ^ 52 + mm % 2 ^ 52 }
  else none

/-- The guard's reading of `A = W * hi`: its two words, the binade bit `ub`,
the shift `10 + ub`, the dropped part `hp` and the half point
`hh = 2 ^ (9 + ub)`. -/
structure Slice where
  Ahi : Nat
  Alo : Nat
  ub : Nat
  sh : Nat
  hp : Nat
  hh : Nat

/-- The fields `num_el_el1` reads out of the high half of the product. -/
def sliceOf (W hi : Nat) : Slice :=
  let Ahi := hi64 W hi
  let ub := Ahi / 2 ^ 63
  let sh := 10 + ub
  { Ahi := Ahi, Alo := lo64 W hi, ub := ub, sh := sh,
    hp := Ahi % 2 ^ sh, hh := 2 ^ (9 + ub) }

/-- The guard's slice test as emitted: `hp - (hh - 2) <= 2` in unsigned 64-bit
arithmetic. -/
def inWindow (hp hh : Nat) : Bool :=
  decide ((hp + 2 ^ 64 - (hh - 2)) % 2 ^ 64 ≤ 2)

/-- `(u + r) % u = r` for `r < u`: the wrap the emitted unsigned subtraction
does when the difference is negative. -/
theorem add_mod_self {u r : Nat} (h : r < u) : (u + r) % u = r := by
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h]

/-- The emitted test is the three-value window: with `2 ≤ hh ≤ 2 ^ 11` and
`hp < 2 ^ 64` the wrapped difference is at most two exactly when it is in
`[hh - 2, hh]`, so the unsigned test is the conjunction. -/
theorem inWindow_iff {hp hh : Nat} (hh2 : 2 ≤ hh) (hhle : hh ≤ 2 ^ 11)
    (hlt : hp < 2 ^ 64) :
    (inWindow hp hh = true ↔ hh - 2 ≤ hp ∧ hp ≤ hh) := by
  unfold inWindow
  rw [decide_eq_true_eq]
  by_cases hge : hh - 2 ≤ hp
  · have hx : hp + 2 ^ 64 - (hh - 2) = 2 ^ 64 + (hp - (hh - 2)) := by
      rw [Nat.add_comm hp, Nat.add_sub_assoc hge]
    have hdiff : hp - (hh - 2) < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le hp (hh - 2)) hlt
    rw [hx, add_mod_self hdiff]
    exact ⟨fun h => ⟨hge, by omega⟩, fun h => by omega⟩
  · have hlow : hp < hh - 2 := Nat.lt_of_not_le hge
    have hx : hp + 2 ^ 64 - (hh - 2) = 2 ^ 64 - ((hh - 2) - hp) := by omega
    have hd : (hh - 2) - hp ≤ 2 ^ 11 :=
      Nat.le_trans (Nat.sub_le (hh - 2) hp) (by omega)
    have hpos : 0 < (hh - 2) - hp := Nat.sub_pos_of_lt hlow
    have hlt' : 2 ^ 64 - ((hh - 2) - hp) < 2 ^ 64 :=
      Nat.sub_lt (by decide) hpos
    have hbig : 2 < 2 ^ 64 - ((hh - 2) - hp) := by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hd 2) (by decide)
    rw [hx, Nat.mod_eq_of_lt hlt']
    exact ⟨fun h => absurd h (by omega), fun h => absurd h.1 (by omega)⟩

/-! ### The decision

`num_el_el1` on `(w, q)`: the normalised product's high half, the window and
`el_exact`'s tie test, then `el_pack`.  `none` is a refusal -- the out-of-range
exponent, the undecidable remainder, or `el_pack`'s own range test -- and each
refusal leaves the value to the caller's exact conversion.  The sign is the
caller's and does not enter the magnitude. -/

/-- **The guard's decision**: the fields `num_el_el1` returns for the mantissa
`w` and the exponent `q`, or `none` where it refuses. -/
def elTier2Code (w : Nat) (q : Int) : Option Code :=
  match epowAt q with
  | none => none
  | some t =>
    if w = 0 then some { expField := 0, mant := 0 }
    else
      let W := Wnorm w
      let s := sliceOf W t.hi
      if inWindow s.hp s.hh then
        let c := hi64 W t.lo
        let L := lo64 W t.lo
        let Rlo := (s.Alo + c) % 2 ^ 64
        let Rhi := (s.Ahi + (if Rlo < s.Alo then 1 else 0)) % 2 ^ 64
        let ub := Rhi / 2 ^ 63
        let sh := 10 + ub
        let m := Rhi / 2 ^ sh
        let hp := Rhi % 2 ^ sh
        let hh := 2 ^ (9 + ub)
        let tie := hp = hh
        let close := hp = hh - 1
        let undec := (tie && decide (Rlo ||| L = 0)) ||
          (close && decide (Rlo = 2 ^ 64 - 1))
        if undec && decide (q < 0) then none
        else
          let up : Nat :=
            if hp > hh then 1
            else if tie && decide ((Rlo ||| L) ≠ 0 ∨ m % 2 = 1) then 1 else 0
          elPack { m := m, up := up, ub := ub, e := t.e, lz := lz w }
      else
        elPack { m := s.Ahi / 2 ^ s.sh, up := if s.hp > s.hh then 1 else 0,
                 ub := s.ub, e := t.e, lz := lz w }

/-! ### The specification's decision at the same input

`roundMag` reads the exact value in ticks.  `w * 10 ^ q` in those units is the
pair below: for `q ≥ 0` it is an integer scaled by `2 ^ 1074`, and for `q < 0`
it is `w * 2 ^ 1074 / 10 ^ -q`. -/

/-- The exact value of `w * 10 ^ q` in `roundMag`'s ticks, `(P, d)`. -/
def valueTicks (w : Nat) (q : Int) : Nat × Nat :=
  if 0 ≤ q then (w * 10 ^ q.toNat * 2 ^ 1074, 1)
  else (w * 2 ^ 1074, 10 ^ q.natAbs)

/-- **The obligation**: on every `(w, q)` the guard decides, the fields it
returns are `roundMag`'s magnitude for the exact value. -/
def ElGuardRefinesOn : Prop :=
  ∀ (w : Nat) (q : Int) (c : Code), elTier2Code w q = some c →
    roundMag (valueTicks w q).1 (valueTicks w q).2 = .fin c

/-! ### What the shape rests on

Below the emitted significand the exact remainder of the 192-bit product is
`hp * 2 ^ 128 + Rlo * 2 ^ 64 + L + g`, where `Rlo` is the high half's low 64
bits, `L` the low half's low 64 bits and `g = W * f` the table entry's
fractional part.  Divided by `2 ^ 64` the remainder is `hp * 2 ^ 64 + Rlo + y`
with `y = (L + g) / 2 ^ 64 < 2`, against a half point of `hh * 2 ^ 64`: one
unit of the slice's arithmetic is `2 ^ 64` of the remainder, and
`discarded_lt` puts everything the guard cannot see at less than one unit and a
sixty-fourth.  The window is measured in single units because that is the whole
width of what is discarded.

What fixes the window's size is measured, not proved here.  Outside
`[hh - 2, hh]` the remainder is at least one unit from the half point, which is
more than the discarded part spans, so those values decide on the slice alone
(`rem_lt_half`, `half_le_rem`).  Inside it the decision changes at `hh - 1` (a
carry out of the low half) and at `hh` (a nonzero low half, or the parity at an
exact tie); a sweep over every digit count put the change at those two slice
values only.  A carry needs `Alo + c >= 2 ^ 64`, which excludes
`Rlo = 2 ^ 64 - 1`, so `hp = hh - 2` can neither tie nor be refused and always
decides as the slice does: the emitted test is one slice value wider than the
decision needs, and it is never wrong for it. -/

/-- Below the window: `hp + 3 ≤ hh` leaves two whole units of slack, and the
discarded words are worth just over one, so the largest possible remainder is
still below the half point and the emitted `up = 0` is the nearest decision
whatever they are.  `u` is one unit of the slice's scale, `2 ^ 64`. -/
theorem rem_lt_half {hp hh u Rlo : Nat} (hu : 2 ≤ u) (hR : Rlo < u)
    (hfar : hp + 3 ≤ hh) :
    hp * u + Rlo + 2 ≤ hh * u := by
  have h1 : hp * u ≤ (hh - 3) * u := Nat.mul_le_mul_right u (by omega)
  have h2 : (hh - 3) * u + u = (hh - 2) * u := by
    have h3 : hh - 3 + 1 = hh - 2 := by omega
    rw [← h3, Nat.add_mul, Nat.one_mul]
  have h4 : (hh - 2) * u + 1 ≤ hh * u := by
    have h6 : (hh - 2) * u + 2 * u = hh * u := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have h7 : 1 ≤ 2 * u := by omega
    omega
  calc hp * u + Rlo + 2 = hp * u + (Rlo + 2) := Nat.add_assoc _ _ _
    _ ≤ (hh - 3) * u + (u + 1) := Nat.add_le_add h1 (by omega)
    _ = (hh - 2) * u + 1 := by rw [← h2, Nat.add_assoc]
    _ ≤ hh * u := h4

/-- Above the window (`hh + 1 ≤ hp`): the remainder is already past the half
point, so the emitted `up = 1` is the nearest decision and again no low word is
needed. -/
theorem half_le_rem {hp hh u Rlo : Nat} (habove : hh + 1 ≤ hp) :
    hh * u ≤ hp * u + Rlo := by
  have h1 : hh * u ≤ hp * u := Nat.mul_le_mul_right u (by omega)
  exact Nat.le_trans h1 (Nat.le_add_right _ _)

/-- Everything the guard cannot see is worth less than one unit plus a
sixty-fourth of one: `Rlo * 2 ^ 64 + L + g < 2 ^ 128 + 2 ^ 65` for `Rlo`,
`L`, `g < 2 ^ 64`.  That is the whole of the discarded part, so a slice value
one unit away from the half point is decided whatever it is, and a slice value
at the half point is not. -/
theorem discarded_lt {Rlo L g : Nat} (hR : Rlo < 2 ^ 64) (hL : L < 2 ^ 64)
    (hg : g < 2 ^ 64) : Rlo * 2 ^ 64 + L + g < 2 ^ 128 + 2 ^ 65 := by
  have h1 : Rlo * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 := by rw [Nat.sub_mul, Nat.one_mul]
  omega

/-! ### The emitted fields as the encoding's bits

`codeBits` is `Binary64.toBits`'s pattern for a finite magnitude, which is what
the emitted kernel's `out_u64` carries. -/

/-- The little-endian integer a finite code's eight bytes spell. -/
def codeBits (c : Code) : Nat :=
  if c.expField = 0 then c.mant else c.expField * 2 ^ 52 + (c.mant - 2 ^ 52)

/-! ### Axiom footprint

Every declaration is pinned.  The statement is computable, and the two lemmas
must stay at the standard footprint: `omega` closes linear arithmetic without
`Classical.choice` when the goal does not need it, and `decide`-free rewriting
adds nothing. -/

#print axioms LeanLLVM.ElGuardRefine.epowAt
#print axioms LeanLLVM.ElGuardRefine.lz
#print axioms LeanLLVM.ElGuardRefine.Wnorm
#print axioms LeanLLVM.ElGuardRefine.hi64
#print axioms LeanLLVM.ElGuardRefine.lo64
#print axioms LeanLLVM.ElGuardRefine.elPack
#print axioms LeanLLVM.ElGuardRefine.sliceOf
#print axioms LeanLLVM.ElGuardRefine.inWindow
#print axioms LeanLLVM.ElGuardRefine.add_mod_self
#print axioms LeanLLVM.ElGuardRefine.inWindow_iff
#print axioms LeanLLVM.ElGuardRefine.elTier2Code
#print axioms LeanLLVM.ElGuardRefine.valueTicks
#print axioms LeanLLVM.ElGuardRefine.ElGuardRefinesOn
#print axioms LeanLLVM.ElGuardRefine.rem_lt_half
#print axioms LeanLLVM.ElGuardRefine.half_le_rem
#print axioms LeanLLVM.ElGuardRefine.discarded_lt
#print axioms LeanLLVM.ElGuardRefine.codeBits

/-! ### The statement against the emitted kernel

`kernel/json/stage2.c`'s `num_el_el1`, extracted to a driver, returns these
eight bytes for the same inputs; glibc's `strtod` on the same lexeme returns
the same bytes, so each line below is the emitted decision *and* the correctly
rounded one.  The comments give what the emitted kernel returned.

The two 15- and 16-digit lines are the ticket's sub-case and they are decided
by the low words: at `hp = hh` the exact remainder is 0.82 and 0.91 units of
`2 ^ 128` above the half point, so the slice alone would round down and the
window rounds up.  `3236375135687599514e1` decides from the slice with exactly
one unit of slack (`hp = hh + 1`, low word zero), and `9762249337681020367e32`
is the tightest below-the-half decision the slice takes (`hp = hh - 3`, low
word `2 ^ 64 - 5389`, one and a half units from the half point). -/

/-- The witnesses, as `(mantissa, exponent)`. -/
def witnesses : List (Nat × Int) :=
  [(34, -36), (7, 22), (50172062708807565, -1), (1, -45),
   (731748122986143, -45), (5637789036708387, -45), (4002413731783293, -45),
   (3236375135687599514, 1), (9762249337681020367, 32)]

/-- What the guard decides for a witness, in the encoding's bits. -/
def witnessBits (w : Nat) (q : Int) : Option Nat :=
  (elTier2Code w q).map codeBits

#eval witnesses.map (fun (w, q) => (w, q, witnessBits w q))
#eval witnessBits 34 (-36)
             -- emitted: 4091125317150703962
#eval witnessBits 7 22                  -- emitted: 4948793441493988800
#eval witnessBits 50172062708807565 (-1) -- emitted: refuses (tier 3)
#eval witnessBits 1 (-45)               -- emitted: 3933566627244108473
#eval epowAt 0
#eval epowAt (-45)
#eval epowAt (-46)

end LeanLLVM.ElGuardRefine
