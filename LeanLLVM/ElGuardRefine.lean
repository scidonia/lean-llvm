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

It also proves the bridge from `roundMag`'s tick pair to the emitted slice,
and the facts the decision rests on:

* the table's fraction: every row is `10 ^ q = (hi * 2 ^ 64 + lo + f) * 2 ^ e`
  with `0 ≤ f < 1` (`EPow.Fits`, checked once over all ninety-one rows by
  `epow_rows`), with no fraction at all for `q ≥ 0` (`EPow.Neq`);
* the product identity: `W * (hi * 2 ^ 64 + lo)` is
  `Rhi * 2 ^ 128 + Rlo * 2 ^ 64 + L` with `Rhi`, `Rlo` the two words `el_exact`
  builds (`exact_split`), so everything below the slice is exactly
  `Rlo * 2 ^ 64 + L + g`;
* the tick-to-slice bridge: `valueTicks`'s `(P, d)` is
  `W * (hi * 2 ^ 64 + lo) * 2 ^ s`, `s = 1074 + e - lz`, for a row with no
  fraction (`valueTicks_nonneg`), and its binade is `190 + s` or `191 + s`
  according as that product reaches `2 ^ 191` (`binade_valueTicks_nonneg`);
  for a truncated row (`q < 0`) the value is `w * 2 ^ 1074 / 10 ^ (-q)` and the
  comparison is `2 ^ 191 * 10 ^ (-q) ≤ W * 2 ^ (-e)` (`binade_valueTicks_neg`);
* the window's edge is the tie (`tie_edge`, `tie_exact_iff`): at `hp = hh` the
  product is the midpoint between `m` and `m + 1` plus exactly the discarded
  words, so the tie is their vanishing and the emitted `up` there is the even
  significand.

It does not prove the obligation.  What remains is the significand itself —
that `roundMag`'s `sig` (or its successor, on a round-up) is the emitted `m`,
which is `normalCode`'s two comparisons of the remainder against the ulp — and
the range/refusal cases (`el_pack`'s exponent test and the `q < 0` refusal at a
zero-valued tie).  The table check is kernel evaluation over the ninety-one
rows, so a proof of the obligation at a symbolic `q` reads the row's facts
through `row_of_epowAt` rather than splitting on `q`.  `#eval` at the end
reproduces the emitted kernel's own output on the boundary witnesses, so the
definitions are the emitted test rather than a paraphrase of it.
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

-- The table check below is one kernel evaluation over ninety-one rows of
-- five-hundred-bit arithmetic.
set_option maxRecDepth 10000

/-! ### The table's fraction -/

/-- The row's 128-bit significand `H = hi * 2 ^ 64 + lo`. -/
def eH (t : EPow) : Nat := t.hi * 2 ^ 64 + t.lo
/-- The numerator `10 ^ max(q, 0) * 2 ^ max(-e, 0)` of the row's ratio. -/
def eN (q : Int) (t : EPow) : Nat := 10 ^ q.toNat * 2 ^ (-t.e).toNat
/-- The denominator `10 ^ max(-q, 0) * 2 ^ max(e, 0)` of the row's ratio. -/
def eD (q : Int) (t : EPow) : Nat := 10 ^ (-q).toNat * 2 ^ t.e.toNat
/-- The row is exact: `H` is the floor of `10 ^ q * 2 ^ (-e)`, i.e.
`10 ^ q = (H + f) * 2 ^ e` with `0 ≤ f < 1`. -/
abbrev EPow.Fits (q : Int) (t : EPow) : Prop := eH t = eN q t / eD q t
/-- The row has no fraction at all: `10 ^ q = H * 2 ^ e` exactly. -/
abbrev EPow.Neq (q : Int) (t : EPow) : Prop := eH t * eD q t = eN q t

/-- Everything a row gives: the word bounds, the exponent's range, the
fraction, no fraction for `q ≥ 0`, a nonzero fraction for `q < 0`, and a
negative exponent there. -/
def EPow.Row (q : Int) (t : EPow) : Prop :=
  (2 ^ 63 ≤ t.hi ∧ t.hi < 2 ^ 64 ∧ t.lo < 2 ^ 64) ∧
  ((-277 : Int) ≤ t.e ∧ t.e ≤ 22) ∧
  t.Fits q ∧ (0 ≤ q → t.Neq q) ∧ (q < 0 → 0 < eN q t % eD q t) ∧
  (q < 0 → t.e < 0)

/-- `EPow.Row` as a `Bool`, so the ninety-one rows are checked once by kernel
evaluation. -/
def rowB (q : Int) (t : EPow) : Bool :=
  decide (2 ^ 63 ≤ t.hi ∧ t.hi < 2 ^ 64 ∧ t.lo < 2 ^ 64) &&
  decide ((-277 : Int) ≤ t.e ∧ t.e ≤ 22) &&
  decide (t.Fits q) &&
  (!decide ((0 : Int) ≤ q) || decide (t.Neq q)) &&
  (!decide (q < 0) || decide (0 < eN q t % eD q t)) &&
  (!decide (q < 0) || decide (t.e < 0))

/-- The check for the row at index `i`, i.e. exponent `i - 45`. -/
def rowOf (i : Nat) : Bool := rowB ((i : Int) - 45) ((epow[i]?).getD default)

/- The largest exponent the table needs is `2 ^ 277`, above the elaborator's
default evaluation threshold; the option is scoped to this check. -/
set_option exponentiation.threshold 400 in
/-- **The table, checked.**  All ninety-one rows satisfy `EPow.Row`. -/
theorem epow_rows : (List.range 91).all rowOf = true := by decide

/-- The `Bool` check implies the proposition. -/
theorem rowB_row {q : Int} {t : EPow} (h : rowB q t = true) : t.Row q := by
  simp only [rowB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩ := h
  refine ⟨hA, hB, hC, ?_, ?_, ?_⟩
  · intro hq
    rcases hD with h' | h'
    · exact absurd (decide_eq_true_eq.mpr hq) (by rw [h']; simp)
    · exact h'
  · intro hq
    rcases hE with h' | h'
    · exact absurd (decide_eq_true_eq.mpr hq) (by rw [h']; simp)
    · exact h'
  · intro hq
    rcases hF with h' | h'
    · exact absurd (decide_eq_true_eq.mpr hq) (by rw [h']; simp)
    · exact h'

/-- **The table at a symbolic exponent.**  A looked-up row carries its own
fraction, bounds and exponent sign, so a proof reads them here rather than
splitting on `q`. -/
theorem row_of_epowAt {q : Int} {t : EPow} (h : epowAt q = some t) : t.Row q := by
  unfold epowAt at h
  split at h
  · rename_i hr
    obtain ⟨hsize, hget⟩ := Array.getElem?_eq_some_iff.mp h
    have hq45 : 0 ≤ q + 45 := by omega
    have hi_eq : ((q + 45).toNat : Int) - 45 = q := by
      have : ((q + 45).toNat : Int) = q + 45 := Int.toNat_of_nonneg hq45
      omega
    have hsz : epow.size = 91 := rfl
    have hmem : (q + 45).toNat ∈ List.range 91 := List.mem_range.mpr (by omega)
    have h1 := (List.all_eq_true.mp epow_rows) _ hmem
    unfold rowOf at h1
    have h2 : ((epow[(q + 45).toNat]?).getD default) = t := by
      rw [Array.getElem?_eq_getElem hsize, hget]
      simp
    rw [h2] at h1
    rw [hi_eq] at h1
    exact rowB_row h1
  · exact absurd h (by simp)

/-! ### The 192-bit split -/

/-- A product splits into its high and low sixty-four-bit words. -/
theorem hi64_add_lo64 {a b : Nat} : a * b = hi64 a b * 2 ^ 64 + lo64 a b := by
  unfold hi64 lo64
  rw [Nat.mul_comm (a * b / 2 ^ 64) (2 ^ 64)]
  exact (Nat.div_add_mod (a * b) (2 ^ 64)).symm

/-- `2 ^ 128 = 2 ^ 64 * 2 ^ 64`, the product's cross term. -/
theorem pow64_128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by
  rw [show (128 : Nat) = 64 + 64 from rfl, Nat.pow_add]

/-- `2 ^ 65 = 2 ^ 64 * 2`: a sum of two sixty-four-bit words is below it. -/
theorem pow64_65 : (2 : Nat) ^ 65 = 2 ^ 64 * 2 := by
  rw [show (65 : Nat) = 64 + 1 from rfl, Nat.pow_add, Nat.pow_one]

/-- A sum of two sixty-four-bit words is its own low word plus the carry into
the high word. -/
theorem word_add {alo c : Nat} (halo : alo < 2 ^ 64) (hc : c < 2 ^ 64) :
    alo + c = (alo + c) % 2 ^ 64 +
      (if (alo + c) % 2 ^ 64 < alo then 1 else 0) * 2 ^ 64 := by
  have hlt : alo + c < 2 ^ 65 := by rw [pow64_65]; omega
  have hdec := Nat.div_add_mod (alo + c) (2 ^ 64)
  have hqle : (alo + c) / 2 ^ 64 ≤ 1 := by
    have h2 : (alo + c) / 2 ^ 64 < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      omega
    omega
  by_cases h0 : (alo + c) / 2 ^ 64 = 0
  · rw [h0] at hdec
    simp only [Nat.mul_zero, Nat.zero_add] at hdec
    split <;> omega
  · have hq1 : (alo + c) / 2 ^ 64 = 1 := by omega
    rw [hq1] at hdec
    simp only [Nat.mul_one] at hdec
    split <;> omega

/-- `el_exact`'s low word: `Alo + c` truncated to sixty-four bits. -/
def exactRlo (W hi lo : Nat) : Nat := (lo64 W hi + hi64 W lo) % 2 ^ 64

/-- `el_exact`'s high word: `Ahi` plus the carry out of the low word. -/
def exactRhi (W hi lo : Nat) : Nat :=
  (hi64 W hi + (if exactRlo W hi lo < lo64 W hi then 1 else 0)) % 2 ^ 64

/-- **The two words are the product's own.**  `W * (hi * 2 ^ 64 + lo)` — the
one-hundred-and-ninety-two-bit integer the guard's two multiplies spell — is
`Rhi * 2 ^ 128 + Rlo * 2 ^ 64 + L`, with `Rhi` and `Rlo` the two words
`el_exact` builds and `L` the low half's low word.  No word wraps: `W, hi <
2 ^ 64` put the high word at most `2 ^ 64 - 1` before the carry. -/
theorem exact_split {W hi lo : Nat} (hW : W < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (hlo : lo < 2 ^ 64) :
    W * (hi * 2 ^ 64 + lo) =
      exactRhi W hi lo * 2 ^ 128 + exactRlo W hi lo * 2 ^ 64 + lo64 W lo := by
  have hA := hi64_add_lo64 (a := W) (b := hi)
  have hB := hi64_add_lo64 (a := W) (b := lo)
  have halo : lo64 W hi < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hc : hi64 W lo < 2 ^ 64 := by
    unfold hi64
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    have h1 : W * lo ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_lt_of_le (by omega : 2 ^ 64 - 1 < 2 ^ 64)
        (by omega : 2 ^ 64 - 1 ≤ 2 ^ 64) (by decide)
    exact Nat.lt_of_le_of_lt h1 h2
  have hadd : lo64 W hi + hi64 W lo =
      exactRlo W hi lo +
        (if exactRlo W hi lo < lo64 W hi then 1 else 0) * 2 ^ 64 :=
    word_add halo hc
  have hAhi : hi64 W hi + (if exactRlo W hi lo < lo64 W hi then 1 else 0) < 2 ^ 64 := by
    have hwhi : W * hi ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : hi64 W hi ≤ 2 ^ 64 - 2 := by
      unfold hi64
      have hlt : W * hi < (2 ^ 64 - 1) * 2 ^ 64 := by
        have h3 : (2 ^ 64 - 1) * (2 ^ 64 - 1) < (2 ^ 64 - 1) * 2 ^ 64 :=
          Nat.mul_lt_mul_of_pos_left (by omega : 2 ^ 64 - 1 < 2 ^ 64) (by omega)
        exact Nat.lt_of_le_of_lt hwhi h3
      have h4 : W * hi / 2 ^ 64 < 2 ^ 64 - 1 :=
        (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt
      omega
    have hcarry : (if exactRlo W hi lo < lo64 W hi then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  have hmod : exactRhi W hi lo =
      hi64 W hi + (if exactRlo W hi lo < lo64 W hi then 1 else 0) :=
    Nat.mod_eq_of_lt hAhi
  rw [hmod, pow64_128]
  calc W * (hi * 2 ^ 64 + lo) = (W * hi) * 2 ^ 64 + W * lo := by
        simp only [Nat.mul_add, Nat.mul_assoc] <;> ac_rfl
    _ = (hi64 W hi * 2 ^ 64 + lo64 W hi) * 2 ^ 64
          + (hi64 W lo * 2 ^ 64 + lo64 W lo) := by rw [hA, hB]
    _ = hi64 W hi * (2 ^ 64 * 2 ^ 64)
          + (lo64 W hi + hi64 W lo) * 2 ^ 64 + lo64 W lo := by
        simp only [Nat.add_mul, Nat.mul_assoc] <;> ac_rfl
    _ = hi64 W hi * (2 ^ 64 * 2 ^ 64)
          + (exactRlo W hi lo +
              (if exactRlo W hi lo < lo64 W hi then 1 else 0) * 2 ^ 64)
            * 2 ^ 64
          + lo64 W lo := by rw [← hadd]
    _ = (hi64 W hi + (if exactRlo W hi lo < lo64 W hi then 1 else 0))
          * (2 ^ 64 * 2 ^ 64)
          + exactRlo W hi lo * 2 ^ 64 + lo64 W lo := by
        simp only [Nat.add_mul, Nat.mul_assoc] <;> ac_rfl



/-! ### Below and above the window, with the discarded part -/

/-- Below the window, with the discarded part: `hp + 3 ≤ hh` leaves two whole
units of slack while the discarded words are worth just over one, so the full
remainder is still below the half point. -/
theorem rem_lt_half_full {hp hh u Rlo L g : Nat} (hu : 2 ≤ u) (hR : Rlo < u)
    (hLg : L + g < 2 * u) (hfar : hp + 3 ≤ hh) :
    hp * u + Rlo + (L + g) / u < hh * u := by
  have h1 : hp * u + Rlo + 2 ≤ hh * u := rem_lt_half hu hR hfar
  have h2 : (L + g) / u ≤ 1 := by
    have h3 : (L + g) / u < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  omega

/-- Above the window, with the discarded part: the remainder is already past
the half point whatever the low words and the fraction are. -/
theorem half_le_rem_full {hp hh u Rlo L g : Nat} (habove : hh + 1 ≤ hp) :
    hh * u ≤ hp * u + Rlo + (L + g) / u :=
  Nat.le_trans (half_le_rem habove) (Nat.le_add_right _ _)

/-! ### `Wnorm`'s two bounds -/

/-- `2 ^ log2 n ≤ n` for positive `n`, without `Classical.choice`. -/
theorem pow_log2_le : ∀ (n : Nat), 0 < n → 2 ^ Nat.log2 n ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have h0 : Nat.log2 n = 0 := by
        rw [Nat.log2_def]; split <;> omega
      rw [h0, Nat.pow_zero]
      omega
    · rw [Nat.log2_def]
      split
      · rename_i h2
        have hpos : 0 < n / 2 := by omega
        have hlt' : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        have hi := ih (n / 2) hlt' hpos
        rw [show Nat.log2 (n / 2) + 1 = (Nat.log2 (n / 2)).succ from rfl, Nat.pow_succ]
        calc 2 ^ Nat.log2 (n / 2) * 2 ≤ (n / 2) * 2 := Nat.mul_le_mul_right 2 hi
          _ ≤ n := by omega
      · omega

/-- `n < 2 ^ (log2 n + 1)`: the leading bit of `n`, without choice. -/
theorem lt_pow_log2_succ (n : Nat) : n < 2 ^ (Nat.log2 n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have h0 : Nat.log2 n = 0 := by
        rw [Nat.log2_def]; split <;> omega
      have hpow : (2 : Nat) ^ (0 + 1) = 2 := by decide
      rw [h0, hpow]
      exact hlt
    · rw [Nat.log2_def]
      split
      · rename_i h2
        have hlt' : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        have hi := ih (n / 2) hlt'
        rw [show Nat.log2 (n / 2) + 1 + 1 = (Nat.log2 (n / 2) + 1).succ from rfl, Nat.pow_succ]
        have h3 : (n / 2) * 2 < 2 ^ (Nat.log2 (n / 2) + 1) * 2 :=
          Nat.mul_lt_mul_of_pos_right hi (by decide)
        have hmod := Nat.div_add_mod n 2
        have hle : n % 2 ≤ 1 := by
          have := Nat.mod_lt n (by decide : 0 < 2)
          omega
        omega
      · omega

/-- A positive `w` below `2 ^ k` has `log2 w < k`. -/
theorem log2_lt_of_lt_pow {w k : Nat} (hw : 0 < w) (h : w < 2 ^ k) :
    Nat.log2 w < k := by
  rcases Nat.lt_or_ge (Nat.log2 w) k with hlt | hk
  · exact hlt
  · exfalso
    have h1 : 2 ^ k ≤ 2 ^ Nat.log2 w := Nat.pow_le_pow_right (by decide) hk
    have h2 := pow_log2_le w hw
    omega

/-- The normalising shift is at most sixty-three. -/
theorem lz_le_63 (w : Nat) : lz w ≤ 63 := by unfold lz; omega

/-- The normalised mantissa's leading bit is at `2 ^ 63`. -/
theorem Wnorm_lower {w : Nat} (hw0 : 0 < w) (hw : w < 2 ^ 64) : 2 ^ 63 ≤ Wnorm w := by
  unfold Wnorm lz
  have hL : Nat.log2 w ≤ 63 := by
    have := log2_lt_of_lt_pow hw0 hw
    omega
  have h1 : 2 ^ Nat.log2 w * 2 ^ (63 - Nat.log2 w) ≤ w * 2 ^ (63 - Nat.log2 w) :=
    Nat.mul_le_mul_right _ (pow_log2_le w hw0)
  have h2 : 2 ^ Nat.log2 w * 2 ^ (63 - Nat.log2 w) = 2 ^ 63 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rwa [h2] at h1

/-- The normalised mantissa is a sixty-four-bit word. -/
theorem Wnorm_upper {w : Nat} (hw0 : 0 < w) (hw : w < 2 ^ 64) : Wnorm w < 2 ^ 64 := by
  unfold Wnorm lz
  have hL : Nat.log2 w ≤ 63 := by
    have := log2_lt_of_lt_pow hw0 hw
    omega
  have h1 : w * 2 ^ (63 - Nat.log2 w) < 2 ^ (Nat.log2 w + 1) * 2 ^ (63 - Nat.log2 w) :=
    Nat.mul_lt_mul_of_pos_right (lt_pow_log2_succ w) (Nat.two_pow_pos _)
  have h2 : 2 ^ (Nat.log2 w + 1) * 2 ^ (63 - Nat.log2 w) = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rwa [h2] at h1

/-! ### The table row's significand -/

/-- The row's significand is at least `2 ^ 127`. -/
theorem eH_lower {t : EPow} (h : 2 ^ 63 ≤ t.hi) : 2 ^ 127 ≤ eH t := by
  unfold eH
  have h1 : 2 ^ 63 * 2 ^ 64 ≤ t.hi * 2 ^ 64 := Nat.mul_le_mul_right _ h
  have h2 : (2 : Nat) ^ 127 = 2 ^ 63 * 2 ^ 64 := by
    rw [show (127 : Nat) = 63 + 64 from rfl, Nat.pow_add]
  rw [h2]
  exact Nat.le_trans h1 (Nat.le_add_right _ _)

/-- The row's significand is below `2 ^ 128`. -/
theorem eH_upper {t : EPow} (hhi : t.hi < 2 ^ 64) (hlo : t.lo < 2 ^ 64) :
    eH t < 2 ^ 128 := by
  unfold eH
  have h1 : t.hi * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 := by
    rw [Nat.sub_mul, Nat.one_mul, ← pow64_128]
  omega

/-! ### The binade of the exact product -/

/-- `binade` is the unique `B` with `d * 2 ^ B ≤ P < d * 2 ^ (B + 1)`, given
an in-range witness for the search. -/
theorem binade_unique {P d B : Nat} (hex : ∃ B', B' < 2100 ∧ P < d * 2 ^ (B' + 1))
    (hB : d * 2 ^ B ≤ P) (hup : P < d * 2 ^ (B + 1)) : binade P d = B := by
  obtain ⟨hminup, hmin⟩ := binade_spec hex
  have h1 : binade P d ≤ B := by
    apply Nat.le_of_not_lt
    intro hlt
    exact absurd (hmin B hlt) (Nat.not_le.mpr hup)
  have h2 : B ≤ binade P d := by
    apply Nat.le_of_not_lt
    intro hlt
    have hp : d * 2 ^ (binade P d + 1) ≤ d * 2 ^ B :=
      Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hlt))
    exact absurd (Nat.le_trans hp hB) (Nat.not_le.mpr hminup)
  exact Nat.le_antisymm h1 h2

/-- Two normalised factors multiply to at least `2 ^ 190`. -/
theorem binade_lower_190 {W H : Nat} (hWlo : 2 ^ 63 ≤ W) (hHlo : 2 ^ 127 ≤ H) :
    2 ^ 190 ≤ W * H := by
  have h1 : 2 ^ 63 * 2 ^ 127 ≤ W * H := Nat.mul_le_mul hWlo hHlo
  have h2 : (2 : Nat) ^ 190 = 2 ^ 63 * 2 ^ 127 := by
    rw [show (190 : Nat) = 63 + 127 from rfl, Nat.pow_add]
  rwa [h2]

/-- The same product is below `2 ^ 192`. -/
theorem binade_upper_192 {W H : Nat} (hWhi : W < 2 ^ 64) (hHhi : H < 2 ^ 128) :
    W * H < 2 ^ 192 := by
  have h1 : W * H < 2 ^ 64 * 2 ^ 128 :=
    Nat.mul_lt_mul_of_le_of_lt (by omega) hHhi (Nat.two_pow_pos 64)
  have h2 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 := by
    rw [show (192 : Nat) = 64 + 128 from rfl, Nat.pow_add]
  rwa [h2]

/-- A product at least `2 ^ j` times, scaled by `2 ^ s`, is at least
`2 ^ (j + s)`. -/
theorem prod_lower {W H P s j : Nat} (h : 2 ^ j ≤ W * H)
    (hP : P = W * H * 2 ^ s) : 1 * 2 ^ (j + s) ≤ P := by
  rw [hP, Nat.one_mul, Nat.pow_add]
  exact Nat.mul_le_mul_right _ h

/-- Below `2 ^ j` times, scaled by `2 ^ s`, is below `2 ^ (j + s)`. -/
theorem prod_upper {W H P s j : Nat} (h : W * H < 2 ^ j)
    (hP : P = W * H * 2 ^ s) : P < 1 * 2 ^ (j + s) := by
  rw [hP, Nat.one_mul]
  calc W * H * 2 ^ s < 2 ^ j * 2 ^ s :=
        Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos s)
    _ = 2 ^ (j + s) := (Nat.pow_add _ _ _).symm

/-- The binade search has an in-range witness for the product. -/
theorem prod_exists {W H P s : Nat} (hs : s < 1900) (h : W * H < 2 ^ 192)
    (hP : P = W * H * 2 ^ s) : ∃ B, B < 2100 ∧ P < 1 * 2 ^ (B + 1) := by
  refine ⟨192 + s, by omega, ?_⟩
  have h1 : P < 1 * 2 ^ (192 + s) := prod_upper h hP
  have h2 : (1 : Nat) * 2 ^ (192 + s) ≤ 1 * 2 ^ (192 + s + 1) :=
    Nat.mul_le_mul_left 1 (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  exact Nat.lt_of_lt_of_le h1 h2

/-- **The binade of the product.**  If the exact value in ticks is
`W * H * 2 ^ s` with `2 ^ 190 ≤ W * H < 2 ^ 192`, the binade is `190 + s`, or
`191 + s` when the product reaches `2 ^ 191`. -/
theorem binade_prod {W H P s : Nat} (hWlo : 2 ^ 63 ≤ W) (hWhi : W < 2 ^ 64)
    (hHlo : 2 ^ 127 ≤ H) (hHhi : H < 2 ^ 128) (hs : s < 1900)
    (hP : P = W * H * 2 ^ s) :
    binade P 1 = 190 + s + (if 2 ^ 191 ≤ W * H then 1 else 0) := by
  have hWHlo : 2 ^ 190 ≤ W * H := binade_lower_190 hWlo hHlo
  have hWHhi : W * H < 2 ^ 192 := binade_upper_192 hWhi hHhi
  have hex : ∃ B, B < 2100 ∧ P < 1 * 2 ^ (B + 1) := prod_exists hs hWHhi hP
  by_cases hcut : 2 ^ 191 ≤ W * H
  · have hlow : 1 * 2 ^ (191 + s) ≤ P := prod_lower hcut hP
    have hup : P < 1 * 2 ^ (192 + s) := prod_upper hWHhi hP
    have hupB : P < 1 * 2 ^ (191 + s + 1) := by
      rwa [← show 191 + s + 1 = 192 + s from by omega] at hup
    have h := binade_unique hex hlow hupB
    rw [h]
    have hc : (if 2 ^ 191 ≤ W * H then 1 else 0) = 1 := by simp [hcut]
    rw [hc]
    omega
  · have hWHlt : W * H < 2 ^ 191 := Nat.lt_of_not_le hcut
    have hlow : 1 * 2 ^ (190 + s) ≤ P := prod_lower hWHlo hP
    have hup : P < 1 * 2 ^ (191 + s) := prod_upper hWHlt hP
    have hupB : P < 1 * 2 ^ (190 + s + 1) := by
      rwa [← show 190 + s + 1 = 191 + s from by omega] at hup
    have h := binade_unique hex hlow hupB
    rw [h]
    have hc : (if 2 ^ 191 ≤ W * H then 1 else 0) = 0 := by simp [hcut]
    rw [hc, Nat.add_zero]

/-- A quotient at least `d * 2 ^ j`, scaled by `2 ^ s`, is at least
`d * 2 ^ (j + s)`. -/
theorem quot_lower {W d k P s j : Nat} (h : d * 2 ^ j ≤ W * 2 ^ k)
    (hP : P = W * 2 ^ (s + k)) : d * 2 ^ (j + s) ≤ P := by
  rw [hP]
  calc d * 2 ^ (j + s) = (d * 2 ^ j) * 2 ^ s := by rw [Nat.pow_add]; ac_rfl
    _ ≤ (W * 2 ^ k) * 2 ^ s := Nat.mul_le_mul_right _ h
    _ = W * 2 ^ (s + k) := by rw [Nat.pow_add]; ac_rfl

/-- Below `d * 2 ^ j`, scaled by `2 ^ s`, is below `d * 2 ^ (j + s)`. -/
theorem quot_upper {W d k P s j : Nat} (h : W * 2 ^ k < d * 2 ^ j)
    (hP : P = W * 2 ^ (s + k)) : P < d * 2 ^ (j + s) := by
  rw [hP]
  calc W * 2 ^ (s + k) = (W * 2 ^ k) * 2 ^ s := by rw [Nat.pow_add]; ac_rfl
    _ < (d * 2 ^ j) * 2 ^ s := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos s)
    _ = d * 2 ^ (j + s) := by rw [Nat.mul_assoc, ← Nat.pow_add]

/-- `W * 2 ^ k < d * 2 ^ 192`, from the row's bracket and `H + 1 ≤ 2 ^ 128`. -/
theorem quot_192 {W H d k : Nat} (hW : W < 2 ^ 64) (hH : H < 2 ^ 128)
    (hhi : 2 ^ k < d * (H + 1)) (hWpos : 0 < W) : W * 2 ^ k < d * 2 ^ 192 := by
  have hHle : H + 1 ≤ 2 ^ 128 := by omega
  have hWHle : W * (H + 1) ≤ 2 ^ 192 := by
    have h1 : W * (H + 1) ≤ (2 ^ 64 - 1) * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) hHle
    have h2 : (2 ^ 64 - 1) * 2 ^ 128 < 2 ^ 64 * 2 ^ 128 :=
      Nat.mul_lt_mul_of_pos_right (by omega : 2 ^ 64 - 1 < 2 ^ 64) (Nat.two_pow_pos 128)
    have h3 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 := by
      rw [show (192 : Nat) = 64 + 128 from rfl, Nat.pow_add]
    rw [h3]
    omega
  have h1 : W * 2 ^ k < W * (d * (H + 1)) :=
    Nat.mul_lt_mul_of_pos_left hhi hWpos
  have h2 : W * (d * (H + 1)) = d * (W * (H + 1)) := by ac_rfl
  have h3 : d * (W * (H + 1)) ≤ d * 2 ^ 192 := Nat.mul_le_mul_left d hWHle
  omega

/-- The binade search has an in-range witness for the quotient. -/
theorem quot_exists {W H d k P s : Nat} (hs : s < 1900) (hW : W < 2 ^ 64)
    (hH : H < 2 ^ 128) (hhi : 2 ^ k < d * (H + 1)) (hWpos : 0 < W)
    (hP : P = W * 2 ^ (s + k)) : ∃ B, B < 2100 ∧ P < d * 2 ^ (B + 1) := by
  refine ⟨192 + s, by omega, ?_⟩
  have hkup : W * 2 ^ k < d * 2 ^ 192 := quot_192 hW hH hhi hWpos
  have h1 : P < d * 2 ^ (192 + s) := quot_upper hkup hP
  have h2 : d * 2 ^ (192 + s) ≤ d * 2 ^ (192 + s + 1) :=
    Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  exact Nat.lt_of_lt_of_le h1 h2

/-- **The binade of the quotient.**  If `P = W * 2 ^ (s + k)` and the row
brackets `2 ^ k` between `d * H` and `d * (H + 1)`, the binade is `190 + s`, or
`191 + s` when `2 ^ 191 * d ≤ W * 2 ^ k`. -/
theorem binade_quot {W H d k P s : Nat} (hWlo : 2 ^ 63 ≤ W)
    (hWhi : W < 2 ^ 64) (hHlo : 2 ^ 127 ≤ H) (hHhi : H < 2 ^ 128)
    (hs : s < 1900) (hP : P = W * 2 ^ (s + k)) (hlo : d * H ≤ 2 ^ k)
    (hhi : 2 ^ k < d * (H + 1)) :
    binade P d = 190 + s + (if 2 ^ 191 * d ≤ W * 2 ^ k then 1 else 0) := by
  have hWpos : 0 < W := by omega
  have hex : ∃ B, B < 2100 ∧ P < d * 2 ^ (B + 1) :=
    quot_exists hs hWhi hHhi hhi hWpos hP
  by_cases hcut : 2 ^ 191 * d ≤ W * 2 ^ k
  · have hcut' : d * 2 ^ 191 ≤ W * 2 ^ k := by
      rw [Nat.mul_comm d (2 ^ 191)]
      exact hcut
    have hlow : d * 2 ^ (191 + s) ≤ P := quot_lower hcut' hP
    have hkup : W * 2 ^ k < d * 2 ^ 192 := quot_192 hWhi hHhi hhi hWpos
    have hup : P < d * 2 ^ (192 + s) := quot_upper hkup hP
    have hupB : P < d * 2 ^ (191 + s + 1) := by
      rwa [← show 191 + s + 1 = 192 + s from by omega] at hup
    have h := binade_unique hex hlow hupB
    rw [h]
    have hc : (if 2 ^ 191 * d ≤ W * 2 ^ k then 1 else 0) = 1 := by simp [hcut]
    rw [hc]
    omega
  · have hbase : d * 2 ^ 190 ≤ W * 2 ^ k := by
      have h1 : 2 ^ 190 ≤ W * H := binade_lower_190 hWlo hHlo
      calc d * 2 ^ 190 ≤ d * (W * H) := Nat.mul_le_mul_left d h1
        _ = W * (d * H) := by ac_rfl
        _ ≤ W * 2 ^ k := Nat.mul_le_mul_left W hlo
    have hlow : d * 2 ^ (190 + s) ≤ P := quot_lower hbase hP
    have hkup : W * 2 ^ k < d * 2 ^ 191 := by
      have h1 : W * 2 ^ k < 2 ^ 191 * d := Nat.lt_of_not_le hcut
      rwa [Nat.mul_comm (2 ^ 191) d] at h1
    have hup : P < d * 2 ^ (191 + s) := quot_upper hkup hP
    have hupB : P < d * 2 ^ (190 + s + 1) := by
      rwa [← show 190 + s + 1 = 191 + s from by omega] at hup
    have h := binade_unique hex hlow hupB
    rw [h]
    have hc : (if 2 ^ 191 * d ≤ W * 2 ^ k then 1 else 0) = 0 := by simp [hcut]
    rw [hc, Nat.add_zero]

/-! ### The tick-to-slice bridge

`elTier2Code` reads the product `W * (hi * 2 ^ 64 + lo)` through two 64-bit
halves; `valueTicks` holds the same value as the rational `P / d`, scaled by
`2 ^ s` with `s = 1074 + e - lz`.  The lemmas below are that bridge: the
product identity, the two shapes `valueTicks` takes, and the binade of the
exact value in the slice's own terms. -/

/-- For a row with no fraction the exact value is `W * (hi * 2 ^ 64 + lo)`
scaled by `2 ^ s`: `10 ^ q * 2 ^ 1074 = (hi * 2 ^ 64 + lo) * 2 ^ (1074 + e)`
and `W = w * 2 ^ lz`. -/
theorem valueTicks_nonneg {w : Nat} {q : Int} {t : EPow} {s : Nat}
    (hq : 0 ≤ q) (hrow : t.Row q)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) :
    (valueTicks w q).1 = Wnorm w * eH t * 2 ^ s := by
  obtain ⟨⟨hhi63, hhihi, hlolo⟩, ⟨he277, he22⟩, hfits, hneq, hneg, hnege⟩ := hrow
  have hqtn : (-q).toNat = 0 := Int.toNat_of_nonpos (by omega)
  have hne := hneq hq
  simp only [EPow.Neq, eD, hqtn, Nat.pow_zero, Nat.one_mul] at hne
  have hP : (valueTicks w q).1 = w * 10 ^ q.toNat * 2 ^ 1074 := by
    unfold valueTicks
    rw [ite_eq_left hq]
  rw [hP]
  by_cases he : 0 ≤ t.e
  · have hneg0 : (-t.e).toNat = 0 := Int.toNat_of_nonpos (by omega)
    have het : (t.e.toNat : Int) = t.e := Int.toNat_of_nonneg he
    simp only [eN, hneg0, Nat.pow_zero, Nat.mul_one] at hne
    have hslz : s + lz w = 1074 + t.e.toNat := by omega
    calc w * 10 ^ q.toNat * 2 ^ 1074
        = w * (eH t * 2 ^ t.e.toNat) * 2 ^ 1074 := by rw [hne]
      _ = w * eH t * 2 ^ (t.e.toNat + 1074) := by
            rw [Nat.pow_add]; ac_rfl
      _ = Wnorm w * eH t * 2 ^ s := by
            unfold Wnorm
            rw [show t.e.toNat + 1074 = lz w + s from by omega, Nat.pow_add]
            ac_rfl
  · have het0 : t.e.toNat = 0 := Int.toNat_of_nonpos (by omega)
    have hk : ((-t.e).toNat : Int) = -t.e := Int.toNat_of_nonneg (by omega)
    simp only [eN, het0, Nat.pow_zero, Nat.mul_one] at hne
    have hk1074 : (-t.e).toNat ≤ 1074 := by omega
    have hslz : 1074 - (-t.e).toNat = lz w + s := by omega
    calc w * 10 ^ q.toNat * 2 ^ 1074
        = w * 10 ^ q.toNat
            * (2 ^ (-t.e).toNat * 2 ^ (1074 - (-t.e).toNat)) := by
            rw [← Nat.pow_add,
              show (-t.e).toNat + (1074 - (-t.e).toNat) = 1074 from by omega]
      _ = w * (10 ^ q.toNat * 2 ^ (-t.e).toNat) * 2 ^ (1074 - (-t.e).toNat) := by
            ac_rfl
      _ = w * eH t * 2 ^ (1074 - (-t.e).toNat) := by rw [← hne]
      _ = Wnorm w * eH t * 2 ^ s := by
            unfold Wnorm
            rw [hslz, Nat.pow_add]
            ac_rfl

/-- The binade of the exact value, in the slice's own terms, for a row with no
fraction: `190 + s + [2 ^ 191 ≤ W * (hi * 2 ^ 64 + lo)]`. -/
theorem binade_valueTicks_nonneg {w : Nat} {q : Int} {t : EPow} {s : Nat}
    (hw0 : 0 < w) (hw : w < 2 ^ 64) (hq : 0 ≤ q) (hrow : t.Row q)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) (hsl : s < 1900) :
    binade (valueTicks w q).1 (valueTicks w q).2 =
      190 + s + (if 2 ^ 191 ≤ Wnorm w * eH t then 1 else 0) := by
  have hP := valueTicks_nonneg hq hrow hs
  have hd : (valueTicks w q).2 = 1 := by
    unfold valueTicks
    rw [ite_eq_left hq]
  rw [hd, hP]
  exact binade_prod (Wnorm_lower hw0 hw) (Wnorm_upper hw0 hw)
    (eH_lower hrow.1.1) (eH_upper hrow.1.2.1 hrow.1.2.2) hsl rfl

/-- The binade of the exact value for a truncated row (`q < 0`): the value is
`w * 2 ^ 1074` over `10 ^ (-q)` and the product `W * 2 ^ (-e)` stands against
`10 ^ (-q) * (hi * 2 ^ 64 + lo)`, so the binade's location is the comparison
`2 ^ 191 * 10 ^ (-q) ≤ W * 2 ^ (-e)`. -/
theorem binade_valueTicks_neg {w : Nat} {q : Int} {t : EPow} {s : Nat}
    (hw0 : 0 < w) (hw : w < 2 ^ 64) (hq : q < 0) (hrow : t.Row q)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) (hsl : s < 1900) :
    binade (valueTicks w q).1 (valueTicks w q).2 =
      190 + s +
        (if 2 ^ 191 * 10 ^ (-q).toNat ≤ Wnorm w * 2 ^ (-t.e).toNat then 1 else 0) := by
  obtain ⟨⟨hhi63, hhihi, hlolo⟩, ⟨he277, he22⟩, hfits, hneq, hneg, hnege⟩ := hrow
  have heneg : t.e < 0 := hnege hq
  have hqnn : ¬ (0 ≤ q) := by omega
  have hqt0 : q.toNat = 0 := Int.toNat_of_nonpos (by omega)
  have het0 : t.e.toNat = 0 := Int.toNat_of_nonpos (by omega)
  have hqabs : q.natAbs = (-q).toNat := by omega
  have hP1 : (valueTicks w q).1 = w * 2 ^ 1074 := by
    unfold valueTicks
    rw [ite_eq_right hqnn]
  have hP2 : (valueTicks w q).2 = 10 ^ (-q).toNat := by
    unfold valueTicks
    rw [ite_eq_right hqnn, hqabs]
  have hfit' : eH t = 2 ^ (-t.e).toNat / 10 ^ (-q).toNat := by
    have h := hfits
    simp only [EPow.Fits, eN, eD, hqt0, het0, Nat.pow_zero, Nat.one_mul, Nat.mul_one] at h
    exact h
  have hdpos : 0 < 10 ^ (-q).toNat := Nat.pow_pos (by decide)
  have hlo : 10 ^ (-q).toNat * eH t ≤ 2 ^ (-t.e).toNat := by
    rw [hfit', Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hhi : 2 ^ (-t.e).toNat < 10 ^ (-q).toNat * (eH t + 1) := by
    rw [hfit']
    have hdec := Nat.div_add_mod (2 ^ (-t.e).toNat) (10 ^ (-q).toNat)
    have hmod := Nat.mod_lt (2 ^ (-t.e).toNat) hdpos
    have h1 : 10 ^ (-q).toNat * (2 ^ (-t.e).toNat / 10 ^ (-q).toNat)
          + 2 ^ (-t.e).toNat % 10 ^ (-q).toNat
        < 10 ^ (-q).toNat * (2 ^ (-t.e).toNat / 10 ^ (-q).toNat)
          + 10 ^ (-q).toNat :=
      Nat.add_lt_add_left hmod _
    rw [hdec] at h1
    rwa [show 10 ^ (-q).toNat * (2 ^ (-t.e).toNat / 10 ^ (-q).toNat)
          + 10 ^ (-q).toNat
        = 10 ^ (-q).toNat * (2 ^ (-t.e).toNat / 10 ^ (-q).toNat + 1) from by
          rw [Nat.mul_add, Nat.mul_one]] at h1
  have hslz : (s : Int) + (-t.e).toNat + (lz w : Int) = 1074 := by omega
  have hslz' : (s : Nat) + (-t.e).toNat + lz w = 1074 := by omega
  have hP : (valueTicks w q).1 = Wnorm w * 2 ^ (s + (-t.e).toNat) := by
    rw [hP1]
    unfold Wnorm
    rw [show (1074 : Nat) = lz w + (s + (-t.e).toNat) from by omega, Nat.pow_add]
    ac_rfl
  rw [hP2]
  exact binade_quot (W := Wnorm w) (H := eH t) (d := 10 ^ (-q).toNat)
    (k := (-t.e).toNat) (P := (valueTicks w q).1) (s := s)
    (Wnorm_lower hw0 hw) (Wnorm_upper hw0 hw)
    (eH_lower hhi63) (eH_upper hhihi hlolo) hsl hP hlo hhi

/-! ### The tie at the window's edge

At `hp = hh` the product sits exactly half an ulp above the grid point `m`:
`(2 * m + 1) * 2 ^ (sh + 127)` is that midpoint in the product's scale, and
the difference from it is exactly the discarded part `Rlo * 2 ^ 64 + L + g`.
So the exact tie is the vanishing of those three words, and the emitted
`up = 1` at an exact tie is `hp > hh` false and `m % 2 = 1` true — the
round-to-even choice. -/

theorem tie_midpoint {sh m : Nat} (hsh : 1 ≤ sh) :
    (2 ^ sh * m + 2 ^ (sh - 1)) * 2 ^ 128 = (2 * m + 1) * 2 ^ (sh + 127) := by
  have h1 : 2 ^ (sh + 127) = 2 ^ (sh - 1) * 2 ^ 128 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h2 : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
    have h3 : sh = (sh - 1) + 1 := by omega
    calc 2 ^ sh = 2 ^ ((sh - 1) + 1) := congrArg (fun x => 2 ^ x) h3
      _ = 2 ^ (sh - 1) * 2 := by rw [Nat.pow_add, Nat.pow_one]
  rw [h1, h2]
  simp only [Nat.add_mul, Nat.one_mul]
  ac_rfl

/-- **The window's edge.**  With `hp = hh` (`hh = 2 ^ (9 + ub)`, `sh = 10 + ub`)
the product is the midpoint between `m` and `m + 1` at its own scale, plus the
discarded part. -/
theorem tie_edge {W hi lo m ub : Nat} (hW : W < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (hlo : lo < 2 ^ 64)
    (hm : m = exactRhi W hi lo / 2 ^ (10 + ub))
    (hpH : exactRhi W hi lo % 2 ^ (10 + ub) = 2 ^ (9 + ub)) :
    W * (hi * 2 ^ 64 + lo) =
      (2 * m + 1) * 2 ^ (10 + ub + 127) +
        (exactRlo W hi lo * 2 ^ 64 + lo64 W lo) := by
  have hsplit := exact_split hW hhi hlo
  have hdec := Nat.div_add_mod (exactRhi W hi lo) (2 ^ (10 + ub))
  rw [← hm] at hdec
  rw [hpH] at hdec
  have hsh : (2 : Nat) ^ (9 + ub) = 2 ^ (10 + ub - 1) := by
    congr 1
    omega
  rw [hsplit, ← hdec, hsh, ← tie_midpoint (sh := 10 + ub) (m := m) (by omega)]
  rw [Nat.add_assoc]

/-- `M + X = M` leaves `X = 0`. -/
theorem add_eq_left_zero {M X : Nat} (h : M + X = M) : X = 0 := by
  have h' : M + X = M + 0 := by rw [Nat.add_zero]; exact h
  exact Nat.add_left_cancel h'

/-- **The tie rule.**  At the window's edge the exact value is the midpoint
exactly when the high half's low word, the low half's low word and the table's
fractional product `g` all vanish; otherwise it is strictly above it.  (`g` is
`W` times the row's fraction, so `g < 2 ^ 64`, and `g = 0` exactly for the rows
with no fraction — `q ≥ 0`.  This is why the guard refuses a zero low word at
`hp = hh` only when `q < 0`.) -/
theorem tie_exact_iff {W hi lo g m ub : Nat} (hW : W < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (hlo : lo < 2 ^ 64)
    (hm : m = exactRhi W hi lo / 2 ^ (10 + ub))
    (hpH : exactRhi W hi lo % 2 ^ (10 + ub) = 2 ^ (9 + ub)) :
    (W * (hi * 2 ^ 64 + lo) + g = (2 * m + 1) * 2 ^ (10 + ub + 127)) ↔
      exactRlo W hi lo = 0 ∧ lo64 W lo = 0 ∧ g = 0 := by
  have h := tie_edge hW hhi hlo hm hpH
  constructor
  · intro he
    rw [h] at he
    rw [Nat.add_assoc] at he
    have h0 : exactRlo W hi lo * 2 ^ 64 + lo64 W lo + g = 0 := add_eq_left_zero he
    obtain ⟨hAL, hg⟩ := Nat.add_eq_zero_iff.mp h0
    obtain ⟨hA, hL⟩ := Nat.add_eq_zero_iff.mp hAL
    refine ⟨?_, hL, hg⟩
    rcases Nat.eq_zero_or_pos (exactRlo W hi lo) with h' | h'
    · exact h'
    · exfalso
      have hpos : 0 < exactRlo W hi lo * 2 ^ 64 := Nat.mul_pos h' (Nat.two_pow_pos 64)
      omega
  · rintro ⟨h1, h2, h3⟩
    rw [h, h1, h2, h3]
    simp


/-! ### Axiom footprint

Every declaration is pinned.  The statement is computable, and the arithmetic
stays at the standard footprint: `omega` closes linear arithmetic without
`Classical.choice` when the goal does not need it, and `decide`-free rewriting
adds nothing.

Four declarations carry `Classical.choice`, and they are named here rather than
left to be discovered: `binade_prod`, `binade_quot`,
`binade_valueTicks_nonneg` and `binade_valueTicks_neg`.  The ingredients are all
at the standard footprint — `binade_unique`, `prod_lower`, `prod_upper`,
`prod_exists`, `quot_lower`, `quot_upper`, `quot_192`, `quot_exists` and
`valueTicks_nonneg` — so the choice enters in the composed presentation of the
threshold (`2 ^ 191 ≤ W * H`, or `2 ^ 191 * d ≤ W * 2 ^ k`), not in any table
row, product identity or value identity. -/

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
#print axioms LeanLLVM.ElGuardRefine.epow_rows
#print axioms LeanLLVM.ElGuardRefine.rowB_row
#print axioms LeanLLVM.ElGuardRefine.row_of_epowAt
#print axioms LeanLLVM.ElGuardRefine.hi64_add_lo64
#print axioms LeanLLVM.ElGuardRefine.word_add
#print axioms LeanLLVM.ElGuardRefine.exact_split
#print axioms LeanLLVM.ElGuardRefine.rem_lt_half_full
#print axioms LeanLLVM.ElGuardRefine.half_le_rem_full
#print axioms LeanLLVM.ElGuardRefine.pow_log2_le
#print axioms LeanLLVM.ElGuardRefine.lt_pow_log2_succ
#print axioms LeanLLVM.ElGuardRefine.log2_lt_of_lt_pow
#print axioms LeanLLVM.ElGuardRefine.lz_le_63
#print axioms LeanLLVM.ElGuardRefine.Wnorm_lower
#print axioms LeanLLVM.ElGuardRefine.Wnorm_upper
#print axioms LeanLLVM.ElGuardRefine.eH_lower
#print axioms LeanLLVM.ElGuardRefine.eH_upper
#print axioms LeanLLVM.ElGuardRefine.binade_unique
#print axioms LeanLLVM.ElGuardRefine.add_eq_left_zero
#print axioms LeanLLVM.ElGuardRefine.binade_lower_190
#print axioms LeanLLVM.ElGuardRefine.binade_upper_192
#print axioms LeanLLVM.ElGuardRefine.prod_lower
#print axioms LeanLLVM.ElGuardRefine.prod_upper
#print axioms LeanLLVM.ElGuardRefine.prod_exists
#print axioms LeanLLVM.ElGuardRefine.quot_lower
#print axioms LeanLLVM.ElGuardRefine.quot_upper
#print axioms LeanLLVM.ElGuardRefine.quot_192
#print axioms LeanLLVM.ElGuardRefine.quot_exists
#print axioms LeanLLVM.ElGuardRefine.binade_prod
#print axioms LeanLLVM.ElGuardRefine.binade_quot
#print axioms LeanLLVM.ElGuardRefine.valueTicks_nonneg
#print axioms LeanLLVM.ElGuardRefine.binade_valueTicks_nonneg
#print axioms LeanLLVM.ElGuardRefine.binade_valueTicks_neg
#print axioms LeanLLVM.ElGuardRefine.tie_midpoint
#print axioms LeanLLVM.ElGuardRefine.tie_edge
#print axioms LeanLLVM.ElGuardRefine.tie_exact_iff

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
