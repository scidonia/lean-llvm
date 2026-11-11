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

It proves the obligation, `elGuardRefinesOn`: `0 < w → w < 2 ^ 64 →
elTier2Code w q = some c → roundMag (valueTicks w q).1 (valueTicks w q).2 =
.fin c`.  The word bound is the emitted `uint64_t w`, and the unbounded reading
is refuted (`not_elGuardRefinesUnbounded`), so the boundary is written down
rather than left to an absent hypothesis.  The significand itself — that
`roundMag`'s `sig` (or its successor, on a round-up) is the emitted `m`, which
is `normalCode`'s two comparisons of the remainder against the ulp — rests on
three pieces, proved below:

* the division identity: `quot_split` reads the high word's own slice and
  `quot_residue_neg` bounds what lies below it; `sig_eq_m_nonneg` and
  `sig_eq_m_neg` put `P / (d * ulp)` at `Rhi / 2 ^ sh` for the two signs of
  `q`.  `upDec` and `normalCode_eq_form` rewrite the specification's answer as
  the pack `el_pack` builds, and `decomp_nonneg` / `decomp_neg` with
  `half_lt`/`half_gt`/`half_eq`/`half_le` and `mod_lt_half`/`mod_gt_half`/
  `mod_eq_half` turn the remainder comparison back into the slice's `hp`;
* the denominator-scaled form for `q < 0`: `decomp_neg` carries `W * R` in the
  remainder, and `at_edge_scaled`, `close_shift` and `below_far_scaled` (with
  the nonnegative `above_far`, `at_edge`, `below_close`, `below_far`) state the
  tie and the `hp = hh - 1` case as `D * M + W * R` against `D * 2 ^ 128`;
* the low half's carry: `rhi_le_of_ub_zero` shows the window excludes
  `Rhi = 2 ^ 63 - 1`, `bit_one` and `bit_zero` identify the rebuilt word's
  binade bit, and `pack_carry_agrees` shows that in the carry case
  `elPack`'s `ov` supplies exactly the exponent the slice's missing `ub` would
  have supplied while its significand wraps to the same `2 ^ 52`.

The emitted body is factored as `elCore`/`elInner`/`elFar`, with
`elTier2Code_reduce` the definitional unfolding, so a branch can be reasoned
about without inlining the whole term, and the identity is `elGuardRefinesOn`
at the end of the module.  Both branches end in `code_agree`: the significand
is the slice's `m` and the exponent's carry `ov` is the specification's own
carry over `2 ^ 53`.  In the window the rebuilt slice is read from `Rhi`, so
its `ub` is the binade bit (`bit_one`/`bit_zero`, with `rhi_le_of_ub_zero`
excluding the one word the window cannot reach), and the round-up comes from
comparing the remainder `T` with the half `T'` through
`decomp_nonneg`/`decomp_neg` (`upDec_zero_of_T_lt`, `upDec_one_of_T_gt`,
`upDec_par_of_T_eq`), with `below_far`/`below_close`/`at_edge`/`above_far` and
their scaled forms giving the four `hp` cases.  The far branch reads the first
slice, so its `m` and `hp` can be one step behind the rebuilt word's
(`Tgt_neg`, `Tlt3_neg_above`, `Tlt3_neg_full`); `mm_zero`/`mm_succ` carry the
comparison across that step, and `mm_of_T_between` is the case where the
remainder has already wrapped past a whole unit.  `pack_carry_agrees` is the
one place the guard's `ub` is one behind the binade bit, and `elPack`'s `ov`
supplies the difference.  No step needs a choice: every declaration is at
`[propext, Quot.sound]`.

The range cases are not refinement cases, and they are empty on both sides.
`roundMag_eq_normalCode` puts every value the guard sees inside the normal
lattice: the table's largest power of ten is below `2 ^ 150`, so `w * 10 ^ q`
lies between `10 ^ -45` and `2 ^ 214`, and the tick value between `2 ^ 1074` and
`2 ^ 1288` — above the subnormal lattice and below the overflow threshold.  So
the specification never answers `.inf` and never takes the subnormal branch:
overflow to infinity and underflow to zero are unreachable from these inputs
rather than refusals to be matched.  The guard's own range test cannot refuse
either (`elPack_range`): the slice's `ub` is at most one and its significand at
most `2 ^ 53` (`hi64_lt`, `exactRhi_lt`, `slice_le`), which puts
`eu = 180 + sh + e - lz` in `[-150, 214]`, inside `[-1022, 1023]`.  The only
refusal left is the `q < 0` tie, and a hypothesis `elTier2Code w q = some c`
excludes it by construction.

A sample over the narrowed domain agreed with `roundMag` on every pair: the
mantissas were `0, 1, 2, 7, 34, 1023, 2 ^ 52 - 1, 2 ^ 52, 2 ^ 52 + 1, 10 ^ 17,
10 ^ 18, 10 ^ 19 - 1, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64 - 2,
3 * 2 ^ 62 + 12345, 2 ^ 62 + 7, 1234567890123456789, 9999999999999999999`,
together with `(k * 6364136223846793005 + 1442695040888963407) % 2 ^ 64` and
`((k * 2862933555777941757 + 3037000493) % 2 ^ 53) * 2 ^ 11 + 513` for
`k < 60`, against all 91 exponents — 12831 pairs, every one decided.  That is a
measurement over a sample, not a proof, and it does not stand in for the three
pieces above.

The table check is kernel evaluation over the ninety-one rows, so a proof of the
obligation at a symbolic `q` reads the row's facts through `row_of_epowAt`
rather than splitting on `q`.  `#eval` at the end reproduces the emitted
kernel's own output on the boundary witnesses, so the definitions are the
emitted test rather than a paraphrase of it.
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

/-- **The obligation**: on every `(w, q)` the guard decides, with `w` a
sixty-four-bit mantissa as the emitted kernel's `uint64_t` parameter, the fields
it returns are `roundMag`'s magnitude for the exact value.

The word bound is the emitted interface's, not a convenience: `num_el_el1` takes
`uint64_t w`, and `Wnorm`'s two bounds, `exact_split`'s no-wrap argument and the
whole slice reading are stated for a sixty-four-bit word.  The unbounded reading
is `ElGuardRefinesUnbounded`, and it is false
(`not_elGuardRefinesUnbounded`). -/
def ElGuardRefinesOn : Prop :=
  ∀ (w : Nat) (q : Int) (c : Code), 0 < w → w < 2 ^ 64 →
    elTier2Code w q = some c →
      roundMag (valueTicks w q).1 (valueTicks w q).2 = .fin c

/-- The same obligation with no word bound: every `Nat` mantissa.  There the
guard's "sixty-four-bit words" are not words, and the statement fails. -/
def ElGuardRefinesUnbounded : Prop :=
  ∀ (w : Nat) (q : Int) (c : Code), elTier2Code w q = some c →
    roundMag (valueTicks w q).1 (valueTicks w q).2 = .fin c

/- The witness's `roundMag` needs the overflow threshold `2 ^ 2098` and the
binade search's two thousand finder steps, so evaluation runs with the exponent
and recursion limits raised. -/
set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2200 in
/-- **The word bound is load-bearing.**  At `w = 2 ^ 66` the slice is read from
`Ahi = W * hi / 2 ^ 64 = 2 ^ 65`, a sixty-six-bit "word", so `ub = 4` and the
slice is cut at `2 ^ 14` instead of `2 ^ 10`.  The guard still decides — it
emits `⟨1090, 2 ^ 52 + 2 ^ 51⟩`, whose value is `1.5 · 2 ^ 67` — while the exact
value `2 ^ 66` is `⟨1089, 2 ^ 52⟩`.  So the domain is the kernel's, and the
omission of the bound is not harmless: the two magnitudes differ by a factor of
three. -/
theorem not_elGuardRefinesUnbounded : ¬ ElGuardRefinesUnbounded := by
  intro h
  have hg : elTier2Code (2 ^ 66) 0 = some ⟨1090, 2 ^ 52 + 2 ^ 51⟩ := by decide
  have hs : roundMag (valueTicks (2 ^ 66) 0).1 (valueTicks (2 ^ 66) 0).2 =
      .fin ⟨1089, 2 ^ 52⟩ := by
    decide
  have hbad := h (2 ^ 66) 0 ⟨1090, 2 ^ 52 + 2 ^ 51⟩ hg
  rw [hs] at hbad
  have hE : (1089 : Nat) = 1090 := congrArg Code.expField (Mag.fin.inj hbad)
  exact absurd hE (by decide)

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

/-- A product of two sixty-four-bit words has a sixty-four-bit high word: the
quotient is below `2 ^ 64` because the product is below `2 ^ 128`. -/
theorem hi64_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : hi64 a b < 2 ^ 64 := by
  unfold hi64
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  have h1 : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_lt_mul_of_lt_of_le (by omega : 2 ^ 64 - 1 < 2 ^ 64)
      (by omega : 2 ^ 64 - 1 ≤ 2 ^ 64) (by decide)
  exact Nat.lt_of_le_of_lt h1 h2

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
  have hc : hi64 W lo < 2 ^ 64 := hi64_lt hW hlo
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

/-! The search's index arithmetic, stated away from any existential hypothesis.

`ω` builds its atom list out of the whole local context, and a context holding
`∃ B, …` puts `Exists.choose` in that list: `choose` is `Classical.choose`, so
an `ω` call made beside an existential hypothesis carries `Classical.choice`.
These three identities are the only arithmetic the two compositional binade
theorems need, so they are proved here — where no existential is in scope — and
applied by rewriting. -/

/-- `191 + s + 1` is the search's next index, `192 + s`. -/
theorem idx191 (s : Nat) : 191 + s + 1 = 192 + s := by omega

/-- `190 + s + 1` is the search's next index, `191 + s`. -/
theorem idx190 (s : Nat) : 190 + s + 1 = 191 + s := by omega

/-- `191 + s` is `190 + s + 1`: the unit added at the top of the binade. -/
theorem idx190_succ (s : Nat) : 191 + s = 190 + s + 1 := by omega

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
      rw [idx191]
      exact hup
    have h := binade_unique hex hlow hupB
    rw [h]
    have hc : (if 2 ^ 191 ≤ W * H then 1 else 0) = 1 := by simp [hcut]
    rw [hc]
    exact idx190_succ s
  · have hWHlt : W * H < 2 ^ 191 := Nat.lt_of_not_le hcut
    have hlow : 1 * 2 ^ (190 + s) ≤ P := prod_lower hWHlo hP
    have hup : P < 1 * 2 ^ (191 + s) := prod_upper hWHlt hP
    have hupB : P < 1 * 2 ^ (190 + s + 1) := by
      rw [idx190]
      exact hup
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
      rw [idx191]
      exact hup
    have h := binade_unique hex hlow hupB
    rw [h]
    have hc : (if 2 ^ 191 * d ≤ W * 2 ^ k then 1 else 0) = 1 := by simp [hcut]
    rw [hc]
    exact idx190_succ s
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
      rw [idx190]
      exact hup
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


/-! ### The specification never leaves the normal lattice

`roundMag` answers `.inf` at or above `overflowTicks = 2 ^ 2098 - 2 ^ 2044` and
takes the subnormal branch below `2 ^ 52` ticks.  For a row of this table and a
sixty-four-bit mantissa neither branch is reachable: `10 ^ q` for `q ≤ 45` is
below `2 ^ 150`, so the value `w * 10 ^ q` lies between `10 ^ -45` and
`2 ^ 214`, which in ticks is between `2 ^ 1074` and `2 ^ 1288` — `2 ^ 1022`
above the subnormal lattice, and below `2 ^ 2097 ≤ overflowTicks` by a factor of
at least `2 ^ 809`.  So the answer is always `normalCode`'s, and the
obligation's only remaining content is the significand. -/

/-- An exponent inside the table: `epowAt` splits on exactly that condition. -/
theorem epowAt_bounds {q : Int} {t : EPow} (h : epowAt q = some t) :
    -45 ≤ q ∧ q ≤ 45 := by
  unfold epowAt at h
  split at h
  · exact ‹-45 ≤ q ∧ q ≤ 45›
  · exact absurd h (by simp)

/-- `10 ^ 45 < 2 ^ 150`: the table's largest power of ten, and the bound the
value estimates below rest on. -/
theorem pow10_45_lt : (10 : Nat) ^ 45 < 2 ^ 150 := by decide

/-- The rebuilt high word is a sixty-four-bit word: it is below the product's
own high word, and the product is below `2 ^ 192`. -/
theorem exactRhi_lt {W hi lo : Nat} (hW : W < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (hlo : lo < 2 ^ 64) : exactRhi W hi lo < 2 ^ 64 := by
  have hsplit := exact_split hW hhi hlo
  have hX : hi * 2 ^ 64 + lo < 2 ^ 128 := by
    have h1 : hi * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 := by
      rw [Nat.sub_mul, Nat.one_mul, ← pow64_128]
    omega
  have hWH : W * (hi * 2 ^ 64 + lo) < 2 ^ 64 * 2 ^ 128 :=
    Nat.mul_lt_mul_of_le_of_lt (by omega) hX (Nat.two_pow_pos 64)
  have hle : exactRhi W hi lo * 2 ^ 128 ≤ W * (hi * 2 ^ 64 + lo) := by
    rw [hsplit]
    exact Nat.le_trans
      (Nat.le_add_right (exactRhi W hi lo * 2 ^ 128) (exactRlo W hi lo * 2 ^ 64))
      (Nat.le_add_right (exactRhi W hi lo * 2 ^ 128 + exactRlo W hi lo * 2 ^ 64)
        (lo64 W lo))
  have hlt : exactRhi W hi lo * 2 ^ 128 < 2 ^ 64 * 2 ^ 128 :=
    Nat.lt_of_le_of_lt hle hWH
  exact lt_of_mul_lt_mul_right hlt

/-- **The slice's significand is at most `2 ^ 53`.**  For any word `A` below
`2 ^ 64`, the guard's `m = A / 2 ^ (10 + A / 2 ^ 63)` is at most `2 ^ 53`:
`A / 2 ^ 63` is the word's top bit, so the cut is `2 ^ 10` on a word below
`2 ^ 63` and `2 ^ 11` on one that reaches it. -/
theorem slice_le {A : Nat} (hA : A < 2 ^ 64) : A / 2 ^ (10 + A / 2 ^ 63) ≤ 2 ^ 53 := by
  have hub2 : A / 2 ^ 63 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    have h2 : (2 : Nat) * 2 ^ 63 = 2 ^ 64 := by rw [Nat.mul_comm, ← Nat.pow_succ]
    omega
  have hub : A / 2 ^ 63 ≤ 1 := by omega
  rcases Nat.lt_or_ge (A / 2 ^ 63) 1 with h0 | h1
  · have hz : A / 2 ^ 63 = 0 := by omega
    have hlt : A < 2 ^ 63 := by
      have hlt1 : A / 2 ^ 63 < 1 := by omega
      rw [Nat.div_lt_iff_lt_mul (by decide)] at hlt1
      simpa using hlt1
    rw [hz, Nat.add_zero]
    have hstep : A / 2 ^ 10 < 2 ^ 53 + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have h2 : (2 ^ 53 + 1) * 2 ^ 10 = 2 ^ 63 + 2 ^ 10 := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add]
      omega
    omega
  · have hone : A / 2 ^ 63 = 1 := by omega
    rw [hone]
    have hstep : A / 2 ^ 11 < 2 ^ 53 + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have h2 : (2 ^ 53 + 1) * 2 ^ 11 = 2 ^ 64 + 2 ^ 11 := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add]
      omega
    omega

/-- The `Ahi`-without-the-carry case is reachable, not hypothetical: at
`q = -43` and `w = 16543612251060553498` the guard's slice is cut from
`2 ^ 63 - 1` — so its `ub` is `0` and `sh` is `10` — while the low half carries
the rebuilt word to `2 ^ 63`, whose top bit is `1`.  The true binade bit is the
rebuilt word's, so the branch reads the wrong `ub`; `el_pack`'s `ov` is what
keeps the emitted code right there. -/
theorem carry_case_reachable :
    (match epowAt (-43) with
      | some t =>
          hi64 (Wnorm 16543612251060553498) t.hi = 2 ^ 63 - 1 &&
            exactRhi (Wnorm 16543612251060553498) t.hi t.lo = 2 ^ 63
      | none => false) = true := by decide

set_option exponentiation.threshold 2200 in
/-- `2 ^ 2097 ≤ overflowTicks`: the threshold is more than half of `2 ^ 2098`,
which is all the overflow bound needs. -/
theorem overflowTicks_ge : (2 : Nat) ^ 2097 ≤ overflowTicks := by
  unfold overflowTicks
  decide

set_option exponentiation.threshold 1300 in
/-- **The specification stays in the normal lattice.**  With a sixty-four-bit
mantissa and an exponent the table has a row for, `roundMag` takes neither the
overflow nor the subnormal branch, so its answer is `normalCode`'s. -/
theorem roundMag_eq_normalCode {w : Nat} {q : Int} {t : EPow}
    (hw0 : 0 < w) (hw : w < 2 ^ 64) (hq : epowAt q = some t) :
    roundMag (valueTicks w q).1 (valueTicks w q).2 =
      .fin (normalCode (valueTicks w q).1 (valueTicks w q).2) := by
  obtain ⟨hqlo, hqhi⟩ := epowAt_bounds hq
  have h10pow : ∀ n : Nat, n ≤ 45 → 10 ^ n < 2 ^ 150 := fun n hn =>
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hn) pow10_45_lt
  have h10pos : ∀ n : Nat, 1 ≤ 10 ^ n := fun n =>
    Nat.succ_le_of_lt (Nat.pow_pos (by decide))
  have hw1 : 1 ≤ w := hw0
  have h1288 : (2 : Nat) ^ 1288 < 2 ^ 2097 := two_pow_lt_of_lt (by decide)
  have h1138 : (2 : Nat) ^ 1138 < 2 ^ 2097 := two_pow_lt_of_lt (by decide)
  have h202 : (2 : Nat) ^ 202 < 2 ^ 1074 := two_pow_lt_of_lt (by decide)
  by_cases hq0 : 0 ≤ q
  · have hqn : q.toNat ≤ 45 := by
      have hcast : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
      omega
    have hP : (valueTicks w q).1 = w * 10 ^ q.toNat * 2 ^ 1074 := by
      unfold valueTicks
      rw [ite_eq_left hq0]
    have hd : (valueTicks w q).2 = 1 := by
      unfold valueTicks
      rw [ite_eq_left hq0]
    have hPlt : (valueTicks w q).1 < overflowTicks := by
      rw [hP]
      have h1 : w * 10 ^ q.toNat < 2 ^ 64 * 2 ^ 150 := by
        calc w * 10 ^ q.toNat < 2 ^ 64 * 10 ^ q.toNat :=
              Nat.mul_lt_mul_of_pos_right hw (Nat.pow_pos (by decide))
          _ < 2 ^ 64 * 2 ^ 150 :=
              Nat.mul_lt_mul_of_pos_left (h10pow _ hqn) (two_pow_pos 64)
      have h2 : w * 10 ^ q.toNat * 2 ^ 1074 < 2 ^ 64 * 2 ^ 150 * 2 ^ 1074 :=
        Nat.mul_lt_mul_of_pos_right h1 (two_pow_pos 1074)
      have h3 : (2 : Nat) ^ 64 * 2 ^ 150 * 2 ^ 1074 = 2 ^ 1288 := by
        rw [← Nat.pow_add, ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le (h3 ▸ h2)
        (Nat.le_trans (Nat.le_of_lt h1288) overflowTicks_ge)
    have hPge : 2 ^ 1074 ≤ (valueTicks w q).1 := by
      rw [hP]
      calc (2 : Nat) ^ 1074 = 1 * 1 * 2 ^ 1074 := by rw [Nat.one_mul]
        _ ≤ w * 10 ^ q.toNat * 2 ^ 1074 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hw1 (h10pos _))
    rw [hd]
    have h1 : ¬ (overflowTicks * 1 ≤ (valueTicks w q).1) := by
      rw [Nat.mul_one]
      exact Nat.not_le.mpr hPlt
    have h2 : ¬ ((valueTicks w q).1 < 1 * 2 ^ 52) := by
      rw [Nat.one_mul]
      exact Nat.not_lt.mpr (Nat.le_trans (two_pow_le_iff.mpr (by decide)) hPge)
    unfold roundMag
    rw [ite_eq_right h1, ite_eq_right h2]
  · have habs : q.natAbs = (-q).toNat := by omega
    have hqn : (-q).toNat ≤ 45 := by
      have hcast : (((-q).toNat : Nat) : Int) = -q := Int.toNat_of_nonneg (by omega)
      omega
    have hP : (valueTicks w q).1 = w * 2 ^ 1074 := by
      unfold valueTicks
      rw [ite_eq_right hq0]
    have hd : (valueTicks w q).2 = 10 ^ (-q).toNat := by
      unfold valueTicks
      rw [ite_eq_right hq0, habs]
    have hPle : (valueTicks w q).1 ≤ 2 ^ 64 * 2 ^ 1074 := by
      rw [hP]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hw)
    have hPge : 2 ^ 1074 ≤ (valueTicks w q).1 := by
      rw [hP]
      calc (2 : Nat) ^ 1074 = 1 * 2 ^ 1074 := (Nat.one_mul _).symm
        _ ≤ w * 2 ^ 1074 := Nat.mul_le_mul_right _ hw1
    rw [hd]
    have hPlt : (valueTicks w q).1 < overflowTicks * 10 ^ (-q).toNat := by
      have h1 : (2 : Nat) ^ 64 * 2 ^ 1074 = 2 ^ 1138 := by rw [← Nat.pow_add]
      have h3 : (valueTicks w q).1 < 2 ^ 1138 := by
        have h4 : (valueTicks w q).1 < 2 ^ 64 * 2 ^ 1074 := by
          rw [hP]
          exact Nat.mul_lt_mul_of_pos_right hw (two_pow_pos 1074)
        exact h1 ▸ h4
      have h2 : overflowTicks ≤ overflowTicks * 10 ^ (-q).toNat := by
        simpa using Nat.mul_le_mul_left overflowTicks (h10pos (-q).toNat)
      exact Nat.lt_of_lt_of_le h3
        (Nat.le_trans (Nat.le_of_lt h1138) (Nat.le_trans overflowTicks_ge h2))
    have hsub : 10 ^ (-q).toNat * 2 ^ 52 < 2 ^ 1074 := by
      have h2 : (2 : Nat) ^ 150 * 2 ^ 52 = 2 ^ 202 := by rw [← Nat.pow_add]
      have h3 : 10 ^ (-q).toNat * 2 ^ 52 < 2 ^ 150 * 2 ^ 52 :=
        Nat.mul_lt_mul_of_pos_right (h10pow _ hqn) (two_pow_pos 52)
      exact Nat.lt_of_lt_of_le (h2 ▸ h3) (Nat.le_of_lt h202)
    have h1 : ¬ (overflowTicks * 10 ^ (-q).toNat ≤ (valueTicks w q).1) :=
      Nat.not_le.mpr hPlt
    have h2 : ¬ ((valueTicks w q).1 < 10 ^ (-q).toNat * 2 ^ 52) :=
      Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_lt hsub) hPge)
    unfold roundMag
    rw [ite_eq_right h1, ite_eq_right h2]

/-- **`el_pack`'s exponent test never refuses on the guard's inputs.**  The
significand is at most `2 ^ 53` before the round-up (`m ≤ 2 ^ 53`, `up ≤ 1`), so
it is at most `2 ^ 53 + 1` after it and `ov = mm / 2 ^ 53 ≤ 1`; the slice word
`ub ≤ 1`, so `sh = 10 + ub + ov ≤ 12`.  With a row exponent in `[-277, 22]` and
a normalising shift at most `63`, `eu = 180 + sh + e - lz` lies in
`[-150, 214]`, well inside the emitted `[-1022, 1023]`, and `el_pack` returns a
code rather than handing the value to the slower tier.

The call sites satisfy the bounds: `ub` is a quotient by `2 ^ 63` of a word
below `2 ^ 64` (`hi64_lt`, `exactRhi_lt`), `up` is `0` or `1` by construction,
and `m` is that word divided by `2 ^ (10 + ub)`, which `slice_le` bounds by
`2 ^ 53`. -/
theorem elPack_range {p : Pack} (hm : p.m ≤ 2 ^ 53) (hup : p.up ≤ 1)
    (hub : p.ub ≤ 1) (he1 : -277 ≤ p.e) (he2 : p.e ≤ 22) (hlz : p.lz ≤ 63) :
    (elPack p).isSome := by
  have hsh : 10 + p.ub + (p.m + p.up) / 2 ^ 53 ≤ 12 := by
    have hmm : p.m + p.up ≤ 2 ^ 53 + 1 := by omega
    have h2 : (2 : Nat) * 2 ^ 53 = 2 ^ 54 := by rw [Nat.mul_comm, ← Nat.pow_succ]
    have hov : (p.m + p.up) / 2 ^ 53 < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      omega
    omega
  have hcast : ((p.lz : Nat) : Int) ≤ 63 := by omega
  have hlo : (-1022 : Int) ≤
      180 + ((10 + p.ub + (p.m + p.up) / 2 ^ 53 : Nat) : Int) + p.e - (p.lz : Int) := by
    omega
  have hhi : 180 + ((10 + p.ub + (p.m + p.up) / 2 ^ 53 : Nat) : Int) + p.e - (p.lz : Int)
      ≤ 1023 := by
    omega
  unfold elPack
  dsimp only
  split
  · rfl
  · rename_i hne
    exact absurd ⟨hlo, hhi⟩ hne



theorem pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k
theorem pow2_ne_zero (k : Nat) : (2 : Nat) ^ k ≠ 0 := Nat.ne_of_gt (pow2_pos k)
theorem div_pow_cancel {a c s : Nat} (hc : 0 < c) : (a * 2 ^ s) / (c * 2 ^ s) = a / c :=
  Nat.mul_div_mul_right a c (pow2_pos s)
theorem mul_cancel_right_le {a b c : Nat} (hc : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨fun h => Nat.le_of_mul_le_mul_right h hc, fun h => Nat.mul_le_mul_right c h⟩
theorem add_mod_pow52 {n : Nat} (hlo : 2 ^ 52 ≤ n) (hhi : n < 2 ^ 53) :
    2 ^ 52 + n % 2 ^ 52 = n := by
  have h2 : (2 : Nat) ^ 53 = 2 * 2 ^ 52 := by
    rw [show (53 : Nat) = 52 + 1 from rfl, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
  have hdiv : n / 2 ^ 52 = 1 := by
    apply Nat.div_eq_of_lt_le (k := 1)
    · omega
    · omega
  have hmod := Nat.div_add_mod n (2 ^ 52)
  rw [hdiv] at hmod
  omega

theorem eD_pos (q : Int) (t : EPow) : 0 < eD q t := by
  unfold eD; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
theorem eN_pos (q : Int) (t : EPow) : 0 < eN q t := by
  unfold eN; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
theorem row_split {q : Int} {t : EPow} (h : t.Fits q) :
    eN q t = eH t * eD q t + eN q t % eD q t := by
  unfold EPow.Fits at h
  have hd := Nat.div_add_mod (eN q t) (eD q t)
  rw [Nat.mul_comm (eD q t)] at hd
  rw [← h] at hd
  exact hd.symm
theorem row_R_lt {q : Int} {t : EPow} : eN q t % eD q t < eD q t := Nat.mod_lt _ (eD_pos q t)
theorem row_R_zero {q : Int} {t : EPow} (hfit : t.Fits q) (hneq : t.Neq q) (hq : 0 ≤ q) :
    eN q t % eD q t = 0 := by
  have hsplit := row_split hfit
  unfold EPow.Neq at hneq
  rw [hneq] at hsplit
  omega
theorem row_R_pos {q : Int} {t : EPow} (hrow : t.Row q) (hq : q < 0) :
    0 < eN q t % eD q t := hrow.2.2.2.2.1 hq
theorem Wf_lt {W R D : Nat} (hW : W < 2 ^ 64) (hR : R < D) (hD : 0 < D) :
    W * R < 2 ^ 64 * D := by
  have h1 : W * R ≤ (2 ^ 64 - 1) * D := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * D < 2 ^ 64 * D := Nat.mul_lt_mul_of_pos_right (by omega) hD
  exact Nat.lt_of_le_of_lt h1 h2
theorem eH_lower_row {q : Int} {t : EPow} (hrow : t.Row q) : 2 ^ 127 ≤ eH t :=
  eH_lower hrow.1.1
theorem eH_upper_row {q : Int} {t : EPow} (hrow : t.Row q) : eH t < 2 ^ 128 :=
  eH_upper hrow.1.2.1 hrow.1.2.2

/-- For a truncated row the tick value's numerator is `W * eN * 2^s`. -/
theorem valueTicks_neg {w : Nat} {q : Int} {t : EPow} {s : Nat}
    (hq : q < 0) (hrow : t.Row q)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) :
    (valueTicks w q).1 = Wnorm w * eN q t * 2 ^ s := by
  obtain ⟨-, -, -, -, -, hnege⟩ := hrow
  have heneg : t.e < 0 := hnege hq
  have hqnn : ¬ (0 ≤ q) := by omega
  have hP1 : (valueTicks w q).1 = w * 2 ^ 1074 := by
    unfold valueTicks; rw [ite_eq_right hqnn]
  have hslz : (s : Nat) + (-t.e).toNat + lz w = 1074 := by omega
  have hP : (valueTicks w q).1 = Wnorm w * 2 ^ (s + (-t.e).toNat) := by
    rw [hP1]
    unfold Wnorm
    rw [show (1074 : Nat) = lz w + (s + (-t.e).toNat) from by omega, Nat.pow_add]
    ac_rfl
  have hN : eN q t = 2 ^ (-t.e).toNat := by
    unfold eN
    rw [Int.toNat_of_nonpos (by omega : q ≤ 0), Nat.pow_zero, Nat.one_mul]
  rw [hP, hN, Nat.pow_add]
  ac_rfl

theorem valueTicks_d_neg {w : Nat} {q : Int} {t : EPow}
    (hq : q < 0) (hrow : t.Row q) :
    (valueTicks w q).2 = eD q t := by
  obtain ⟨-, -, -, -, -, hnege⟩ := hrow
  have heneg : t.e < 0 := hnege hq
  have hqnn : ¬ (0 ≤ q) := by omega
  have hqabs : q.natAbs = (-q).toNat := by omega
  unfold valueTicks
  rw [ite_eq_right hqnn, hqabs]
  unfold eD
  rw [Int.toNat_of_nonpos (by omega : t.e ≤ 0), Nat.pow_zero, Nat.mul_one]

theorem valueTicks_d_nonneg {w : Nat} {q : Int} (hq : 0 ≤ q) :
    (valueTicks w q).2 = 1 := by
  unfold valueTicks; rw [ite_eq_left hq]

/-- **The binade of the tick value, uniformly.**  `B = 190 + s + b` where `b`
is the indicator `2 ^ 191 * eD ≤ W * eN`. -/
theorem binade_valueTicks {w : Nat} {q : Int} {t : EPow} {s : Nat}
    (hw0 : 0 < w) (hw : w < 2 ^ 64) (hrow : t.Row q)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) (hsl : s < 1900) :
    binade (valueTicks w q).1 (valueTicks w q).2 =
      190 + s + (if 2 ^ 191 * eD q t ≤ Wnorm w * eN q t then 1 else 0) := by
  by_cases hq : 0 ≤ q
  · have hb := binade_valueTicks_nonneg hw0 hw hq hrow hs hsl
    have hneq : t.Neq q := hrow.2.2.2.1 hq
    have heq : (2 ^ 191 * eD q t ≤ Wnorm w * eN q t) ↔ (2 ^ 191 ≤ Wnorm w * eH t) := by
      rw [← hneq, ← Nat.mul_assoc]
      exact mul_cancel_right_le (eD_pos q t)
    rw [hb]
    by_cases h : 2 ^ 191 * eD q t ≤ Wnorm w * eN q t
    · rw [ite_eq_left h, ite_eq_left (heq.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h (heq.mpr hh))]
  · have hqneg : q < 0 := by omega
    have hb := binade_valueTicks_neg hw0 hw hqneg hrow hs hsl
    have heneg : t.e < 0 := hrow.2.2.2.2.2 hqneg
    have heq : (2 ^ 191 * 10 ^ (-q).toNat ≤ Wnorm w * 2 ^ (-t.e).toNat) ↔
        (2 ^ 191 * eD q t ≤ Wnorm w * eN q t) := by
      simp only [eD, eN, Int.toNat_of_nonpos (by omega : q ≤ 0),
        Int.toNat_of_nonpos (by omega : t.e ≤ 0), Nat.pow_zero, Nat.mul_one, Nat.one_mul]
    rw [hb]
    by_cases h : 2 ^ 191 * 10 ^ (-q).toNat ≤ Wnorm w * 2 ^ (-t.e).toNat
    · rw [ite_eq_left h, ite_eq_left (heq.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h (heq.mpr hh))]

/-! ### The division identity -/

/-- `(Rhi * 2^128 + M) / 2^(138+b) = Rhi / 2^(10+b)`: the high word reads its
own slice, and anything below it is below one unit of the cut. -/
theorem quot_split {Rhi M b : Nat} (hM : M < 2 ^ 128) :
    (Rhi * 2 ^ 128 + M) / 2 ^ (138 + b) = Rhi / 2 ^ (10 + b) := by
  have hpow : (2 : Nat) ^ (138 + b) = 2 ^ (10 + b) * 2 ^ 128 := by
    rw [show 138 + b = (10 + b) + 128 from by omega, Nat.pow_add]
  have hdec := Nat.div_add_mod Rhi (2 ^ (10 + b))
  have hhp : Rhi % 2 ^ (10 + b) < 2 ^ (10 + b) := Nat.mod_lt _ (pow2_pos _)
  have hres : (Rhi % 2 ^ (10 + b)) * 2 ^ 128 + M < 2 ^ (10 + b) * 2 ^ 128 := by
    have h1 : ((Rhi % 2 ^ (10 + b)) + 1) * 2 ^ 128 ≤ 2 ^ (10 + b) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (Rhi % 2 ^ (10 + b)) * 2 ^ 128 + M < ((Rhi % 2 ^ (10 + b)) + 1) * 2 ^ 128 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_of_lt_of_le h2 h1
  have hpos : 0 < 2 ^ (10 + b) * 2 ^ 128 :=
    Nat.mul_pos (pow2_pos _) (pow2_pos _)
  have hnum : (Rhi % 2 ^ (10 + b)) * 2 ^ 128 + M
        + (Rhi / 2 ^ (10 + b)) * (2 ^ (10 + b) * 2 ^ 128)
      = Rhi * 2 ^ 128 + M := by
    have h1 : (Rhi / 2 ^ (10 + b)) * (2 ^ (10 + b) * 2 ^ 128)
        = ((Rhi / 2 ^ (10 + b)) * 2 ^ (10 + b)) * 2 ^ 128 := by rw [Nat.mul_assoc]
    rw [h1]
    have h2 : (Rhi % 2 ^ (10 + b)) * 2 ^ 128 + M
          + ((Rhi / 2 ^ (10 + b)) * 2 ^ (10 + b)) * 2 ^ 128
        = ((Rhi % 2 ^ (10 + b)) + (Rhi / 2 ^ (10 + b)) * 2 ^ (10 + b)) * 2 ^ 128 + M := by
      rw [Nat.add_mul]
      ac_rfl
    have h3 : (Rhi % 2 ^ (10 + b)) + (Rhi / 2 ^ (10 + b)) * 2 ^ (10 + b) = Rhi := by
      rw [Nat.add_comm, Nat.mul_comm (Rhi / 2 ^ (10 + b)) (2 ^ (10 + b)), hdec]
    rw [h2, h3]
  rw [hpow, ← hnum, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hres, Nat.zero_add]

/-- The spec's significand for a nonnegative row is the slice's `m`. -/
theorem sig_eq_m_nonneg {w : Nat} {q : Int} {t : EPow} {s b : Nat}
    (hw0 : 0 < w) (hw : w < 2 ^ 64) (hrow : t.Row q) (hq : 0 ≤ q)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) (hsl : s < 1900)
    (hB : binade (valueTicks w q).1 (valueTicks w q).2 = 190 + s + b) :
    (valueTicks w q).1 /
      ((valueTicks w q).2 * ulp (valueTicks w q).1 (valueTicks w q).2)
      = exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b) := by
  have hP := valueTicks_nonneg hq hrow hs
  have hd := valueTicks_d_nonneg (w := w) hq
  have hWs : Wnorm w < 2 ^ 64 := Wnorm_upper hw0 hw
  have hu : ulp (valueTicks w q).1 (valueTicks w q).2 = 2 ^ (138 + s + b) := by
    unfold ulp
    rw [hB]
    congr 1; omega
  rw [hu, hP, hd, Nat.one_mul]
  rw [show 138 + s + b = (138 + b) + s from by omega, Nat.pow_add]
  rw [div_pow_cancel (pow2_pos _)]
  have hsplit := exact_split hWs hrow.1.2.1 hrow.1.2.2
  have hM : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo < 2 ^ 128 := by
    have h1 : exactRlo (Wnorm w) t.hi t.lo < 2 ^ 64 := Nat.mod_lt _ (pow2_pos 64)
    have h2 : lo64 (Wnorm w) t.lo < 2 ^ 64 := Nat.mod_lt _ (pow2_pos 64)
    have h3 : exactRlo (Wnorm w) t.hi t.lo ≤ 2 ^ 64 - 1 := by omega
    have h4 : lo64 (Wnorm w) t.lo ≤ 2 ^ 64 - 1 := by omega
    have h5 : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ h3
    have h6 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 := by
      rw [Nat.sub_mul, Nat.one_mul, pow64_128]
    omega
  rw [show eH t = t.hi * 2 ^ 64 + t.lo from rfl, hsplit,
    show exactRhi (Wnorm w) t.hi t.lo * 2 ^ 128
        + exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo
      = exactRhi (Wnorm w) t.hi t.lo * 2 ^ 128
        + (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo)
      from by rw [Nat.add_assoc]]
  exact quot_split hM

/-- The residue of the truncated row's quotient stays inside one unit, so the
sliced high word still reads the floor. -/
theorem quot_residue_neg {W Rhi M D hp b : Nat} (hD : 0 < D)
    (hRR : W * Rhi < 2 ^ 64 * D) (hM : M < 2 ^ 128)
    (hhp : hp + 2 ≤ 2 ^ (10 + b)) :
    D * (hp * 2 ^ 128) + D * M + W * Rhi < D * (2 ^ (10 + b) * 2 ^ 128) := by
  have h64 : (2 : Nat) ^ 64 < 2 ^ 128 := by
    have h : (2 : Nat) ^ 64 * 1 < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_left (by decide : 1 < 2 ^ 64) (pow2_pos 64)
    rw [Nat.mul_one, ← pow64_128] at h
    exact h
  have h1 : hp * 2 ^ 128 + M + 2 ^ 64 < 2 ^ (10 + b) * 2 ^ 128 := by
    have hph : (hp + 2) * 2 ^ 128 ≤ 2 ^ (10 + b) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ hhp
    have hMle : M ≤ 2 ^ 128 - 1 := by omega
    have h3 : hp * 2 ^ 128 + M + 2 ^ 64 < (hp + 2) * 2 ^ 128 := by
      rw [Nat.add_mul]
      omega
    exact Nat.lt_of_lt_of_le h3 hph
  have he : D * (hp * 2 ^ 128) + D * M + 2 ^ 64 * D
      = D * (hp * 2 ^ 128 + M + 2 ^ 64) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm (2 ^ 64) D]
  have h4 : D * (hp * 2 ^ 128) + D * M + W * Rhi
      < D * (hp * 2 ^ 128 + M + 2 ^ 64) := by
    have h := Nat.add_lt_add_left hRR (D * (hp * 2 ^ 128) + D * M)
    rwa [he] at h
  have h6 : D * (hp * 2 ^ 128 + M + 2 ^ 64) < D * (2 ^ (10 + b) * 2 ^ 128) :=
    Nat.mul_lt_mul_of_pos_left h1 hD
  exact Nat.lt_trans h4 h6

/-- The spec's significand for a truncated row, in-window: the slice's `m`. -/
theorem sig_eq_m_neg {w : Nat} {q : Int} {t : EPow} {s b : Nat}
    (hw0 : 0 < w) (hw : w < 2 ^ 64) (hrow : t.Row q) (hq : q < 0)
    (hs : (s : Int) = 1074 + t.e - (lz w : Int)) (hsl : s < 1900)
    (hB : binade (valueTicks w q).1 (valueTicks w q).2 = 190 + s + b)
    (hhp : exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b) + 2 ≤ 2 ^ (10 + b)) :
    (valueTicks w q).1 /
      ((valueTicks w q).2 * ulp (valueTicks w q).1 (valueTicks w q).2)
      = exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b) := by
  have hP := valueTicks_neg hq hrow hs
  have hd := valueTicks_d_neg (w := w) hq hrow
  have hWs : Wnorm w < 2 ^ 64 := Wnorm_upper hw0 hw
  have hD := eD_pos q t
  have hu : ulp (valueTicks w q).1 (valueTicks w q).2 = 2 ^ (138 + s + b) := by
    unfold ulp
    rw [hB]
    congr 1; omega
  rw [hu, hP, hd]
  rw [show 138 + s + b = (138 + b) + s from by omega, Nat.pow_add]
  rw [show eD q t * (2 ^ (138 + b) * 2 ^ s) = (eD q t * 2 ^ (138 + b)) * 2 ^ s from by
    rw [Nat.mul_assoc]]
  rw [div_pow_cancel (Nat.mul_pos hD (pow2_pos _))]
  -- goal: (W * eN) / (eD * 2^(138+b)) = Rhi / 2^(10+b)
  have hsplit := exact_split hWs hrow.1.2.1 hrow.1.2.2
  have hM : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo < 2 ^ 128 := by
    have h1 : exactRlo (Wnorm w) t.hi t.lo < 2 ^ 64 := Nat.mod_lt _ (pow2_pos 64)
    have h2 : lo64 (Wnorm w) t.lo < 2 ^ 64 := Nat.mod_lt _ (pow2_pos 64)
    have h3 : exactRlo (Wnorm w) t.hi t.lo ≤ 2 ^ 64 - 1 := by omega
    have h4 : lo64 (Wnorm w) t.lo ≤ 2 ^ 64 - 1 := by omega
    have h5 : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ h3
    have h6 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 := by
      rw [Nat.sub_mul, Nat.one_mul, pow64_128]
    omega
  have hRhi : exactRhi (Wnorm w) t.hi t.lo < 2 ^ 64 := exactRhi_lt hWs hrow.1.2.1 hrow.1.2.2
  -- write eN = eH * eD + R, W*eN = D*(W*eH) + W*R
  have hNsplit := row_split hrow.2.2.1
  -- R < D
  have hRlt : eN q t % eD q t < eD q t := row_R_lt
  have hWR : Wnorm w * (eN q t % eD q t) < 2 ^ 64 * eD q t :=
    Wf_lt hWs hRlt hD
  -- W*eH = Rhi * 2^128 + M
  have hWH : Wnorm w * eH t = exactRhi (Wnorm w) t.hi t.lo * 2 ^ 128
      + (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo) := by
    rw [show eH t = t.hi * 2 ^ 64 + t.lo from rfl, hsplit, Nat.add_assoc]
  -- the guard's slice
  have hdecRhi : exactRhi (Wnorm w) t.hi t.lo
      = exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b) * 2 ^ (10 + b)
        + exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b) := by
    have := Nat.div_add_mod (exactRhi (Wnorm w) t.hi t.lo) (2 ^ (10 + b))
    rw [Nat.mul_comm] at this
    exact this.symm
  -- now build the division
  have hC : (2 : Nat) ^ (138 + b) = 2 ^ (10 + b) * 2 ^ 128 := by
    rw [show 138 + b = (10 + b) + 128 from by omega, Nat.pow_add]
  have hnum : Wnorm w * eN q t
      = (eD q t * ((exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b)) * 2 ^ 128)
            + eD q t * (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo)
            + Wnorm w * (eN q t % eD q t))
        + (exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b)) * (eD q t * (2 ^ (10 + b) * 2 ^ 128)) := by
    have hWN : Wnorm w * eN q t
        = eD q t * (Wnorm w * eH t) + Wnorm w * (eN q t % eD q t) := by
      conv => lhs; rw [hNsplit]
      rw [Nat.mul_add, ← Nat.mul_assoc]
      ac_rfl
    calc Wnorm w * eN q t
        = eD q t * (Wnorm w * eH t) + Wnorm w * (eN q t % eD q t) := hWN
      _ = eD q t * (exactRhi (Wnorm w) t.hi t.lo * 2 ^ 128
              + (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo))
            + Wnorm w * (eN q t % eD q t) := by rw [hWH]
      _ = eD q t * (((exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b)) * 2 ^ (10 + b)
              + exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b)) * 2 ^ 128
              + (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo))
            + Wnorm w * (eN q t % eD q t) := by
        conv => lhs; rw [hdecRhi]
      _ = _ := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
        ac_rfl
  have hres : eD q t * ((exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b)) * 2 ^ 128)
      + eD q t * (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo)
      + Wnorm w * (eN q t % eD q t) < eD q t * (2 ^ (10 + b) * 2 ^ 128) :=
    quot_residue_neg hD hWR hM hhp
  rw [hC, hnum]
  rw [Nat.add_mul_div_right _ _ (Nat.mul_pos hD (Nat.mul_pos (pow2_pos _) (pow2_pos _)))]
  rw [Nat.div_eq_of_lt hres, Nat.zero_add]


/-! ### The decision as a pack -/

theorem lt_of_mul_lt_mul_left_nat {a b c : Nat} (h : c * a < c * b) (hc : 0 < c) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul_left c hge))

/-- The rounded-up bit the specification applies: `0` below the half, `1`
above, and the significand's parity at an exact tie. -/
def upDec (P d : Nat) : Nat :=
  if 2 * (P % (d * ulp P d)) < d * ulp P d then 0
  else if d * ulp P d < 2 * (P % (d * ulp P d)) then 1
  else P / (d * ulp P d) % 2

theorem upDec_zero {P d : Nat} (h : 2 * (P % (d * ulp P d)) < d * ulp P d) :
    upDec P d = 0 := by
  unfold upDec; rw [ite_eq_left h]

theorem upDec_one {P d : Nat} (h1 : ¬ 2 * (P % (d * ulp P d)) < d * ulp P d)
    (h2 : d * ulp P d < 2 * (P % (d * ulp P d))) : upDec P d = 1 := by
  unfold upDec; rw [ite_eq_right h1, ite_eq_left h2]

theorem upDec_par {P d : Nat} (h1 : ¬ 2 * (P % (d * ulp P d)) < d * ulp P d)
    (h2 : ¬ d * ulp P d < 2 * (P % (d * ulp P d))) :
    upDec P d = P / (d * ulp P d) % 2 := by
  unfold upDec; rw [ite_eq_right h1, ite_eq_right h2]

/-- `normalCode` as the pack `el_pack` builds it, whenever the significand is
in the normal range. -/
theorem normalCode_eq_form {P d : Nat} (hB : 52 ≤ binade P d)
    (hlo : 2 ^ 52 ≤ P / (d * ulp P d)) (hhi : P / (d * ulp P d) < 2 ^ 53) :
    normalCode P d =
      ⟨binade P d - 51 + (P / (d * ulp P d) + upDec P d) / 2 ^ 53,
        2 ^ 52 + (P / (d * ulp P d) + upDec P d) % 2 ^ 52⟩ := by
  have hm0 : (2 : Nat) ^ 53 % 2 ^ 52 = 0 := by
    rw [show (53 : Nat) = 52 + 1 from rfl, Nat.pow_add, Nat.pow_one]
  unfold normalCode
  dsimp only
  generalize hq0 : P / (d * ulp P d) = q0 at hlo hhi ⊢
  generalize hr : P % (d * ulp P d) = r
  by_cases h1 : 2 * r < d * ulp P d
  · rw [ite_eq_left h1]
    have hpar : upDec P d = 0 := upDec_zero (by rw [hr]; exact h1)
    have hq0lt : q0 / 2 ^ 53 = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hpar, Nat.add_zero, hq0lt, add_mod_pow52 hlo hhi]
  · by_cases h2 : d * ulp P d < 2 * r
    · rw [ite_eq_right h1, ite_eq_left h2]
      have hpar : upDec P d = 1 := upDec_one (by rw [hr]; exact h1) (by rw [hr]; exact h2)
      by_cases h3 : q0 + 1 = 2 ^ 53
      · rw [ite_eq_left h3]
        have hq1 : (q0 + 1) / 2 ^ 53 = 1 := by rw [h3, Nat.div_self (pow2_pos _)]
        simp only [hpar, hq1, h3, hm0, Nat.add_zero,
          show binade P d - 51 + 1 = binade P d - 50 from by omega]
      · rw [ite_eq_right h3]
        have hq0lt : (q0 + 1) / 2 ^ 53 = 0 := Nat.div_eq_of_lt (by omega)
        have hq0' : 2 ^ 52 + (q0 + 1) % 2 ^ 52 = q0 + 1 :=
          add_mod_pow52 (by omega) (by omega)
        simp only [hpar, hq0lt, Nat.add_zero, hq0']
    · rw [ite_eq_right h1, ite_eq_right h2]
      have hpar : upDec P d = q0 % 2 := by
        rw [← hq0]
        exact upDec_par (by rw [hr]; exact h1) (by rw [hr]; exact h2)
      by_cases h4 : q0 % 2 = 0
      · rw [ite_eq_left h4]
        have hq0lt : q0 / 2 ^ 53 = 0 := Nat.div_eq_of_lt (by omega)
        simp only [hpar, h4, Nat.add_zero, hq0lt, add_mod_pow52 hlo hhi]
      · rw [ite_eq_right h4]
        by_cases h3 : q0 + 1 = 2 ^ 53
        · rw [ite_eq_left h3]
          have hp1 : q0 % 2 = 1 := by omega
          have hq1 : (q0 + 1) / 2 ^ 53 = 1 := by rw [h3, Nat.div_self (pow2_pos _)]
          simp only [hpar, hp1, hq1, h3, hm0, Nat.add_zero,
            show binade P d - 51 + 1 = binade P d - 50 from by omega]
        · rw [ite_eq_right h3]
          have hp1 : q0 % 2 = 1 := by omega
          have hq0lt : (q0 + 1) / 2 ^ 53 = 0 := Nat.div_eq_of_lt (by omega)
          have hq0' : 2 ^ 52 + (q0 + 1) % 2 ^ 52 = q0 + 1 :=
            add_mod_pow52 (by omega) (by omega)
          simp only [hpar, hp1, hq0lt, Nat.add_zero, hq0']


/-! ### The 192-bit half comparison -/

theorem pow2_mul_pow2 (a b : Nat) : (2 : Nat) ^ a * 2 ^ b = 2 ^ (a + b) :=
  (Nat.pow_add 2 a b).symm

theorem two_mul_pow (s : Nat) : 2 * (2 : Nat) ^ s = 2 ^ (s + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem hh_mul128 (b : Nat) : (2 : Nat) ^ (9 + b) * 2 ^ 128 = 2 ^ (137 + b) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- `2^(138+s+b) = 2^(s+1) * 2^(137+b)`. -/
theorem Z_factor (s b : Nat) :
    (2 : Nat) ^ (138 + s + b) = 2 ^ (s + 1) * 2 ^ (137 + b) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- **The nonnegative decomposition.**  `2 P = 2 m Z + 2^(s+1) (hp·2^128 + M)`. -/
theorem decomp_nonneg {W H Rhi M hp m b s P : Nat}
    (hP : P = W * H * 2 ^ s) (hWH : W * H = Rhi * 2 ^ 128 + M)
    (hdec : Rhi = m * 2 ^ (10 + b) + hp) :
    2 * P = 2 * m * 2 ^ (138 + s + b) + 2 ^ (s + 1) * (hp * 2 ^ 128 + M) := by
  have h138 : (2 : Nat) ^ (138 + b) = 2 * 2 ^ (137 + b) := by
    rw [show 138 + b = (137 + b) + 1 from by omega, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
  have hmul : (2 : Nat) ^ (10 + b) * 2 ^ 128 = 2 ^ (138 + b) := by
    rw [← Nat.pow_add]; congr 1; omega
  have e1 : 2 * (W * H * 2 ^ s) = 2 ^ (s + 1) * (W * H) := by
    rw [show 2 * (W * H * 2 ^ s) = (W * H) * (2 * 2 ^ s) from by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]]
    rw [two_mul_pow, Nat.mul_comm]
  have h1 : 2 * P = 2 ^ (s + 1) * (W * H) := by rw [hP, e1]
  have harg : (m * 2 ^ (10 + b) + hp) * 2 ^ 128 + M
      = m * 2 ^ (138 + b) + (hp * 2 ^ 128 + M) := by
    rw [Nat.add_mul, Nat.mul_assoc, hmul]
    omega
  have h2 : 2 ^ (s + 1) * (W * H) = 2 ^ (s + 1) * (m * 2 ^ (138 + b) + (hp * 2 ^ 128 + M)) := by
    rw [hWH, hdec, harg]
  have hstep : 2 ^ (s + 1) * (m * 2 ^ (138 + b)) = 2 * m * 2 ^ (138 + s + b) := by
    rw [Z_factor, h138]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have h3 : 2 ^ (s + 1) * (m * 2 ^ (138 + b) + (hp * 2 ^ 128 + M))
      = 2 * m * 2 ^ (138 + s + b) + 2 ^ (s + 1) * (hp * 2 ^ 128 + M) := by
    rw [← hstep, ← Nat.mul_add]
  rw [h1, h2, h3]

/-- **The truncated decomposition.**  `2 P = 2 m Z + 2^(s+1) (D(hp·2^128+M) + W·R)`. -/
theorem decomp_neg {W H D R Rhi M hp m b s P : Nat}
    (hP : P = W * (H * D + R) * 2 ^ s) (hWH : W * H = Rhi * 2 ^ 128 + M)
    (hdec : Rhi = m * 2 ^ (10 + b) + hp) :
    2 * P = 2 * m * (D * 2 ^ (138 + s + b))
      + 2 ^ (s + 1) * (D * (hp * 2 ^ 128 + M) + W * R) := by
  have h138 : (2 : Nat) ^ (138 + b) = 2 * 2 ^ (137 + b) := by
    rw [show 138 + b = (137 + b) + 1 from by omega, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
  have hmul : (2 : Nat) ^ (10 + b) * 2 ^ 128 = 2 ^ (138 + b) := by
    rw [← Nat.pow_add]; congr 1; omega
  have e1 : 2 * (W * (H * D + R) * 2 ^ s) = 2 ^ (s + 1) * (W * (H * D + R)) := by
    rw [show 2 * (W * (H * D + R) * 2 ^ s)
        = W * (H * D + R) * (2 * 2 ^ s) from by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]]
    rw [two_mul_pow, Nat.mul_comm]
  have h1 : 2 * P = 2 ^ (s + 1) * (W * (H * D + R)) := by rw [hP, e1]
  have hWNR : W * (H * D + R) = D * (W * H) + W * R := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (W * H) D]
  have harg : (m * 2 ^ (10 + b) + hp) * 2 ^ 128 + M
      = m * 2 ^ (138 + b) + (hp * 2 ^ 128 + M) := by
    rw [Nat.add_mul, Nat.mul_assoc, hmul]
    omega
  have hargD : D * ((m * 2 ^ (10 + b) + hp) * 2 ^ 128 + M) + W * R
      = D * (m * 2 ^ (138 + b) + (hp * 2 ^ 128 + M)) + W * R := by
    rw [harg]
  have hstep : 2 ^ (s + 1) * (D * (m * 2 ^ (138 + b))) = 2 * m * (D * 2 ^ (138 + s + b)) := by
    rw [Z_factor, h138]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have h3 : 2 ^ (s + 1) * (D * (m * 2 ^ (138 + b) + (hp * 2 ^ 128 + M)) + W * R)
      = 2 * m * (D * 2 ^ (138 + s + b))
        + 2 ^ (s + 1) * (D * (hp * 2 ^ 128 + M) + W * R) := by
    rw [← hstep, ← Nat.mul_add]
    congr 1
    rw [Nat.mul_add]
    omega
  rw [h1, hWNR, hWH, hdec, hargD, h3]

/-- With `2P = 2mZ + 2^(s+1)·T` and `Z = 2^(s+1)·T'`, the half comparison is
`T` against `T'`. -/
theorem half_lt {P Z m s T T' : Nat} (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T)
    (hZ : Z = 2 ^ (s + 1) * T') (h : T < T') : 2 * P < (2 * m + 1) * Z := by
  have hZ' : (2 * m + 1) * Z = 2 * m * Z + Z := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : 2 ^ (s + 1) * T < 2 ^ (s + 1) * T' := Nat.mul_lt_mul_of_pos_left h (pow2_pos _)
  omega

theorem half_gt {P Z m s T T' : Nat} (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T)
    (hZ : Z = 2 ^ (s + 1) * T') (h : T' < T) : (2 * m + 1) * Z < 2 * P := by
  have hZ' : (2 * m + 1) * Z = 2 * m * Z + Z := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : 2 ^ (s + 1) * T' < 2 ^ (s + 1) * T := Nat.mul_lt_mul_of_pos_left h (pow2_pos _)
  omega

theorem half_eq {P Z m s T T' : Nat} (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T)
    (hZ : Z = 2 ^ (s + 1) * T') (h : T = T') : 2 * P = (2 * m + 1) * Z := by
  have hZ' : (2 * m + 1) * Z = 2 * m * Z + Z := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : 2 ^ (s + 1) * T = 2 ^ (s + 1) * T' := by rw [h]
  omega

theorem half_le {P Z m s T T' : Nat} (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T)
    (hZ : Z = 2 ^ (s + 1) * T') (h : T' ≤ T) : (2 * m + 1) * Z ≤ 2 * P := by
  have hZ' : (2 * m + 1) * Z = 2 * m * Z + Z := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : 2 ^ (s + 1) * T' ≤ 2 ^ (s + 1) * T := Nat.mul_le_mul_left _ h
  omega

/-- The remainder below the half is below the ulp. -/
theorem mod_lt_half {P Z m : Nat} (hm : P / Z = m) (h : 2 * P < (2 * m + 1) * Z) :
    2 * (P % Z) < Z := by
  have hle : m * Z ≤ P := by rw [← hm]; exact Nat.div_mul_le_self P Z
  have hmod : P % Z = P - m * Z := by
    rw [Nat.mod_eq_sub_mul_div, hm, Nat.mul_comm]
  have hP : P = m * Z + (P % Z) := by rw [hmod]; omega
  have hZ' : (2 * m + 1) * Z = 2 * (m * Z) + Z := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  rw [hZ'] at h
  omega

theorem mod_gt_half {P Z m : Nat} (hm : P / Z = m) (h : (2 * m + 1) * Z < 2 * P) :
    Z < 2 * (P % Z) := by
  have hle : m * Z ≤ P := by rw [← hm]; exact Nat.div_mul_le_self P Z
  have hmod : P % Z = P - m * Z := by
    rw [Nat.mod_eq_sub_mul_div, hm, Nat.mul_comm]
  have hP : P = m * Z + (P % Z) := by rw [hmod]; omega
  have hZ' : (2 * m + 1) * Z = 2 * (m * Z) + Z := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  rw [hZ'] at h
  omega

theorem mod_eq_half {P Z m : Nat} (hm : P / Z = m) (h : 2 * P = (2 * m + 1) * Z) :
    2 * (P % Z) = Z := by
  have hle : m * Z ≤ P := by rw [← hm]; exact Nat.div_mul_le_self P Z
  have hmod : P % Z = P - m * Z := by
    rw [Nat.mod_eq_sub_mul_div, hm, Nat.mul_comm]
  have hP : P = m * Z + (P % Z) := by rw [hmod]; omega
  have hZ' : (2 * m + 1) * Z = 2 * (m * Z) + Z := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  rw [hZ'] at h
  omega

/-! ### The numeric edges -/

theorem hh_pos (b : Nat) : 2 ≤ 2 ^ (9 + b) := by
  have h1 : 2 ≤ (2 : Nat) ^ 9 := by decide
  exact Nat.le_trans h1 (Nat.pow_le_pow_right (by decide) (by omega))

theorem above_far {hp M b : Nat} (h : 2 ^ (9 + b) + 1 ≤ hp) :
    2 ^ (137 + b) < hp * 2 ^ 128 + M := by
  rw [← hh_mul128 b]
  have h2 : (2 ^ (9 + b) + 1) * 2 ^ 128 ≤ hp * 2 ^ 128 := Nat.mul_le_mul_right _ h
  have h3 : 2 ^ (9 + b) * 2 ^ 128 + 2 ^ 128 ≤ (2 ^ (9 + b) + 1) * 2 ^ 128 := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_refl _
  omega

theorem at_edge {hp b : Nat} (h : hp = 2 ^ (9 + b)) : hp * 2 ^ 128 = 2 ^ (137 + b) := by
  rw [h]; exact hh_mul128 b

theorem below_close {hp M b : Nat} (h : hp = 2 ^ (9 + b) - 1) (hM : M < 2 ^ 128) :
    hp * 2 ^ 128 + M < 2 ^ (137 + b) := by
  rw [← hh_mul128 b, h, Nat.sub_mul, Nat.one_mul]
  have hX : (2 : Nat) ^ 128 ≤ 2 ^ (9 + b) * 2 ^ 128 := by
    simpa using Nat.mul_le_mul_right ((2 : Nat) ^ 128) (Nat.one_le_two_pow (n := 9 + b))
  omega

theorem below_far {hp M b : Nat} (h : hp + 2 ≤ 2 ^ (9 + b)) (hM : M < 2 ^ 128) :
    hp * 2 ^ 128 + M < 2 ^ (137 + b) := by
  rw [← hh_mul128 b]
  have h2 : (hp + 2) * 2 ^ 128 ≤ 2 ^ (9 + b) * 2 ^ 128 := Nat.mul_le_mul_right _ h
  have h3 : hp * 2 ^ 128 + M < (hp + 2) * 2 ^ 128 := by
    rw [Nat.add_mul]
    omega
  exact Nat.lt_of_lt_of_le h3 h2

/-! ### The binade bit from the rebuilt word -/

/-- The window's exclusion of `Rhi = 2^63 - 1` turns `ub = 0` into
`Rhi ≤ 2^63 - 2`. -/
theorem rhi_le_of_ub_zero {Rhi ub sh hp hh : Nat} (hub : ub = Rhi / 2 ^ 63)
    (hsh : sh = 10 + ub) (hhp : hp = Rhi % 2 ^ sh) (hhh : hh = 2 ^ (9 + ub))
    (hzero : ub = 0) (hwin : hh - 2 ≤ hp ∧ hp ≤ hh) : Rhi ≤ 2 ^ 63 - 2 := by
  subst hzero
  have hub0 : Rhi / 2 ^ 63 = 0 := by rw [← hub]
  have hlt : Rhi < 2 ^ 63 := by
    rcases Nat.lt_or_ge Rhi (2 ^ 63) with h | h
    · exact h
    · exfalso
      have hge : 1 ≤ Rhi / 2 ^ 63 := by
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 63)]
        simpa using h
      omega
  have hne : Rhi ≠ 2 ^ 63 - 1 := by
    intro he
    have hsh10 : sh = 10 := by rw [hsh]
    have hhh512 : hh = 512 := by rw [hhh]
    have hph : hp = 1023 := by rw [hhp, he, hsh10]
    omega
  rcases Nat.lt_or_ge Rhi (2 ^ 63 - 1) with h | h
  · omega
  · exfalso
    exact hne (by omega)

theorem bit_one {W H D R Rhi M : Nat} (hWH : W * H = Rhi * 2 ^ 128 + M)
    (h : 2 ^ 63 ≤ Rhi) : 2 ^ 191 * D ≤ W * (H * D + R) := by
  have hWNR : W * (H * D + R) = D * (W * H) + W * R := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (W * H) D]
  rw [hWNR]
  have h1 : 2 ^ 191 ≤ W * H := by
    rw [hWH]
    have h191 : (2 : Nat) ^ 191 = 2 ^ 63 * 2 ^ 128 := by rw [← Nat.pow_add]
    rw [h191]
    exact Nat.le_trans (Nat.mul_le_mul_right _ h) (Nat.le_add_right _ _)
  have h2 : 2 ^ 191 * D ≤ D * (W * H) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left D h1
  exact Nat.le_trans h2 (Nat.le_add_right _ _)

theorem bit_zero {W H D R Rhi M : Nat} (hW : W < 2 ^ 64) (hD : 0 < D)
    (hR : R < D) (hM : M < 2 ^ 128) (hWH : W * H = Rhi * 2 ^ 128 + M)
    (hRhi : Rhi ≤ 2 ^ 63 - 2) : W * (H * D + R) < 2 ^ 191 * D := by
  have hWNR : W * (H * D + R) = D * (W * H) + W * R := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (W * H) D]
  rw [hWNR]
  have hA : W * H ≤ (2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1) := by
    rw [hWH]
    have h1 : Rhi * 2 ^ 128 ≤ (2 ^ 63 - 2) * 2 ^ 128 := Nat.mul_le_mul_right _ hRhi
    have h2 : M ≤ 2 ^ 128 - 1 := by omega
    exact Nat.add_le_add h1 h2
  have hDm : D * (W * H) ≤ D * ((2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1)) :=
    Nat.mul_le_mul_left D hA
  have hWRlt : W * R < 2 ^ 64 * D := Wf_lt hW hR hD
  have hkey : (2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1) + 2 ^ 64 < 2 ^ 191 := by
    have h191 : (2 : Nat) ^ 191 = 2 ^ 63 * 2 ^ 128 := by rw [← Nat.pow_add]
    rw [h191]
    have e1 : (2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1) + 2 ^ 64
        = (2 ^ 63 - 1) * 2 ^ 128 + (2 ^ 64 - 1) := by
      have h1 : (2 ^ 63 - 2) * 2 ^ 128 + 2 ^ 128 = (2 ^ 63 - 1) * 2 ^ 128 := by
        rw [show (2 ^ 63 - 1 : Nat) = (2 ^ 63 - 2) + 1 from by omega, Nat.add_mul,
          Nat.one_mul]
      have h2 : (1 : Nat) ≤ 2 ^ 128 := Nat.one_le_two_pow
      have h3 : (1 : Nat) ≤ 2 ^ 64 := Nat.one_le_two_pow
      omega
    rw [e1]
    have h1 : (2 ^ 63 - 1) * 2 ^ 128 + 2 ^ 128 = 2 ^ 63 * 2 ^ 128 := by
      rw [show (2 ^ 63 : Nat) = (2 ^ 63 - 1) + 1 from by omega, Nat.add_mul, Nat.one_mul]
    have h64 : (2 : Nat) ^ 64 < 2 ^ 128 := by
      have h : (2 : Nat) ^ 64 * 1 < 2 ^ 64 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_left (show 1 < 2 ^ 64 by decide) (Nat.two_pow_pos 64)
      rw [Nat.mul_one, ← pow64_128] at h
      exact h
    omega
  have he : D * ((2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1)) + 2 ^ 64 * D
      = D * ((2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1) + 2 ^ 64) := by
    rw [Nat.mul_add D ((2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1)) (2 ^ 64),
      Nat.mul_comm (2 ^ 64) D]
  calc D * (W * H) + W * R
      < D * ((2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1)) + 2 ^ 64 * D :=
        Nat.add_lt_add_of_le_of_lt hDm hWRlt
    _ = D * ((2 ^ 63 - 2) * 2 ^ 128 + (2 ^ 128 - 1) + 2 ^ 64) := he
    _ < D * 2 ^ 191 := Nat.mul_lt_mul_of_pos_left hkey hD
    _ = 2 ^ 191 * D := Nat.mul_comm _ _


/-! ### The truncated row's scaled edges -/

theorem pow64_lt_128 : (2 : Nat) ^ 64 < 2 ^ 128 := by
  have h : (2 : Nat) ^ 64 * 1 < 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_lt_mul_of_pos_left (show 1 < 2 ^ 64 by decide) (Nat.two_pow_pos 64)
  rw [Nat.mul_one, ← pow64_128] at h
  exact h

theorem above_scaled {W D R hp M b : Nat} (hD : 0 < D) (h : 2 ^ (9 + b) + 1 ≤ hp) :
    D * 2 ^ (137 + b) ≤ D * (hp * 2 ^ 128 + M) + W * R := by
  have h1 : 2 ^ (137 + b) ≤ hp * 2 ^ 128 + M := Nat.le_of_lt (above_far (M := M) h)
  calc D * 2 ^ (137 + b) ≤ D * (hp * 2 ^ 128 + M) := Nat.mul_le_mul_left D h1
    _ ≤ D * (hp * 2 ^ 128 + M) + W * R := Nat.le_add_right _ _

theorem at_edge_scaled {W D R hp M b : Nat} (h : hp = 2 ^ (9 + b)) :
    D * (hp * 2 ^ 128 + M) + W * R = D * 2 ^ (137 + b) + (D * M + W * R) := by
  rw [h, Nat.mul_add, hh_mul128 b]
  omega

/-- At the close edge the comparison with the ulp is the comparison of the
discarded part with `D * 2^128`. -/
theorem close_shift {D M W R hp b : Nat} (h : hp = 2 ^ (9 + b) - 1) :
    D * (hp * 2 ^ 128 + M) + W * R + D * 2 ^ 128 = D * 2 ^ (137 + b) + (D * M + W * R) := by
  have he : ((2 ^ (9 + b) - 1) * 2 ^ 128 + M) + 2 ^ 128 = 2 ^ (9 + b) * 2 ^ 128 + M := by
    rw [Nat.sub_mul, Nat.one_mul]
    have hpos : (2 : Nat) ^ 128 ≤ 2 ^ (9 + b) * 2 ^ 128 := by
      simpa using Nat.mul_le_mul_right ((2 : Nat) ^ 128) (Nat.one_le_two_pow (n := 9 + b))
    omega
  rw [h]
  rw [show D * (((2 ^ (9 + b) - 1) * 2 ^ 128 + M)) + W * R + D * 2 ^ 128
      = (D * (((2 ^ (9 + b) - 1) * 2 ^ 128 + M)) + D * 2 ^ 128) + W * R from by omega]
  rw [← Nat.mul_add, he, hh_mul128 b, Nat.mul_add]
  omega

theorem below_far_scaled {D M W R hp b : Nat} (hD : 0 < D) (hM : M < 2 ^ 128)
    (hWR : W * R < 2 ^ 64 * D) (h : hp + 2 ≤ 2 ^ (9 + b)) :
    D * (hp * 2 ^ 128 + M) + W * R < D * 2 ^ (137 + b) := by
  have hgap : hp * 2 ^ 128 + M + 2 ^ 64 < 2 ^ (9 + b) * 2 ^ 128 := by
    have h2 : (hp + 2) * 2 ^ 128 ≤ 2 ^ (9 + b) * 2 ^ 128 := Nat.mul_le_mul_right _ h
    have h3 : hp * 2 ^ 128 + M + 2 ^ 64 < (hp + 2) * 2 ^ 128 := by
      rw [Nat.add_mul]
      have h64 : (2 : Nat) ^ 64 < 2 ^ 128 := pow64_lt_128
      omega
    exact Nat.lt_of_lt_of_le h3 h2
  have h1 : D * (hp * 2 ^ 128 + M) + D * 2 ^ 64 < D * (2 ^ (9 + b) * 2 ^ 128) := by
    rw [← Nat.mul_add]
    exact Nat.mul_lt_mul_of_pos_left hgap hD
  have h2 : D * (hp * 2 ^ 128 + M) + W * R < D * (2 ^ (9 + b) * 2 ^ 128) := by
    have h64 : 2 ^ 64 * D = D * 2 ^ 64 := Nat.mul_comm _ _
    have hWR' : W * R < D * 2 ^ 64 := by rw [← h64]; exact hWR
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hWR' _) (Nat.le_of_lt h1)
  rw [← hh_mul128 b]
  exact h2


/-! ### The significand complement -/

theorem sig_bounds {P d : Nat} (hd : 0 < d)
    (hex : ∃ B', B' < 2100 ∧ P < d * 2 ^ (B' + 1)) (hB : 52 ≤ binade P d) :
    2 ^ 52 ≤ P / (d * ulp P d) ∧ P / (d * ulp P d) < 2 ^ 53 := by
  obtain ⟨B0, hB0, hP0⟩ := hex
  have hspec := binade_spec ⟨B0, hB0, hP0⟩
  have hupos : 0 < d * ulp P d := Nat.mul_pos hd (pow2_pos _)
  have hu : ulp P d = 2 ^ (binade P d - 52) := rfl
  have hmul : ∀ k : Nat, (2 : Nat) ^ k * (d * ulp P d) = d * 2 ^ (binade P d - 52 + k) := by
    intro k
    rw [hu, ← Nat.mul_assoc, Nat.mul_comm ((2 : Nat) ^ k) d, Nat.mul_assoc, ← Nat.pow_add,
      Nat.add_comm]
  constructor
  · rw [Nat.le_div_iff_mul_le hupos]
    have hmin := hspec.2 (binade P d - 1) (by omega)
    have he : binade P d - 1 + 1 = binade P d := by omega
    rw [he] at hmin
    rw [hmul, show binade P d - 52 + 52 = binade P d from by omega]
    exact hmin
  · rw [Nat.div_lt_iff_lt_mul hupos]
    rw [hmul, show binade P d - 52 + 53 = binade P d + 1 from by omega]
    exact hspec.1

/-- The high word's significand stays in the normal range. -/
theorem W_H_lt {W H : Nat} (hW : W < 2 ^ 64) (hH : H < 2 ^ 128) : W * H < 2 ^ 192 := by
  have h1 : W * H ≤ (2 ^ 64 - 1) * (2 ^ 128 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * (2 ^ 128 - 1) < 2 ^ 64 * 2 ^ 128 :=
    Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (pow2_pos _)
  have h3 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 := by rw [← Nat.pow_add]
  omega

theorem W_H1_le {W H : Nat} (hW : W < 2 ^ 64) (hH : H < 2 ^ 128) :
    W * (H + 1) ≤ 2 ^ 192 := by
  have h1 : W * (H + 1) ≤ (2 ^ 64 - 1) * 2 ^ 128 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * 2 ^ 128 < 2 ^ 64 * 2 ^ 128 :=
    Nat.mul_lt_mul_of_pos_right (by omega) (pow2_pos _)
  have h3 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 := by rw [← Nat.pow_add]
  omega


/-! ### The guard's body, split at the window test -/

def elUndec (hp hh Rlo L : Nat) : Bool :=
  (decide (hp = hh) && decide (Rlo ||| L = 0)) ||
    (decide (hp = hh - 1) && decide (Rlo = 2 ^ 64 - 1))

def elUp (m hp hh Rlo L : Nat) : Nat :=
  if hp > hh then 1
  else if decide (hp = hh) && decide ((Rlo ||| L) ≠ 0 ∨ m % 2 = 1) then 1 else 0

def elInner (s : Slice) (c L : Nat) (e : Int) (lz : Nat) (q : Int) : Option Code :=
  let Rlo := (s.Alo + c) % 2 ^ 64
  let Rhi := (s.Ahi + (if Rlo < s.Alo then 1 else 0)) % 2 ^ 64
  let ub := Rhi / 2 ^ 63
  let sh := 10 + ub
  let m := Rhi / 2 ^ sh
  let hp := Rhi % 2 ^ sh
  let hh := 2 ^ (9 + ub)
  if elUndec hp hh Rlo L && decide (q < 0) then none
  else elPack { m := m, up := elUp m hp hh Rlo L, ub := ub, e := e, lz := lz }

def elFar (s : Slice) (e : Int) (lz : Nat) : Option Code :=
  elPack { m := s.Ahi / 2 ^ s.sh, up := if s.hp > s.hh then 1 else 0,
           ub := s.ub, e := e, lz := lz }

def elCore (W : Nat) (hi lo : Nat) (e : Int) (lz : Nat) (q : Int) : Option Code :=
  let s := sliceOf W hi
  if inWindow s.hp s.hh then elInner s (hi64 W lo) (lo64 W lo) e lz q
  else elFar s e lz

theorem elTier2Code_reduce (w : Nat) (q : Int) :
    elTier2Code w q =
      (match epowAt q with
       | none => none
       | some t =>
         if w = 0 then some { expField := 0, mant := 0 }
         else elCore (Wnorm w) t.hi t.lo t.e (lz w) q) := rfl

theorem lor_eq_zero_left {a b : Nat} (h : (a ||| b) = 0) : a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h0 : a.testBit i = false := by
    have h1 : (a ||| b).testBit i = false := by rw [h, Nat.zero_testBit]
    rw [Nat.testBit_or] at h1
    simp only [Bool.or_eq_false_iff] at h1
    exact h1.1
  rw [h0, Nat.zero_testBit]

theorem lor_eq_zero_iff {a b : Nat} : (a ||| b) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact ⟨lor_eq_zero_left h, by rw [Nat.or_comm] at h; exact lor_eq_zero_left h⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem elUp_above {m hp hh Rlo L : Nat} (h : hh < hp) : elUp m hp hh Rlo L = 1 := by
  unfold elUp; rw [ite_eq_left h]

theorem elUp_below {m hp hh Rlo L : Nat} (h1 : ¬ hh < hp) (h2 : hp ≠ hh) :
    elUp m hp hh Rlo L = 0 := by
  unfold elUp
  have hc : ¬ ((decide (hp = hh) && decide ((Rlo ||| L) ≠ 0 ∨ m % 2 = 1)) = true) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h, -⟩
    exact h2 h
  rw [ite_eq_right h1, ite_eq_right hc]

theorem elUp_tie_zero {m hp hh Rlo L : Nat} (h1 : hp = hh) (h2 : (Rlo ||| L) = 0) :
    elUp m hp hh Rlo L = m % 2 := by
  unfold elUp
  have hcond : (decide (hp = hh) && decide ((Rlo ||| L) ≠ 0 ∨ m % 2 = 1)) = decide (m % 2 = 1) := by
    rw [h1, h2]
    simp
  rw [ite_eq_right (by omega), hcond]
  by_cases h : m % 2 = 1
  · rw [ite_eq_left (by simpa using h)]; omega
  · rw [ite_eq_right (by simpa using h)]; omega

theorem elUp_tie_ne {m hp hh Rlo L : Nat} (h1 : hp = hh) (h2 : (Rlo ||| L) ≠ 0) :
    elUp m hp hh Rlo L = 1 := by
  unfold elUp
  have hcond : (decide (hp = hh) && decide ((Rlo ||| L) ≠ 0 ∨ m % 2 = 1)) = true := by
    rw [h1]; simp [h2]
  rw [ite_eq_right (by omega), ite_eq_left (by simpa using hcond)]


/-- **The low half's carry and `el_pack`'s `ov`.**  Read from `Ahi` alone the
slice has `ub = 0` and `m = 2 ^ 53 - 1` while the rebuilt word is `2 ^ 63`;
the round-up gives `mm = 2 ^ 53`, so `ov = 1`.  The encoding `el_pack` builds
is then the specification's `⟨B - 51, 2 ^ 52⟩`: `ov` adds exactly the exponent
the missing binade bit would have added, and the significand wraps. -/
theorem pack_carry_agrees {e : Int} {s : Nat} {lzw : Nat}
    (hs : (s : Int) = 1074 + e - (lzw : Int)) :
    (⟨(180 + ((11 : Nat) : Int) + e - (lzw : Int) + 1023).toNat,
        2 ^ 52 + (2 ^ 53) % 2 ^ 52⟩ : Code)
      = ⟨(190 + s + 1) - 51 + (2 ^ 52) / 2 ^ 53, 2 ^ 52 + (2 ^ 52) % 2 ^ 52⟩ := by
  have h1 : (2 : Nat) ^ 52 / 2 ^ 53 = 0 := by
    rw [show (53 : Nat) = 52 + 1 from rfl, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
  have h2 : (2 : Nat) ^ 53 % 2 ^ 52 = 0 := by
    rw [show (53 : Nat) = 52 + 1 from rfl, Nat.pow_add, Nat.pow_one]
  rw [h1]
  rw [h2]
  simp only [Nat.add_zero]
  congr 1
  have h4 : (180 + ((11 : Nat) : Int) + e - (lzw : Int) + 1023) = ((140 + s : Nat) : Int) := by
    omega
  rw [h4, Int.toNat_natCast]
  omega


/-- The significand's bounds, from the explicit binade bound a caller holds. -/
theorem sig_bounds_at {P d B : Nat} (hd : 0 < d) (hB2100 : B < 2100)
    (hP : P < d * 2 ^ (B + 1)) (hB52 : 52 ≤ binade P d) :
    2 ^ 52 ≤ P / (d * ulp P d) ∧ P / (d * ulp P d) < 2 ^ 53 :=
  sig_bounds hd ⟨B, hB2100, hP⟩ hB52

/-- The pack's exponent field: `ub0 + ovg = b + ovs` is all the two sides need. -/
theorem pack_exp {s : Nat} {e : Int} {lzw b ub0 ovg ovs : Nat}
    (hs : (s : Int) = 1074 + e - (lzw : Int)) (hov : ub0 + ovg = b + ovs) :
    (180 + ((10 + ub0 + ovg : Nat) : Int) + e - (lzw : Int) + 1023).toNat
      = 190 + s + b - 51 + ovs := by
  have hcast : ((10 + ub0 + ovg : Nat) : Int) = 10 + (ub0 : Int) + (ovg : Int) := by
    push_cast; rfl
  have hnat : ((190 + s + b - 51 + ovs : Nat) : Int)
      = 190 + (s : Int) + (b : Int) - 51 + (ovs : Int) := by
    have h1 : 190 + s + b = (190 + s + b - 51) + 51 := by omega
    conv => lhs; rw [h1]
    push_cast
    omega
  have hkey : (180 + ((10 + ub0 + ovg : Nat) : Int) + e - (lzw : Int) + 1023)
      = ((190 + s + b - 51 + ovs : Nat) : Int) := by
    rw [hcast, hnat]
    omega
  rw [hkey, Int.toNat_natCast]

/-- The lattice's ulp in the slice's own scale. -/
theorem ulp_eq {P d s b : Nat} (hB : binade P d = 190 + s + b) :
    ulp P d = 2 ^ (138 + s + b) := by
  unfold ulp
  rw [hB]
  congr 1
  omega

/-- `2^(138+s+b) = 2^(s+1) 2^(137+b)`. -/
theorem Z0 (s b : Nat) : (2 : Nat) ^ (138 + s + b) = 2 ^ (s + 1) * 2 ^ (137 + b) := by
  rw [show 138 + s + b = (s + 1) + (137 + b) from by omega, Nat.pow_add]

/-- `D 2^(138+s+b) = 2^(s+1) (D 2^(137+b))`. -/
theorem ZD (D s b : Nat) :
    D * (2 : Nat) ^ (138 + s + b) = 2 ^ (s + 1) * (D * 2 ^ (137 + b)) := by
  rw [Z0, Nat.mul_left_comm]


/-- **Below the half.**  `T < T'` rounds down. -/
theorem upDec_zero_of_T_lt {P d Z m s T T' : Nat} (hdZ : Z = d * ulp P d)
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) (hZ : Z = 2 ^ (s + 1) * T')
    (hm : P / Z = m) (h : T < T') : upDec P d = 0 := by
  refine upDec_zero ?_
  rw [← hdZ]
  exact mod_lt_half hm (half_lt hP hZ h)

/-- **Above the half.**  `T' < T` rounds up. -/
theorem upDec_one_of_T_gt {P d Z m s T T' : Nat} (hdZ : Z = d * ulp P d)
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) (hZ : Z = 2 ^ (s + 1) * T')
    (hm : P / Z = m) (h : T' < T) : upDec P d = 1 := by
  have h2 := mod_gt_half hm (half_gt hP hZ h)
  refine upDec_one ?_ ?_
  · rw [← hdZ]
    exact Nat.not_lt.mpr (Nat.le_of_lt h2)
  · rw [← hdZ]
    exact h2

/-- **At the half.**  The significand's parity decides. -/
theorem upDec_par_of_T_eq {P d Z m s T T' : Nat} (hdZ : Z = d * ulp P d)
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) (hZ : Z = 2 ^ (s + 1) * T')
    (hm : P / Z = m) (h : T = T') : upDec P d = m % 2 := by
  have h2 : 2 * (P % (d * ulp P d)) = d * ulp P d := by
    rw [← hdZ]
    exact mod_eq_half hm (half_eq hP hZ h)
  have h3 : upDec P d = P / Z % 2 := by
    have h4 := upDec_par (P := P) (d := d) (Nat.not_lt.mpr (Nat.le_of_eq h2.symm))
      (Nat.not_lt.mpr (Nat.le_of_eq h2))
    rwa [← hdZ] at h4
  rw [h3, hm]

/-- The carry's exponent: the guard's `ov` and the specification's carry agree. -/
theorem carry_agree {b ub0 X : Nat} (hbu : ub0 ≤ b) (hb : b ≤ 1) (hub : ub0 ≤ 1)
    (hlo : 2 ^ 52 ≤ X) (hz : b = ub0 ∨ X < 2 ^ 53) :
    ub0 + (X + (b - ub0) * 2 ^ 52) / 2 ^ 53 = b + X / 2 ^ 53 := by
  rcases Nat.lt_or_ge ub0 b with h | h
  · have hb1 : b = ub0 + 1 := by omega
    have hk : b - ub0 = 1 := by omega
    rcases hz with hz' | hz'
    · omega
    · rw [hk, Nat.one_mul]
      have hdiv : (X + 2 ^ 52) / 2 ^ 53 = 1 := by
        refine Nat.div_eq_of_lt_le (k := 1) (by omega) ?_
        rw [show (1 + 1) * 2 ^ 53 = 2 ^ 54 from by rw [Nat.mul_comm, ← Nat.pow_succ]]
        omega
      have hzero : X / 2 ^ 53 = 0 := Nat.div_eq_of_lt hz'
      rw [hdiv, hzero, Nat.add_zero, hb1]
  · have hbe : b = ub0 := by omega
    have hk : b - ub0 = 0 := by omega
    rw [hk, Nat.zero_mul, Nat.add_zero, hbe]

/-- The two `Code`s agree once the significands and the exponent's carry do. -/
theorem code_agree {s : Nat} {e : Int} {lzw b ub0 q0 upDec m_g up_g : Nat}
    (hs : (s : Int) = 1074 + e - (lzw : Int))
    (hmant : (m_g + up_g) % 2 ^ 52 = (q0 + upDec) % 2 ^ 52)
    (hov : ub0 + (m_g + up_g) / 2 ^ 53 = b + (q0 + upDec) / 2 ^ 53) :
    (⟨190 + s + b - 51 + (q0 + upDec) / 2 ^ 53, 2 ^ 52 + (q0 + upDec) % 2 ^ 52⟩ : Code)
      = ⟨(180 + ((10 + ub0 + (m_g + up_g) / 2 ^ 53 : Nat) : Int) + e - (lzw : Int) + 1023).toNat,
          2 ^ 52 + (m_g + up_g) % 2 ^ 52⟩ := by
  rw [Code.mk.injEq]
  exact ⟨(pack_exp hs hov).symm, congrArg (fun x => 2 ^ 52 + x) hmant.symm⟩

/-- `hi64` of two words is at most `2 ^ 64 - 2`. -/
theorem hi64_le {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : hi64 a b ≤ 2 ^ 64 - 2 := by
  unfold hi64
  have hlt : a * b < (2 ^ 64 - 1) * 2 ^ 64 := by
    have h1 : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) < (2 ^ 64 - 1) * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_left (by omega : 2 ^ 64 - 1 < 2 ^ 64) (by omega)
    exact Nat.lt_of_le_of_lt h1 h2
  have h4 : a * b / 2 ^ 64 < 2 ^ 64 - 1 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt
  omega

/-- The rebuilt high word is the first word plus the low half's carry, with no
wrap. -/
theorem exactRhi_eq {W hi lo : Nat} (hW : W < 2 ^ 64) (hhi : hi < 2 ^ 64) :
    exactRhi W hi lo = hi64 W hi + (if exactRlo W hi lo < lo64 W hi then 1 else 0) := by
  have h2 : hi64 W hi ≤ 2 ^ 64 - 2 := hi64_le hW hhi
  have hcarry : (if exactRlo W hi lo < lo64 W hi then 1 else 0) ≤ 1 := by split <;> omega
  unfold exactRhi
  exact Nat.mod_eq_of_lt (by omega)

theorem pow_succ_mul (s T : Nat) : 2 ^ (s + 1) * T = 2 * (2 ^ s * T) := by
  rw [Nat.pow_succ]; ac_rfl

theorem pow128 (b : Nat) : (2 : Nat) ^ (10 + b) * 2 ^ 128 = 2 * 2 ^ (137 + b) := by
  rw [← Nat.pow_add, show 10 + b + 128 = 137 + b + 1 from by omega, Nat.pow_succ,
    Nat.mul_comm]

theorem pow138 (b : Nat) : (2 : Nat) ^ (138 + b) = 2 * 2 ^ (137 + b) := by
  rw [show 138 + b = (137 + b) + 1 from by omega, Nat.pow_succ, Nat.mul_comm]

theorem pow128_le (b : Nat) : (2 : Nat) ^ 128 ≤ 2 ^ (137 + b) :=
  Nat.pow_le_pow_right (by decide) (by omega)

theorem pow10_128 (b : Nat) : (2 : Nat) ^ (10 + b) * 2 ^ 128 = 2 ^ (138 + b) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem fullA {hp b : Nat} (h : hp = 2 ^ (10 + b) - 1) :
    hp * 2 ^ 128 = 2 ^ (138 + b) - 2 ^ 128 := by
  rw [h, Nat.sub_mul, Nat.one_mul, pow10_128]

theorem fullD {D hp b : Nat} (h : hp = 2 ^ (10 + b) - 1) :
    D * (hp * 2 ^ 128) = D * 2 ^ (138 + b) - D * 2 ^ 128 := by
  rw [fullA h, Nat.mul_sub]

theorem Tgt_neg {D W R M hp b : Nat} (hD : 0 < D) (h : 2 ^ (9 + b) + 1 ≤ hp) :
    D * 2 ^ (137 + b) < D * (hp * 2 ^ 128 + M) + W * R := by
  have h1 : 2 ^ (137 + b) < hp * 2 ^ 128 := by
    have h2 : (2 ^ (9 + b) + 1) * 2 ^ 128 ≤ hp * 2 ^ 128 := Nat.mul_le_mul_right _ h
    have h3 : 2 ^ (9 + b) * 2 ^ 128 < (2 ^ (9 + b) + 1) * 2 ^ 128 := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.lt_add_of_pos_right (pow2_pos 128)
    rw [← hh_mul128 b]
    exact Nat.lt_of_lt_of_le h3 h2
  have h4 : D * 2 ^ (137 + b) < D * (hp * 2 ^ 128) := Nat.mul_lt_mul_of_pos_left h1 hD
  have h5 : D * (hp * 2 ^ 128) ≤ D * (hp * 2 ^ 128 + M) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  exact Nat.lt_of_lt_of_le h4 (Nat.le_trans h5 (Nat.le_add_right _ _))

theorem Tlt3_pos_above {M hp b : Nat} (hM : M < 2 ^ 128) (h : hp + 2 ≤ 2 ^ (10 + b)) :
    hp * 2 ^ 128 + M < 3 * 2 ^ (137 + b) := by
  have h1 : hp * 2 ^ 128 + M < (hp + 1) * 2 ^ 128 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h2 : (hp + 1) * 2 ^ 128 ≤ 2 ^ (10 + b) * 2 ^ 128 := Nat.mul_le_mul_right _ (by omega)
  rw [pow128 b] at h2
  have h3 : 2 * (2 : Nat) ^ (137 + b) ≤ 3 * 2 ^ (137 + b) := by
    have h4 : 0 < (2 : Nat) ^ (137 + b) := pow2_pos _
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)

theorem Tlt3_neg_above {D W R M hp b : Nat} (hD : 0 < D) (hWR : W * R < 2 ^ 64 * D)
    (hM : M < 2 ^ 128) (h : hp + 2 ≤ 2 ^ (10 + b)) :
    D * (hp * 2 ^ 128 + M) + W * R < 3 * (D * 2 ^ (137 + b)) := by
  have hw : W * R < D * 2 ^ 64 := by rw [Nat.mul_comm D]; exact hWR
  have h8 : hp * 2 ^ 128 + M + 2 ^ 64 < 2 ^ (10 + b) * 2 ^ 128 := by
    have h4 : (hp + 2) * 2 ^ 128 ≤ 2 ^ (10 + b) * 2 ^ 128 := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul] at h4
    omega
  have h9 : D * (hp * 2 ^ 128 + M) + D * 2 ^ 64 = D * (hp * 2 ^ 128 + M + 2 ^ 64) := by
    rw [← Nat.mul_add]
  have h10 : D * (hp * 2 ^ 128 + M + 2 ^ 64) < D * (2 ^ (10 + b) * 2 ^ 128) :=
    Nat.mul_lt_mul_of_pos_left h8 hD
  have h11 : D * (2 ^ (10 + b) * 2 ^ 128) = 2 * (D * 2 ^ (137 + b)) := by
    rw [pow128 b, Nat.mul_comm D (2 * 2 ^ (137 + b)), Nat.mul_assoc,
      Nat.mul_comm (2 ^ (137 + b)) D]
  have h12 : 2 * (D * 2 ^ (137 + b)) ≤ 3 * (D * 2 ^ (137 + b)) := by
    have h13 : 0 < D * 2 ^ (137 + b) := Nat.mul_pos hD (pow2_pos _)
    omega
  calc D * (hp * 2 ^ 128 + M) + W * R
      < D * (hp * 2 ^ 128 + M) + D * 2 ^ 64 := Nat.add_lt_add_left hw _
    _ = D * (hp * 2 ^ 128 + M + 2 ^ 64) := h9
    _ < D * (2 ^ (10 + b) * 2 ^ 128) := h10
    _ = 2 * (D * 2 ^ (137 + b)) := h11
    _ ≤ 3 * (D * 2 ^ (137 + b)) := h12

theorem Tlt3_pos_full {M hp b : Nat} (hM : M < 2 ^ 128) (h : hp = 2 ^ (10 + b) - 1) :
    hp * 2 ^ 128 + M < 3 * 2 ^ (137 + b) := by
  have hC : (2 : Nat) ^ 128 ≤ 2 ^ (137 + b) := pow128_le b
  rw [fullA h, pow138 b]
  omega

theorem Tlt3_neg_full {D W R M hp b : Nat} (hD : 0 < D) (hWR : W * R < 2 ^ 64 * D)
    (hM : M < 2 ^ 128) (h : hp = 2 ^ (10 + b) - 1) :
    D * (hp * 2 ^ 128 + M) + W * R < 3 * (D * 2 ^ (137 + b)) := by
  have hw : W * R < D * 2 ^ 64 := by rw [Nat.mul_comm D]; exact hWR
  have hX : 0 < D * 2 ^ (137 + b) := Nat.mul_pos hD (pow2_pos _)
  have hA : D * (hp * 2 ^ 128 + M) + W * R
      = (D * 2 ^ (138 + b) - D * 2 ^ 128) + (D * M + W * R) := by
    rw [Nat.mul_add, fullD (D := D) h, Nat.add_assoc]
  have h1 : D * M + W * R < D * 2 ^ 128 + D * 2 ^ (137 + b) := by
    have h2 : D * M < D * 2 ^ 128 := Nat.mul_lt_mul_of_pos_left hM hD
    have h3 : W * R < D * 2 ^ (137 + b) :=
      Nat.lt_of_lt_of_le hw (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
    exact Nat.add_lt_add h2 h3
  have hB : D * 2 ^ (138 + b) = 2 * (D * 2 ^ (137 + b)) := by
    rw [pow138 b, Nat.mul_comm D (2 * 2 ^ (137 + b)), Nat.mul_assoc,
      Nat.mul_comm (2 ^ (137 + b)) D]
  have hC : D * 2 ^ 128 ≤ D * 2 ^ (138 + b) := by
    rw [hB]
    have h4 : D * 2 ^ 128 ≤ D * 2 ^ (137 + b) :=
      Nat.mul_le_mul_left _ (pow128_le b)
    have h5 : 0 < D * 2 ^ (137 + b) := hX
    omega
  have h3 : 3 * (D * 2 ^ (137 + b)) = 2 * (D * 2 ^ (137 + b)) + D * 2 ^ (137 + b) := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.add_mul, Nat.one_mul]
  rw [hA, hB, h3]
  omega



/-- `2 (2 x) = 4 x`. -/
theorem two_mul_two (x : Nat) : 2 * (2 * x) = 4 * x := by
  rw [← Nat.mul_assoc]

/-- `(c Z + X) % Z = X` for `X < Z`. -/
theorem mod_add_mul {X c Z : Nat} (hX : X < Z) : (c * Z + X) % Z = X := by
  rw [Nat.mul_comm c Z, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- A remainder below one unit leaves the floor at `m`. -/
theorem split_of_two {P Z m s T : Nat}
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) : P = m * Z + 2 ^ s * T := by
  have h := hP
  rw [pow_succ_mul] at h
  have h3 : 2 * (m * Z + 2 ^ s * T) = 2 * m * Z + 2 * (2 ^ s * T) := by
    rw [Nat.mul_add, ← Nat.mul_assoc]
  exact Nat.mul_left_cancel (n := 2) (by decide) (h.trans h3.symm)

theorem div_slice {P Z m s T : Nat} (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T)
    (hT : 2 ^ s * T < Z) : P / Z = m := by
  have h2 := split_of_two hP
  have hZ : 0 < Z := Nat.lt_of_le_of_lt (Nat.zero_le _) hT
  rw [h2, Nat.add_comm, Nat.mul_comm m Z, Nat.add_mul_div_left _ _ hZ,
    Nat.div_eq_of_lt hT, Nat.zero_add]

/-- **Past the half with the remainder wrapped over a unit.** -/
theorem mm_of_T_between {P d Z m s T T' : Nat} (hdZ : Z = d * ulp P d) (hZpos : 0 < Z)
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) (hZ : Z = 2 ^ (s + 1) * T')
    (h1 : 2 * T' ≤ T) (h2 : T < 3 * T') :
    P / (d * ulp P d) + upDec P d = m + 1 := by
  have hZ2 : Z = 2 * (2 ^ s * T') := by
    rw [hZ, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
  have hY1 : Z ≤ 2 ^ s * T := by
    rw [hZ2]
    calc 2 * (2 ^ s * T') = 2 ^ s * (2 * T') := by rw [Nat.mul_left_comm]
      _ ≤ 2 ^ s * T := Nat.mul_le_mul_left _ h1
  have hY2 : 2 ^ s * T < 2 * Z := by
    rw [hZ2]
    calc 2 ^ s * T < 2 ^ s * (3 * T') := Nat.mul_lt_mul_of_pos_left h2 (pow2_pos s)
      _ = 3 * (2 ^ s * T') := by ac_rfl
      _ ≤ 4 * (2 ^ s * T') := Nat.mul_le_mul_right _ (by decide : 3 ≤ 4)
      _ = 2 * (2 * (2 ^ s * T')) := by rw [two_mul_two]
  have hY3 : 2 * (2 ^ s * T) < 3 * Z := by
    rw [hZ2]
    calc 2 * (2 ^ s * T) < 2 * (2 ^ s * (3 * T')) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_pos_left h2 (pow2_pos s)) (by decide)
      _ = 3 * (2 * (2 ^ s * T')) := by ac_rfl
  have hrec : 2 ^ s * T = Z + (2 ^ s * T - Z) := by omega
  have hm1 : m * Z + Z = (m + 1) * Z := by rw [Nat.add_mul, Nat.one_mul]
  have hXlt : 2 ^ s * T - Z < Z := by omega
  have hPP : P = (m + 1) * Z + (2 ^ s * T - Z) := by
    conv => lhs; rw [split_of_two hP, hrec, ← Nat.add_assoc, hm1]
  have hmod : P % Z = 2 ^ s * T - Z := by
    rw [hPP]; exact mod_add_mul hXlt
  have hdiv : P / Z = m + 1 := by
    rw [hPP, Nat.add_comm ((m + 1) * Z), Nat.add_mul_div_right _ _ hZpos,
      Nat.div_eq_of_lt hXlt]
    omega
  have hup : upDec P d = 0 := by
    refine upDec_zero ?_
    rw [← hdZ, hmod]
    omega
  rw [← hdZ, hdiv, hup, Nat.add_zero]

/-- `(c 2^z + X) % 2^z = X % 2^z`. -/
theorem mod_slice {c z X : Nat} : (c * 2 ^ z + X) % 2 ^ z = X % 2 ^ z := by
  rw [Nat.add_comm, Nat.mul_comm c, Nat.add_mul_mod_self_left]

/-- `(c 2^z + X) / 2^z = c` for `X < 2^z`. -/
theorem div_slice' {c z X : Nat} (hX : X < 2 ^ z) : (c * 2 ^ z + X) / 2 ^ z = c := by
  rw [Nat.add_comm, Nat.mul_comm c, Nat.add_mul_div_left _ _ (pow2_pos z),
    Nat.div_eq_of_lt hX, Nat.zero_add]

theorem mm_zero {P d Z m s T T' : Nat} (hdZ : Z = d * ulp P d)
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) (hZ : Z = 2 ^ (s + 1) * T')
    (hm : P / Z = m) (h : T < T') :
    P / (d * ulp P d) + upDec P d = m := by
  rw [← hdZ, hm, upDec_zero_of_T_lt hdZ hP hZ hm h]
  exact Nat.add_zero m

/-- **Above the half** leaves the floor one higher. -/
theorem mm_succ {P d Z m s T T' : Nat} (hdZ : Z = d * ulp P d) (hZpos : 0 < Z)
    (hP : 2 * P = 2 * m * Z + 2 ^ (s + 1) * T) (hZ : Z = 2 ^ (s + 1) * T')
    (h1 : T' < T) (h2 : T < 3 * T') :
    P / (d * ulp P d) + upDec P d = m + 1 := by
  rcases Nat.lt_or_ge T (2 * T') with hlt | hge
  · have hY : 2 ^ s * T < Z := by
      rw [hZ]
      calc 2 ^ s * T < 2 ^ s * (2 * T') := Nat.mul_lt_mul_of_pos_left hlt (pow2_pos s)
        _ = 2 ^ (s + 1) * T' := by rw [pow_succ_mul]; ac_rfl
    have hm := div_slice hP hY
    rw [← hdZ, hm, upDec_one_of_T_gt hdZ hP hZ hm h1]
  · exact mm_of_T_between hdZ hZpos hP hZ hge h2


set_option maxHeartbeats 2000000 in
theorem elGuardRefinesOn : ElGuardRefinesOn := by
  intro w q c hw0 hw hg
  rw [elTier2Code_reduce] at hg
  split at hg
  · exact absurd hg (by simp)
  · rename_i t ht
    have hrow := row_of_epowAt ht
    have hwz : w ≠ 0 := by omega
    rw [ite_eq_right hwz] at hg
    have hhi63 : 2 ^ 63 ≤ t.hi := hrow.1.1
    have hhihi : t.hi < 2 ^ 64 := hrow.1.2.1
    have hlolo : t.lo < 2 ^ 64 := hrow.1.2.2
    have he277 : (-277 : Int) ≤ t.e := hrow.2.1.1
    have he22 : t.e ≤ 22 := hrow.2.1.2
    have hfits : t.Fits q := hrow.2.2.1
    have hne : 0 ≤ q → t.Neq q := hrow.2.2.2.1
    have hRpos : q < 0 → 0 < eN q t % eD q t := hrow.2.2.2.2.1
    have heneg : q < 0 → t.e < 0 := hrow.2.2.2.2.2
    have hlz : lz w ≤ 63 := lz_le_63 w
    have hs0 : 0 ≤ 1074 + t.e - (lz w : Int) := by
      have := hrow.2.1.1
      omega
    obtain ⟨s, hs⟩ : ∃ s : Nat, (s : Int) = 1074 + t.e - (lz w : Int) :=
      ⟨_, Int.toNat_of_nonneg hs0⟩
    have hsl : s < 1900 := by omega
    obtain ⟨P, d, hPd⟩ : ∃ P d : Nat, valueTicks w q = (P, d) := ⟨_, _, rfl⟩
    have hP1 : (valueTicks w q).1 = P := congrArg Prod.fst hPd
    have hP2 : (valueTicks w q).2 = d := congrArg Prod.snd hPd
    obtain ⟨b, hb⟩ : ∃ b : Nat,
        b = (if 2 ^ 191 * eD q t ≤ Wnorm w * eN q t then 1 else 0) := ⟨_, rfl⟩
    have hB : binade P d = 190 + s + b := by
      have h := binade_valueTicks hw0 hw hrow hs hsl
      rw [hP1, hP2, ← hb] at h
      exact h
    have hnc : roundMag P d = .fin (normalCode P d) := by
      rw [← hP1, ← hP2]
      exact roundMag_eq_normalCode hw0 hw ht
    have hWlt : Wnorm w < 2 ^ 64 := Wnorm_upper hw0 hw
    have hWge : 2 ^ 63 ≤ Wnorm w := Wnorm_lower hw0 hw
    have hDpos : 0 < eD q t := eD_pos q t
    have hNsplit : eN q t = eH t * eD q t + eN q t % eD q t := row_split hfits
    have hRlt : eN q t % eD q t < eD q t := row_R_lt
    have hHlo : 2 ^ 127 ≤ eH t := eH_lower hhi63
    have hHhi : eH t < 2 ^ 128 := eH_upper hhihi hlolo
    have hMlt : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo < 2 ^ 128 := by
      have h1 : exactRlo (Wnorm w) t.hi t.lo < 2 ^ 64 := Nat.mod_lt _ (pow2_pos 64)
      have h2 : lo64 (Wnorm w) t.lo < 2 ^ 64 := Nat.mod_lt _ (pow2_pos 64)
      have h3 : exactRlo (Wnorm w) t.hi t.lo ≤ 2 ^ 64 - 1 := by omega
      have h4 : lo64 (Wnorm w) t.lo ≤ 2 ^ 64 - 1 := by omega
      have h5 : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 :=
        Nat.mul_le_mul_right _ h3
      have h6 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 := by
        rw [Nat.sub_mul, Nat.one_mul, pow64_128]
      omega
    have hWH : Wnorm w * eH t = exactRhi (Wnorm w) t.hi t.lo * 2 ^ 128
        + (exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo) := by
      rw [show eH t = t.hi * 2 ^ 64 + t.lo from rfl,
        exact_split hWlt hhihi hlolo, Nat.add_assoc]
    have hRhi_lt : exactRhi (Wnorm w) t.hi t.lo < 2 ^ 64 := exactRhi_lt hWlt hhihi hlolo
    have hWfR : Wnorm w * (eN q t % eD q t) < 2 ^ 64 * eD q t := Wf_lt hWlt hRlt hDpos
    have hdpos : 0 < d := by
      have h : 0 < (valueTicks w q).2 := by
        by_cases hq : 0 ≤ q
        · rw [valueTicks_d_nonneg hq]; decide
        · rw [valueTicks_d_neg (by omega) hrow]; exact hDpos
      rwa [hP2] at h
    have hPb : P < d * 2 ^ (192 + s + 1) := by
      by_cases hq : 0 ≤ q
      · have hd1 : d = 1 := by rw [← hP2]; exact valueTicks_d_nonneg hq
        have hPv : P = Wnorm w * eH t * 2 ^ s := by rw [← hP1]; exact valueTicks_nonneg hq hrow hs
        have hWHlt : Wnorm w * eH t < 2 ^ 192 := W_H_lt hWlt hHhi
        rw [hd1, Nat.one_mul, hPv]
        calc Wnorm w * eH t * 2 ^ s < 2 ^ 192 * 2 ^ s :=
              Nat.mul_lt_mul_of_pos_right hWHlt (pow2_pos s)
          _ = 2 ^ (192 + s) := by rw [← Nat.pow_add]
          _ ≤ 2 ^ (192 + s + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      · have hqneg : q < 0 := by omega
        have hdD : d = eD q t := by rw [← hP2]; exact valueTicks_d_neg hqneg hrow
        have hPv : P = Wnorm w * eN q t * 2 ^ s := by rw [← hP1]; exact valueTicks_neg hqneg hrow hs
        have hWN : Wnorm w * eN q t < eD q t * 2 ^ 192 := by
          rw [hNsplit, Nat.mul_add]
          have hlt1 : Wnorm w * (eH t * eD q t) + Wnorm w * (eN q t % eD q t)
              < Wnorm w * (eH t * eD q t) + Wnorm w * eD q t := by
            have h2 : Wnorm w * (eN q t % eD q t) < Wnorm w * eD q t :=
              Nat.mul_lt_mul_of_pos_left hRlt (by omega)
            omega
          have heq : Wnorm w * (eH t * eD q t) + Wnorm w * eD q t
              = (Wnorm w * (eH t + 1)) * eD q t := by
            rw [Nat.mul_add (Wnorm w) (eH t) 1, Nat.mul_one, Nat.add_mul, Nat.mul_assoc]
          have hW1 : Wnorm w * (eH t + 1) ≤ 2 ^ 192 := W_H1_le hWlt hHhi
          have hthis : (Wnorm w * (eH t + 1)) * eD q t ≤ 2 ^ 192 * eD q t :=
            Nat.mul_le_mul_right _ hW1
          rw [Nat.mul_comm ((2 : Nat) ^ 192) (eD q t)] at hthis
          rw [heq] at hlt1
          exact Nat.lt_of_lt_of_le hlt1 hthis
        rw [hdD, hPv]
        have h2 : Wnorm w * eN q t * 2 ^ s < (eD q t * 2 ^ 192) * 2 ^ s :=
          Nat.mul_lt_mul_of_pos_right hWN (pow2_pos s)
        have he : (eD q t * 2 ^ 192) * 2 ^ s = eD q t * 2 ^ (192 + s) := by
          rw [Nat.mul_assoc, ← Nat.pow_add]
        rw [he] at h2
        exact Nat.lt_of_lt_of_le h2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
    have hB52 : 52 ≤ binade P d := by rw [hB]; omega
    have hsig := sig_bounds_at (d := d) (B := 192 + s) hdpos (by omega) hPb hB52
    have hq0lo : 2 ^ 52 ≤ P / (d * ulp P d) := hsig.1
    have hq0hi : P / (d * ulp P d) < 2 ^ 53 := hsig.2
    -- the reconstructed words and the abbreviated slice
    obtain ⟨Ahi, hAhi⟩ : ∃ A, hi64 (Wnorm w) t.hi = A := ⟨_, rfl⟩
    obtain ⟨Alo, hAlo⟩ : ∃ A, lo64 (Wnorm w) t.hi = A := ⟨_, rfl⟩
    obtain ⟨Lo, hLo⟩ : ∃ A, lo64 (Wnorm w) t.lo = A := ⟨_, rfl⟩
    obtain ⟨ub0, hub0⟩ : ∃ A, Ahi / 2 ^ 63 = A := ⟨_, rfl⟩
    obtain ⟨sh0, hsh0⟩ : ∃ A, 10 + ub0 = A := ⟨_, rfl⟩
    obtain ⟨hp0, hhp0⟩ : ∃ A, Ahi % 2 ^ sh0 = A := ⟨_, rfl⟩
    obtain ⟨hh0, hhh0⟩ : ∃ A, 2 ^ (9 + ub0) = A := ⟨_, rfl⟩
    have hAhi_lt : Ahi < 2 ^ 64 := by rw [← hAhi]; exact hi64_lt hWlt hhihi
    have hAlo_lt : Alo < 2 ^ 64 := by rw [← hAlo]; exact Nat.mod_lt _ (pow2_pos 64)
    have hLo_lt : Lo < 2 ^ 64 := by rw [← hLo]; exact Nat.mod_lt _ (pow2_pos 64)
    have hub0le : ub0 ≤ 1 := by
      rw [← hub0]
      rcases Nat.lt_or_ge (hi64 (Wnorm w) t.hi / 2 ^ 63) 2 with h | h
      · omega
      · exfalso
        have hge : 2 * 2 ^ 63 ≤ hi64 (Wnorm w) t.hi :=
          (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 63)).mp h
        rw [show (2 : Nat) * 2 ^ 63 = 2 ^ 64 from by rw [Nat.mul_comm, ← Nat.pow_succ]] at hge
        omega
    have hhh0pos : 2 ≤ hh0 := by
      rw [← hhh0]
      exact Nat.le_trans (by decide : 2 ≤ (2 : Nat) ^ 9) (Nat.pow_le_pow_right (by decide) (by omega))
    have hhh0le : hh0 ≤ 2 ^ 11 := by
      rw [← hhh0]
      calc (2 : Nat) ^ (9 + ub0) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
    have hhp0_lt : hp0 < 2 ^ 64 := by
      rw [← hhp0]
      refine Nat.lt_of_lt_of_le (Nat.mod_lt _ (pow2_pos _)) ?_
      rw [← hsh0]
      have : ub0 ≤ 1 := hub0le
      calc (2 : Nat) ^ (10 + ub0) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨M, hM⟩ : ∃ A,
        exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64 + lo64 (Wnorm w) t.lo = A := ⟨_, rfl⟩
    have hMlt' : M < 2 ^ 128 := by rw [← hM]; exact hMlt
    obtain ⟨D, hD⟩ : ∃ A, eD q t = A := ⟨_, rfl⟩
    obtain ⟨R, hRv⟩ : ∃ A, eN q t % eD q t = A := ⟨_, rfl⟩
    have hDpos' : 0 < D := by rw [← hD]; exact hDpos
    have hRlt' : R < D := by rw [← hRv, ← hD]; exact hRlt
    have hWfR' : Wnorm w * R < 2 ^ 64 * D := by rw [← hRv, ← hD]; exact hWfR
    have hWH' : Wnorm w * eH t
        = exactRhi (Wnorm w) t.hi t.lo * 2 ^ 128 + M := by rw [← hM]; exact hWH
    unfold elCore at hg
    dsimp only at hg
    unfold sliceOf at hg
    dsimp only at hg
    simp only [hAhi, hAlo, hub0, hsh0, hhp0, hhh0] at hg
    split at hg
    · -- ================= in window =================
      rename_i hwin0
      have hwin : hh0 - 2 ≤ hp0 ∧ hp0 ≤ hh0 :=
        (inWindow_iff hhh0pos hhh0le hhp0_lt).mp hwin0
      unfold elInner at hg
      dsimp only at hg
      obtain ⟨Rlo, hRlo⟩ : ∃ A, (Alo + hi64 (Wnorm w) t.lo) % 2 ^ 64 = A := ⟨_, rfl⟩
      obtain ⟨cy, hcy⟩ : ∃ A, (if Rlo < Alo then 1 else 0) = A := ⟨_, rfl⟩
      obtain ⟨Rhi, hRhi⟩ : ∃ A, (Ahi + cy) % 2 ^ 64 = A := ⟨_, rfl⟩
      obtain ⟨ub, hub⟩ : ∃ A, Rhi / 2 ^ 63 = A := ⟨_, rfl⟩
      obtain ⟨sh, hsh⟩ : ∃ A, 10 + ub = A := ⟨_, rfl⟩
      obtain ⟨m, hm⟩ : ∃ A, Rhi / 2 ^ sh = A := ⟨_, rfl⟩
      obtain ⟨hp, hhp⟩ : ∃ A, Rhi % 2 ^ sh = A := ⟨_, rfl⟩
      obtain ⟨hh, hhh⟩ : ∃ A, 2 ^ (9 + ub) = A := ⟨_, rfl⟩
      obtain ⟨up, hup⟩ : ∃ A, elUp m hp hh Rlo (lo64 (Wnorm w) t.lo) = A := ⟨_, rfl⟩
      obtain ⟨sh2, hsh2⟩ : ∃ A, 10 + ub + (m + up) / 2 ^ 53 = A := ⟨_, rfl⟩
      obtain ⟨eu, heu⟩ : ∃ A, 180 + (sh2 : Int) + t.e - (lz w : Int) = A := ⟨_, rfl⟩
      simp only [hRlo, hcy, hRhi, hub, hsh, hm, hhp, hhh, hup] at hg
      split at hg
      · exact absurd hg (by simp)
      · rename_i hnotundec
        unfold elPack at hg
        dsimp only at hg
        rw [hsh2, heu] at hg
        split at hg
        · rename_i hrange
          have hc : c = ⟨(eu + 1023).toNat, 2 ^ 52 + (m + up) % 2 ^ 52⟩ :=
            (Option.some.inj hg).symm
          have hRlo_eq : Rlo = exactRlo (Wnorm w) t.hi t.lo := by
            rw [← hRlo, ← hAlo]; rfl
          have hRhi_eq : Rhi = exactRhi (Wnorm w) t.hi t.lo := by
            rw [← hRhi, ← hcy, ← hAhi, hRlo_eq, ← hAlo]; rfl
          have hcy1 : cy ≤ 1 := by rw [← hcy]; split <;> omega
          have hRhi_nz : Rhi ≠ 0 := by
            intro h0
            have hWH2 := hWH
            rw [← hRhi_eq] at hWH2
            rw [h0, Nat.zero_mul, Nat.zero_add] at hWH2
            have h2 : 2 ^ 190 ≤ Wnorm w * eH t := binade_lower_190 hWge hHlo
            omega
          have hnoWrap : Ahi + cy < 2 ^ 64 := by
            rcases Nat.lt_or_ge (Ahi + cy) (2 ^ 64) with h | h
            · exact h
            · exfalso
              have h2 : Ahi + cy = 2 ^ 64 := by omega
              rw [h2] at hRhi
              simp only [Nat.mod_self] at hRhi
              exact hRhi_nz hRhi.symm
          have hRhi_sum : Ahi + cy = Rhi := by
            rw [← hRhi]; exact (Nat.mod_eq_of_lt hnoWrap).symm
          have hub_eq : ub = ub0 := by
            rcases Nat.lt_or_ge ub0 1 with h0 | h1
            · have hz0 : ub0 = 0 := by omega
              have hlt : Ahi < 2 ^ 63 := by
                rcases Nat.lt_or_ge Ahi (2 ^ 63) with h | h
                · exact h
                · exfalso
                  have hge : 1 ≤ Ahi / 2 ^ 63 := by
                    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 63)]
                    simpa using h
                  rw [← hub0] at hz0
                  omega
              have hle : Rhi ≤ 2 ^ 63 := by
                rw [← hRhi_sum]; omega
              have hne63 : Rhi ≠ 2 ^ 63 := by
                intro he
                have hsh10 : sh0 = 10 := by rw [← hsh0, hz0]
                have hAhi63 : Ahi = 2 ^ 63 - 1 := by omega
                have hcy1' : cy = 1 := by omega
                have hhp1023 : hp0 = 1023 := by
                  rw [← hhp0, hsh10, hAhi63]
                have hhh0v : hh0 = 512 := by rw [← hhh0, hz0]
                omega
              have huz : Rhi / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
              rw [← hub, huz, hz0]
            · have h1' : ub0 = 1 := by omega
              have hge : 2 ^ 63 ≤ Ahi := by
                rw [← hub0] at h1'
                rcases Nat.lt_or_ge Ahi (2 ^ 63) with h | h
                · exfalso
                  have hz : Ahi / 2 ^ 63 = 0 := Nat.div_eq_of_lt h
                  omega
                · exact h
              have hue : Rhi / 2 ^ 63 = 1 := by
                refine Nat.div_eq_of_lt_le (k := 1) (by omega) ?_
                rw [show (1 + 1) * 2 ^ 63 = 2 ^ 64 from by rw [Nat.mul_comm, ← Nat.pow_succ]]
                rw [← hRhi_sum]; omega
              rw [hub] at hue
              rw [hue, h1']
          have hhh_eq : hh = hh0 := by rw [← hhh, ← hhh0, hub_eq]
          have hsh_eq : sh = sh0 := by rw [← hsh, ← hsh0, hub_eq]
          have hp_eq : hp = hp0 + cy := by
            have h1 : hp = (Ahi + cy) % 2 ^ sh := by rw [← hhp, ← hRhi_sum]
            have h2 : Ahi % 2 ^ sh = hp0 := by
              rw [hsh_eq]; exact hhp0
            have hcylt : cy < 2 ^ sh := by
              have h2 : 2 ≤ 2 ^ sh := by
                have h1 : 1 ≤ sh := by rw [← hsh]; omega
                calc (2 : Nat) = 2 ^ 1 := rfl
                  _ ≤ 2 ^ sh := Nat.pow_le_pow_right (by decide) h1
              omega
            rw [h1, Nat.add_mod, h2, Nat.mod_eq_of_lt hcylt]
            refine Nat.mod_eq_of_lt ?_
            have hbnd : (2 : Nat) ^ (9 + ub0) + 1 < 2 ^ (10 + ub0) := by
              have hpow : 2 * 2 ^ (9 + ub0) = 2 ^ (10 + ub0) := by
                rw [Nat.mul_comm, ← Nat.pow_succ]
                congr 1
                omega
              have hpos : 0 < (2 : Nat) ^ (9 + ub0) := pow2_pos _
              omega
            have hshv : sh = 10 + ub0 := by rw [hsh_eq, ← hsh0]
            rw [hshv]
            omega
          have hdd : Rhi = Rhi / 2 ^ sh * 2 ^ sh + Rhi % 2 ^ sh := by
            rw [Nat.mul_comm (Rhi / 2 ^ sh) (2 ^ sh)]
            exact (Nat.div_add_mod Rhi (2 ^ sh)).symm
          have hRhi_ne : Rhi ≠ 2 ^ 63 - 1 := by
            intro he
            have hu0 : ub = 0 := by
              rw [← hub, he]
            have hsh10 : sh = 10 := by rw [← hsh, hu0]
            have hhpv : hp = 1023 := by
              rw [← hhp, he, hsh10]
            have hle : hp ≤ 513 := by
              rw [hp_eq]
              have hw2 : hp0 ≤ hh0 := hwin.2
              have hb0 : ub0 = 0 := by rw [← hub_eq, hu0]
              have h512 : hh0 = 512 := by rw [← hhh0, hb0]
              omega
            omega
          have hb_eq : b = ub := by
            have hRhi64 : Rhi < 2 ^ 64 := by rw [← hRhi_sum]; omega
            rcases Nat.lt_or_ge Rhi (2 ^ 63) with hlt | hge
            · have hRhi2 : Rhi ≤ 2 ^ 63 - 2 := by omega
              have hb0 : b = 0 := by
                rw [hb]
                have hnot : ¬ (2 ^ 191 * eD q t ≤ Wnorm w * eN q t) := by
                  rw [hNsplit]
                  exact Nat.not_le.mpr
                    (bit_zero hWlt hDpos hRlt hMlt' hWH' (by rw [← hRhi_eq]; exact hRhi2))
                rw [ite_eq_right hnot]
              have huz : ub = 0 := by rw [← hub]; exact Nat.div_eq_of_lt hlt
              rw [hb0, huz]
            · have hb1 : b = 1 := by
                rw [hb]
                have h : 2 ^ 191 * eD q t ≤ Wnorm w * eN q t := by
                  rw [hNsplit]
                  exact bit_one hWH' (by rw [← hRhi_eq]; exact hge)
                rw [ite_eq_left h]
              have hu1 : ub = 1 := by
                rw [← hub]
                refine Nat.div_eq_of_lt_le (k := 1) (by omega) ?_
                rw [show (1 + 1) * 2 ^ 63 = 2 ^ 64 from by rw [Nat.mul_comm, ← Nat.pow_succ]]
                omega
              rw [hb1, hu1]
          have hshb : sh = 10 + b := by rw [← hsh, hb_eq]
          have hh_b : hh = 2 ^ (9 + b) := by rw [← hhh, ← hb_eq]
          have hp_hi : hp ≤ hh + 1 := by rw [hp_eq, hhh_eq]; omega
          have hp_lo : hh - 2 ≤ hp := by rw [hp_eq, hhh_eq]; omega
          have hhhp : exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b) + 2 ≤ 2 ^ (10 + b) := by
            have h1 : exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b) = hp := by
              rw [← hRhi_eq, ← hshb]
              exact hhp
            rw [h1]
            have hp2 : hp ≤ 2 ^ (9 + b) + 1 := by rw [← hh_b]; exact hp_hi
            have hsplit : (2 : Nat) ^ (10 + b) = 2 * 2 ^ (9 + b) := by
              rw [show 10 + b = (9 + b) + 1 from by omega, Nat.pow_add, Nat.pow_one,
                Nat.mul_comm]
            have h3 : 3 ≤ 2 ^ (9 + b) := Nat.le_trans (by decide : 3 ≤ (2 : Nat) ^ 9)
              (Nat.pow_le_pow_right (by decide) (by omega))
            omega
          have hfin : exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b) = m := by
            rw [← hm, ← hRhi_eq, ← hshb]
          have hq0m : P / (d * ulp P d) = m := by
            by_cases hq : 0 ≤ q
            · have h := sig_eq_m_nonneg hw0 hw hrow hq hs hsl (by rw [hP1, hP2]; exact hB)
              rw [hP1, hP2] at h
              rw [h, hfin]
            · have hqneg : q < 0 := by omega
              have h := sig_eq_m_neg hw0 hw hrow hqneg hs hsl
                (by rw [hP1, hP2]; exact hB) hhhp
              rw [hP1, hP2] at h
              rw [h, hfin]
          have hdec : exactRhi (Wnorm w) t.hi t.lo = m * 2 ^ (10 + b) + hp := by
            rw [← hRhi_eq, ← hm, ← hhp, ← hshb]
            exact hdd
          have hupD : upDec P d = up := by
            by_cases hq : 0 ≤ q
            · have hd1 : d = 1 := by rw [← hP2]; exact valueTicks_d_nonneg hq
              have hPQ : P = Wnorm w * eH t * 2 ^ s := by
                rw [← hP1]; exact valueTicks_nonneg hq hrow hs
              have hPdec : 2 * P = 2 * m * 2 ^ (138 + s + b)
                  + 2 ^ (s + 1) * (hp * 2 ^ 128 + M) :=
                decomp_nonneg hPQ hWH' hdec
              have hZeq : (2 : Nat) ^ (138 + s + b) = 2 ^ (s + 1) * 2 ^ (137 + b) := Z0 s b
              have hdZ : (2 : Nat) ^ (138 + s + b) = d * ulp P d := by
                rw [ulp_eq hB, hd1, Nat.one_mul]
              have hmZ : P / 2 ^ (138 + s + b) = m := by
                rw [← hq0m, hdZ]
              rcases Nat.lt_or_ge hh hp with habove | hle
              · have hge : 2 ^ (9 + b) + 1 ≤ hp := by
                  have := habove
                  rw [hh_b] at this
                  omega
                have hup1 : up = 1 := by
                  rw [← hup]; exact elUp_above habove
                have hT : 2 ^ (137 + b) < hp * 2 ^ 128 + M :=
                  above_far (M := M) (b := b) hge
                have hupd : upDec P d = 1 := upDec_one_of_T_gt hdZ hPdec hZeq hmZ hT
                rw [hup1, hupd]
              · rcases Nat.lt_or_ge hp hh with hlt | hge
                · rcases Nat.lt_or_ge (hh - 2) hp with hgt | hle2
                  · have hpe : hp = 2 ^ (9 + b) - 1 := by
                      have := hlt
                      rw [hh_b] at this
                      have := hgt
                      rw [hh_b] at this
                      omega
                    have hup0 : up = 0 := by
                      rw [← hup]
                      exact elUp_below (by rw [hh_b]; omega) (by rw [hh_b]; omega)
                    have hT : hp * 2 ^ 128 + M < 2 ^ (137 + b) :=
                      below_close (M := M) (b := b) hpe hMlt'
                    have hupd : upDec P d = 0 := upDec_zero_of_T_lt hdZ hPdec hZeq hmZ hT
                    rw [hup0, hupd]
                  · have hup0 : up = 0 := by
                      rw [← hup]
                      exact elUp_below (by rw [hh_b]; omega) (by rw [hh_b]; omega)
                    have hfar : hp + 2 ≤ 2 ^ (9 + b) := by
                      have := hle2
                      rw [hh_b] at this
                      omega
                    have hT : hp * 2 ^ 128 + M < 2 ^ (137 + b) :=
                      below_far (M := M) (b := b) hfar hMlt'
                    have hupd : upDec P d = 0 := upDec_zero_of_T_lt hdZ hPdec hZeq hmZ hT
                    rw [hup0, hupd]
                · have hpe : hp = 2 ^ (9 + b) := by
                    have h1 := hge
                    rw [hh_b] at h1
                    omega
                  have hTeq : hp * 2 ^ 128 + M = 2 ^ (137 + b) + M := by rw [at_edge hpe]
                  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
                  · have hlor : (Rlo ||| lo64 (Wnorm w) t.lo) = 0 := by
                      have h1 : Rlo = 0 := by
                        rw [hRlo_eq]
                        have h2 : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64
                            + lo64 (Wnorm w) t.lo = 0 := by rw [hM, hM0]
                        rcases Nat.add_eq_zero_iff.mp h2 with ⟨h3, -⟩
                        rcases Nat.mul_eq_zero.mp h3 with h4 | h4
                        · exact h4
                        · exact absurd h4 (by decide : (2 : Nat) ^ 64 ≠ 0)
                      have h2 : lo64 (Wnorm w) t.lo = 0 := by
                        have h3 : exactRlo (Wnorm w) t.hi t.lo * 2 ^ 64
                            + lo64 (Wnorm w) t.lo = 0 := by rw [hM, hM0]
                        exact (Nat.add_eq_zero_iff.mp h3).2
                      rw [lor_eq_zero_iff]; exact ⟨h1, h2⟩
                    have hupv : up = m % 2 := by
                      rw [← hup]; exact elUp_tie_zero (by rw [hh_b]; exact hpe) hlor
                    have hupd : upDec P d = m % 2 :=
                      upDec_par_of_T_eq hdZ hPdec hZeq hmZ (by rw [hTeq]; omega)
                    rw [hupv, hupd]
                  · have hlor : (Rlo ||| lo64 (Wnorm w) t.lo) ≠ 0 := by
                      intro h1
                      rcases lor_eq_zero_iff.mp h1 with ⟨h2, h3⟩
                      have h4 : exactRlo (Wnorm w) t.hi t.lo = 0 := by rw [← hRlo_eq]; exact h2
                      rw [← hM, h4, h3] at hMpos
                      exact absurd hMpos (Nat.lt_irrefl 0)
                    have hupv : up = 1 := by
                      rw [← hup]; exact elUp_tie_ne (by rw [hh_b]; exact hpe) hlor
                    have hupd : upDec P d = 1 :=
                      upDec_one_of_T_gt hdZ hPdec hZeq hmZ (by rw [hTeq]; omega)
                    rw [hupv, hupd]
            · have hqneg : q < 0 := by omega
              have hdD : d = eD q t := by rw [← hP2]; exact valueTicks_d_neg hqneg hrow
              have hNs : eN q t = eH t * D + R := by rw [hNsplit, hRv, hD]
              have hPQ : P = Wnorm w * (eH t * D + R) * 2 ^ s := by
                rw [← hP1, ← hNs]
                exact valueTicks_neg hqneg hrow hs
              have hPdec : 2 * P = 2 * m * (D * 2 ^ (138 + s + b))
                  + 2 ^ (s + 1) * (D * (hp * 2 ^ 128 + M) + Wnorm w * R) := by
                have h := decomp_neg (W := Wnorm w) (H := eH t) (D := D) (R := R)
                  (Rhi := exactRhi (Wnorm w) t.hi t.lo) (M := M) (hp := hp) (m := m)
                  (b := b) (s := s) (P := P) hPQ hWH' hdec
                exact h
              have hZeq : D * (2 : Nat) ^ (138 + s + b) = 2 ^ (s + 1) * (D * 2 ^ (137 + b)) :=
                ZD D s b
              have hdZ : D * (2 : Nat) ^ (138 + s + b) = d * ulp P d := by
                rw [ulp_eq hB, hdD, ← hD]
              have hmZ : P / (D * 2 ^ (138 + s + b)) = m := by
                rw [← hq0m, hdZ]
              rcases Nat.lt_or_ge hh hp with habove | hle
              · have hgen : 2 ^ (9 + b) + 1 ≤ hp := by
                  have := habove
                  rw [hh_b] at this
                  omega
                have hup1 : up = 1 := by
                  rw [← hup]; exact elUp_above habove
                have hT : D * 2 ^ (137 + b) < D * (hp * 2 ^ 128 + M) + Wnorm w * R := by
                  have h1 : 2 ^ (137 + b) < hp * 2 ^ 128 := by
                    have h2 : (2 ^ (9 + b) + 1) * 2 ^ 128 ≤ hp * 2 ^ 128 :=
                      Nat.mul_le_mul_right _ hgen
                    have h4 : 2 ^ (9 + b) * 2 ^ 128 < (2 ^ (9 + b) + 1) * 2 ^ 128 := by
                      rw [Nat.add_mul, Nat.one_mul]
                      exact Nat.lt_add_of_pos_right (by decide : 0 < 2 ^ 128)
                    rw [← hh_mul128 b]
                    exact Nat.lt_of_lt_of_le h4 h2
                  have h4 : D * 2 ^ (137 + b) < D * (hp * 2 ^ 128) :=
                    Nat.mul_lt_mul_of_pos_left h1 hDpos'
                  have h5 : D * (hp * 2 ^ 128) ≤ D * (hp * 2 ^ 128 + M) :=
                    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
                  exact Nat.lt_of_lt_of_le h4 (Nat.le_trans h5 (Nat.le_add_right _ _))
                have hupd : upDec P d = 1 := upDec_one_of_T_gt hdZ hPdec hZeq hmZ hT
                rw [hup1, hupd]
              · rcases Nat.lt_or_ge hp hh with hlt | hge
                · rcases Nat.lt_or_ge (hh - 2) hp with hgt | hle2
                  · have hpe : hp = 2 ^ (9 + b) - 1 := by
                      have h1 := hlt
                      rw [hh_b] at h1
                      have h2 := hgt
                      rw [hh_b] at h2
                      omega
                    have hup0 : up = 0 := by
                      rw [← hup]
                      exact elUp_below (by rw [hh_b]; omega) (by rw [hh_b]; omega)
                    have hRlo_ne : Rlo ≠ 2 ^ 64 - 1 := by
                      intro he
                      have hu : elUndec hp hh Rlo (lo64 (Wnorm w) t.lo) = true := by
                        unfold elUndec
                        rw [hh_b, hpe, he]
                        simp
                      rw [hu] at hnotundec
                      have hqT : decide (q < 0) = true := decide_eq_true_eq.mpr hqneg
                      rw [hqT] at hnotundec
                      exact hnotundec rfl
                    have hMle : M ≤ 2 ^ 128 - 2 ^ 64 - 1 := by
                      have hRle : Rlo ≤ 2 ^ 64 - 2 := by omega
                      have h4 : exactRlo (Wnorm w) t.hi t.lo = Rlo := hRlo_eq.symm
                      rw [← hM, h4]
                      calc Rlo * 2 ^ 64 + lo64 (Wnorm w) t.lo
                          ≤ (2 ^ 64 - 2) * 2 ^ 64 + (2 ^ 64 - 1) :=
                            Nat.add_le_add (Nat.mul_le_mul_right _ hRle) (by omega)
                        _ = 2 ^ 128 - 2 ^ 64 - 1 := by
                            rw [Nat.sub_mul, ← pow64_128]
                    have hT : D * (hp * 2 ^ 128 + M) + Wnorm w * R < D * 2 ^ (137 + b) := by
                      have hshift := close_shift (D := D) (M := M) (W := Wnorm w) (R := R)
                        (hp := hp) (b := b) hpe
                      have hlt2 : D * M + Wnorm w * R < D * 2 ^ 128 := by
                        have h1 : D * M < D * (2 ^ 128 - 2 ^ 64) :=
                          Nat.mul_lt_mul_of_pos_left (by omega) hDpos'
                        have h2 : D * M + Wnorm w * R < D * (2 ^ 128 - 2 ^ 64) + 2 ^ 64 * D :=
                          Nat.add_lt_add h1 hWfR'
                        have h3 : D * (2 ^ 128 - 2 ^ 64) + 2 ^ 64 * D = D * 2 ^ 128 := by
                          rw [Nat.mul_comm (2 ^ 64) D, ← Nat.mul_add,
                            Nat.sub_add_cancel (by omega : 2 ^ 64 ≤ 2 ^ 128)]
                        rw [h3] at h2
                        exact h2
                      omega
                    have hupd : upDec P d = 0 := upDec_zero_of_T_lt hdZ hPdec hZeq hmZ hT
                    rw [hup0, hupd]
                  · have hup0 : up = 0 := by
                      rw [← hup]
                      exact elUp_below (by rw [hh_b]; omega) (by rw [hh_b]; omega)
                    have hfar : hp + 2 ≤ 2 ^ (9 + b) := by
                      have := hle2
                      rw [hh_b] at this
                      omega
                    have hT : D * (hp * 2 ^ 128 + M) + Wnorm w * R < D * 2 ^ (137 + b) :=
                      below_far_scaled hDpos' hMlt' hWfR' hfar
                    have hupd : upDec P d = 0 := upDec_zero_of_T_lt hdZ hPdec hZeq hmZ hT
                    rw [hup0, hupd]
                · have hpe : hp = 2 ^ (9 + b) := by
                    have h1 := hge
                    rw [hh_b] at h1
                    omega
                  have hlor : (Rlo ||| lo64 (Wnorm w) t.lo) ≠ 0 := by
                    intro he
                    have hu : elUndec hp hh Rlo (lo64 (Wnorm w) t.lo) = true := by
                      unfold elUndec
                      rw [hh_b, hpe, he]
                      simp
                    rw [hu] at hnotundec
                    have hqT : decide (q < 0) = true := decide_eq_true_eq.mpr hqneg
                    rw [hqT] at hnotundec
                    exact hnotundec rfl
                  have hupv : up = 1 := by
                    rw [← hup]; exact elUp_tie_ne (by rw [hh_b]; exact hpe) hlor
                  have hTeq := at_edge_scaled (W := Wnorm w) (R := R) (M := M) (D := D)
                    (b := b) hpe
                  have hpos : 0 < D * M + Wnorm w * R := by
                    have hRpos' : 0 < R := by rw [← hRv]; exact hRpos hqneg
                    have hWpos : 0 < Wnorm w := by omega
                    have h1 : 0 < Wnorm w * R := Nat.mul_pos hWpos hRpos'
                    omega
                  have hT : D * 2 ^ (137 + b) < D * (hp * 2 ^ 128 + M) + Wnorm w * R := by
                    rw [hTeq]; omega
                  have hupd : upDec P d = 1 := upDec_one_of_T_gt hdZ hPdec hZeq hmZ hT
                  rw [hupv, hupd]
          have heu' : eu = 180 + ((10 + ub0 + (m + up) / 2 ^ 53 : Nat) : Int)
              + t.e - (lz w : Int) := by
            rw [← heu, ← hsh2, hub_eq]
          have hmant : (m + up) % 2 ^ 52 = (P / (d * ulp P d) + upDec P d) % 2 ^ 52 := by
            rw [hq0m, hupD]
          have hov : ub0 + (m + up) / 2 ^ 53
              = b + (P / (d * ulp P d) + upDec P d) / 2 ^ 53 := by
            rw [hq0m, hupD, ← hub_eq, ← hb_eq]
          rw [hP1, hP2, hnc, normalCode_eq_form hB52 hq0lo hq0hi, hB, hc, heu']
          exact congrArg Mag.fin
            (code_agree (s := s) (e := t.e) (lzw := lz w) hs hmant hov)
        · exact absurd hg (by simp)
    · -- ================= far =================
      rename_i hnotwin0
      have hfar : ¬ (hh0 - 2 ≤ hp0 ∧ hp0 ≤ hh0) := by
        intro hc
        have h1 : inWindow hp0 hh0 = true := (inWindow_iff hhh0pos hhh0le hhp0_lt).mpr hc
        rw [h1] at hnotwin0
        exact absurd hnotwin0 (by simp)
      unfold elFar at hg
      dsimp only at hg
      obtain ⟨mf, hmf⟩ : ∃ A, Ahi / 2 ^ sh0 = A := ⟨_, rfl⟩
      obtain ⟨uf, huf⟩ : ∃ A, (if hp0 > hh0 then 1 else 0) = A := ⟨_, rfl⟩
      obtain ⟨sh2, hsh2⟩ : ∃ A, 10 + ub0 + (mf + uf) / 2 ^ 53 = A := ⟨_, rfl⟩
      obtain ⟨eu, heu⟩ : ∃ A, 180 + (sh2 : Int) + t.e - (lz w : Int) = A := ⟨_, rfl⟩
      simp only [hmf, huf] at hg
      unfold elPack at hg
      dsimp only at hg
      simp only [hsh2, heu] at hg
      split at hg
      · rename_i hrange
        have hc : c = ⟨(eu + 1023).toNat, 2 ^ 52 + (mf + uf) % 2 ^ 52⟩ :=
          (Option.some.inj hg).symm
        obtain ⟨cy, hcy⟩ : ∃ A,
            (if exactRlo (Wnorm w) t.hi t.lo < lo64 (Wnorm w) t.hi then 1 else 0) = A := ⟨_, rfl⟩
        have hcy_le : cy ≤ 1 := by rw [← hcy]; split <;> omega
        have hRhi_def : exactRhi (Wnorm w) t.hi t.lo = Ahi + cy := by
          rw [exactRhi_eq (lo := t.lo) hWlt hhihi, hAhi, hcy]
        have hAhi_le : Ahi ≤ 2 ^ 64 - 2 := by rw [← hAhi]; exact hi64_le hWlt hhihi
        have hbu : ub0 ≤ b := by
          rcases Nat.lt_or_ge ub0 1 with h0 | h1
          · omega
          · have h1' : ub0 = 1 := by omega
            have hge : 2 ^ 63 ≤ Ahi := by
              rw [← hub0] at h1'
              rcases Nat.lt_or_ge Ahi (2 ^ 63) with h | h
              · exfalso
                have hz : Ahi / 2 ^ 63 = 0 := Nat.div_eq_of_lt h
                omega
              · exact h
            have hb1 : b = 1 := by
              rw [hb]
              have h2 : 2 ^ 191 * eD q t ≤ Wnorm w * eN q t := by
                rw [hNsplit]
                exact bit_one hWH' (by rw [hRhi_def]; omega)
              rw [ite_eq_left h2]
            omega
        have hb_le : b ≤ 1 := by rw [hb]; split <;> omega
        obtain ⟨q0, hq0⟩ : ∃ A, exactRhi (Wnorm w) t.hi t.lo / 2 ^ (10 + b) = A := ⟨_, rfl⟩
        obtain ⟨hpx, hhpx⟩ : ∃ A, exactRhi (Wnorm w) t.hi t.lo % 2 ^ (10 + b) = A := ⟨_, rfl⟩
        have hdecr : exactRhi (Wnorm w) t.hi t.lo = q0 * 2 ^ (10 + b) + hpx := by
          have h := (Nat.div_add_mod (exactRhi (Wnorm w) t.hi t.lo) (2 ^ (10 + b))).symm
          rw [hq0, hhpx, Nat.mul_comm] at h
          exact h
        have hpx_lt : hpx < 2 ^ (10 + b) := by rw [← hhpx]; exact Nat.mod_lt _ (pow2_pos _)
        have hdb : (2 : Nat) ^ (10 + b) = 2 * 2 ^ (9 + b) := by
          rw [show 10 + b = (9 + b) + 1 from by omega, Nat.pow_succ, Nat.mul_comm]
        obtain ⟨D, hD⟩ : ∃ A, (if 0 ≤ q then 1 else eD q t) = A := ⟨_, rfl⟩
        obtain ⟨R, hRv⟩ : ∃ A, (if 0 ≤ q then 0 else eN q t % eD q t) = A := ⟨_, rfl⟩
        have hD1 : 0 ≤ q → D = 1 := by intro hq; rw [← hD]; simp [hq]
        have hDe : ¬ 0 ≤ q → D = eD q t := by intro hq; rw [← hD]; simp [hq]
        have hR0 : 0 ≤ q → R = 0 := by intro hq; rw [← hRv]; simp [hq]
        have hRe : ¬ 0 ≤ q → R = eN q t % eD q t := by intro hq; rw [← hRv]; simp [hq]
        have hDpos' : 0 < D := by
          by_cases hq : 0 ≤ q
          · rw [hD1 hq]; omega
          · rw [hDe hq]; exact hDpos
        have hWfR' : Wnorm w * R < 2 ^ 64 * D := by
          by_cases hq : 0 ≤ q
          · rw [hR0 hq, hD1 hq, Nat.mul_zero, Nat.mul_one]; exact pow2_pos 64
          · rw [hRe hq, hDe hq]; exact hWfR
        have hPQ : P = Wnorm w * (eH t * D + R) * 2 ^ s := by
          by_cases hq : 0 ≤ q
          · rw [hD1 hq, hR0 hq, Nat.mul_one, Nat.add_zero, ← hP1]
            exact valueTicks_nonneg hq hrow hs
          · rw [hDe hq, hRe hq, ← hNsplit, ← hP1]
            exact valueTicks_neg (by omega) hrow hs
        have hPdec : 2 * P = 2 * q0 * (D * 2 ^ (138 + s + b))
            + 2 ^ (s + 1) * (D * (hpx * 2 ^ 128 + M) + Wnorm w * R) := by
          by_cases hq : 0 ≤ q
          · rw [hD1 hq, hR0 hq] at hPQ
            simp only [Nat.mul_one, Nat.add_zero] at hPQ
            rw [hD1 hq, hR0 hq]
            simp only [Nat.one_mul, Nat.mul_zero, Nat.add_zero]
            exact decomp_nonneg hPQ hWH' hdecr
          · rw [hDe hq, hRe hq] at hPQ
            rw [hDe hq, hRe hq]
            exact decomp_neg (W := Wnorm w) (H := eH t) (D := eD q t) (R := eN q t % eD q t)
              (Rhi := exactRhi (Wnorm w) t.hi t.lo) (M := M) (hp := hpx) (m := q0) (b := b)
              (s := s) (P := P) hPQ hWH' hdecr
        have hZeq : D * (2 : Nat) ^ (138 + s + b) = 2 ^ (s + 1) * (D * 2 ^ (137 + b)) :=
          ZD D s b
        have hZpos : 0 < D * (2 : Nat) ^ (138 + s + b) := Nat.mul_pos hDpos' (pow2_pos _)
        have hdZ : D * (2 : Nat) ^ (138 + s + b) = d * ulp P d := by
          by_cases hq : 0 ≤ q
          · have hd1 : d = 1 := by rw [← hP2]; exact valueTicks_d_nonneg hq
            rw [hD1 hq, ulp_eq hB, hd1, Nat.one_mul]
          · have hdD : d = eD q t := by rw [← hP2]; exact valueTicks_d_neg (by omega) hrow
            rw [hDe hq, ulp_eq hB, hdD]
        have hSig : hpx + 2 ≤ 2 ^ (10 + b) → P / (d * ulp P d) = q0 := by
          intro hpxp
          by_cases hq : 0 ≤ q
          · have h := sig_eq_m_nonneg hw0 hw hrow hq hs hsl (by rw [hP1, hP2]; exact hB)
            rw [hP1, hP2] at h
            rw [h, hq0]
          · have h := sig_eq_m_neg hw0 hw hrow (by omega) hs hsl
              (by rw [hP1, hP2]; exact hB) (by rw [hhpx]; exact hpxp)
            rw [hP1, hP2] at h
            rw [h, hq0]
        have hfull : P / (d * ulp P d) + upDec P d = 2 ^ 52 ∨ b = ub0 := by
          by_cases hbe : b = ub0
          · exact Or.inr hbe
          · left
            have hz0 : ub0 = 0 := by
              rcases Nat.lt_or_ge ub0 1 with h | h
              · omega
              · exact absurd hbe (by omega)
            have hb1 : b = 1 := by
              rcases Nat.lt_or_ge b 1 with h | h
              · omega
              · omega
            have hsh10 : sh0 = 10 := by rw [← hsh0, hz0]
            have hRge : 2 ^ 63 - 1 ≤ exactRhi (Wnorm w) t.hi t.lo := by
              rcases Nat.lt_or_ge (exactRhi (Wnorm w) t.hi t.lo) (2 ^ 63 - 1) with h | h
              · exfalso
                have h3 : exactRhi (Wnorm w) t.hi t.lo ≤ 2 ^ 63 - 2 := by omega
                have h1 : b = 0 := by
                  rw [hb]
                  have h2 : ¬ (2 ^ 191 * eD q t ≤ Wnorm w * eN q t) := by
                    rw [hNsplit]
                    exact Nat.not_le.mpr (bit_zero hWlt hDpos hRlt hMlt' hWH' h3)
                  rw [ite_eq_right h2]
                omega
              · exact h
            have hA63 : 2 ^ 63 - 2 ≤ Ahi := by rw [hRhi_def] at hRge; omega
            have hAhi_cases : Ahi = 2 ^ 63 - 2 ∨ Ahi = 2 ^ 63 - 1 := by omega
            have hRle : exactRhi (Wnorm w) t.hi t.lo ≤ 2 ^ 63 := by
              rw [hRhi_def]; omega
            rcases Nat.lt_or_ge (exactRhi (Wnorm w) t.hi t.lo) (2 ^ 63) with hR | hR
            · have hR1 : exactRhi (Wnorm w) t.hi t.lo = 2 ^ 63 - 1 := by omega
              have hq0v : q0 = 2 ^ 52 - 1 := by rw [← hq0, hR1, hb1]
              have hpxv : hpx = 2 ^ 11 - 1 := by rw [← hhpx, hR1, hb1]
              have hpfx : hpx = 2 ^ (10 + b) - 1 := by rw [hpxv, hb1]
              have hge : 2 ^ (9 + b) + 1 ≤ hpx := by rw [hpfx, hdb]; omega
              have hTgt : D * 2 ^ (137 + b) < D * (hpx * 2 ^ 128 + M) + Wnorm w * R :=
                Tgt_neg (M := M) hDpos' hge
              have hTlt3 : D * (hpx * 2 ^ 128 + M) + Wnorm w * R
                  < 3 * (D * 2 ^ (137 + b)) := Tlt3_neg_full hDpos' hWfR' hMlt' hpfx
              have hms : P / (d * ulp P d) + upDec P d = q0 + 1 :=
                mm_succ hdZ hZpos hPdec hZeq hTgt hTlt3
              rw [hms, hq0v, Nat.sub_add_cancel (show 1 ≤ (2 : Nat) ^ 52 from by decide)]
            · have hR1 : exactRhi (Wnorm w) t.hi t.lo = 2 ^ 63 := by omega
              have hq0v : q0 = 2 ^ 52 := by rw [← hq0, hR1, hb1]
              have hpxv : hpx = 0 := by rw [← hhpx, hR1, hb1]
              have hpxp : hpx + 2 ≤ 2 ^ (10 + b) := by rw [hpxv, hb1]; omega
              have hm : P / (D * 2 ^ (138 + s + b)) = q0 := by
                rw [hdZ]; exact hSig hpxp
              have hT : D * (hpx * 2 ^ 128 + M) + Wnorm w * R < D * 2 ^ (137 + b) :=
                below_far_scaled hDpos' hMlt' hWfR' (by rw [hpxv, hb1]; omega)
              have hms := mm_zero hdZ hPdec hZeq hm hT
              rw [hms, hq0v]
        have hMM : mf + uf = (P / (d * ulp P d) + upDec P d) + (b - ub0) * 2 ^ 52 := by
          by_cases hAB : ub0 = b
          · have hsh0b : sh0 = 10 + b := by rw [← hsh0, ← hAB]
            have hhh0b : hh0 = 2 ^ (9 + b) := by rw [← hhh0, ← hAB]
            have hAhiB : Ahi = mf * 2 ^ (10 + b) + hp0 := by
              have h := (Nat.div_add_mod Ahi (2 ^ sh0)).symm
              rw [hmf, hhp0, hsh0b, Nat.mul_comm] at h
              exact h
            have hk0 : b - ub0 = 0 := by omega
            have hhp0lt : hp0 < 2 ^ (10 + b) := by
              rw [← hhp0, hsh0b]; exact Nat.mod_lt _ (pow2_pos _)
            have hmodE : hpx = (hp0 + cy) % 2 ^ (10 + b) := by
              rw [← hhpx, hRhi_def, hAhiB, Nat.add_assoc, mod_slice]
            have hdivE : q0 = (hp0 + cy) / 2 ^ (10 + b) + mf := by
              rw [← hq0, hRhi_def, hAhiB, Nat.add_assoc,
                Nat.add_comm (mf * 2 ^ (10 + b)) (hp0 + cy),
                Nat.add_mul_div_right _ _ (pow2_pos _)]
            have hcyv : cy = 0 ∨ cy = 1 := by omega
            have huf0 : hp0 ≤ hh0 → uf = 0 := by
              intro h
              rw [← huf]
              exact ite_eq_right (by omega)
            have huf1 : hh0 < hp0 → uf = 1 := by
              intro h
              rw [← huf]
              exact ite_eq_left (by omega)
            by_cases hpfx : hpx = 2 ^ (10 + b) - 1
            · have hsum : hp0 + cy = 2 ^ (10 + b) - 1 := by
                have h1 : (hp0 + cy) % 2 ^ (10 + b) = 2 ^ (10 + b) - 1 := by
                  rw [← hmodE, hpfx]
                rcases Nat.lt_or_ge (hp0 + cy) (2 ^ (10 + b)) with h3 | h3
                · rwa [Nat.mod_eq_of_lt h3] at h1
                · have h4 : (hp0 + cy) % 2 ^ (10 + b) = 0 := by
                    rcases Nat.eq_or_lt_of_le h3 with h5 | h5
                    · rw [h5, Nat.mod_self]
                    · exact absurd h5 (by omega)
                  omega
              have hq0mf : q0 = mf := by
                rw [hdivE, hsum, Nat.div_eq_of_lt (by omega), Nat.zero_add]
              have huf1' : uf = 1 := by
                rw [← huf]
                exact ite_eq_left (by rw [hhh0b]; omega)
              have hge : 2 ^ (9 + b) + 1 ≤ hpx := by
                rw [hpfx, hdb]
                have h2 : 2 ≤ (2 : Nat) ^ (9 + b) := by
                  calc (2 : Nat) = 2 ^ 1 := rfl
                    _ ≤ 2 ^ (9 + b) := Nat.pow_le_pow_right (by decide) (by omega)
                omega
              have hTgt : D * 2 ^ (137 + b) < D * (hpx * 2 ^ 128 + M) + Wnorm w * R :=
                Tgt_neg (M := M) hDpos' hge
              have hTlt3 : D * (hpx * 2 ^ 128 + M) + Wnorm w * R
                  < 3 * (D * 2 ^ (137 + b)) := Tlt3_neg_full hDpos' hWfR' hMlt' hpfx
              have hms : P / (d * ulp P d) + upDec P d = q0 + 1 :=
                mm_succ hdZ hZpos hPdec hZeq hTgt hTlt3
              rw [hk0, Nat.zero_mul, Nat.add_zero, huf1', hms, hq0mf]
            · have hpxp : hpx + 2 ≤ 2 ^ (10 + b) := by omega
              have hmq : P / (d * ulp P d) = q0 := hSig hpxp
              have hm : P / (D * 2 ^ (138 + s + b)) = q0 := by rw [hdZ]; exact hmq
              rcases hcyv with hcy0 | hcy1
              · have hpx0 : hpx = hp0 := by
                  rw [hmodE, hcy0, Nat.add_zero, Nat.mod_eq_of_lt hhp0lt]
                have hq0v : q0 = mf := by
                  rw [hdivE, hcy0, Nat.add_zero, Nat.div_eq_of_lt hhp0lt, Nat.zero_add]
                rcases Nat.lt_or_ge hp0 (hh0 + 1) with hbelow | habove
                · have hT : D * (hpx * 2 ^ 128 + M) + Wnorm w * R < D * 2 ^ (137 + b) :=
                    below_far_scaled hDpos' hMlt' hWfR'
                      (by rw [hpx0]; rw [hhh0b] at hbelow; omega)
                  have hms := mm_zero hdZ hPdec hZeq hm hT
                  have huf0' : uf = 0 := huf0 (by omega)
                  rw [hk0, Nat.zero_mul, Nat.add_zero, huf0', hms, hq0v, Nat.add_zero]
                · have hge : 2 ^ (9 + b) + 1 ≤ hpx := by
                    rw [hpx0]; rw [hhh0b] at habove; omega
                  have hTgt : D * 2 ^ (137 + b) < D * (hpx * 2 ^ 128 + M) + Wnorm w * R :=
                    Tgt_neg (M := M) hDpos' hge
                  have hTlt3 : D * (hpx * 2 ^ 128 + M) + Wnorm w * R
                      < 3 * (D * 2 ^ (137 + b)) := Tlt3_neg_above hDpos' hWfR' hMlt' hpxp
                  have hms := mm_succ hdZ hZpos hPdec hZeq hTgt hTlt3
                  have huf1' : uf = 1 := huf1 (by rw [hhh0b]; omega)
                  rw [hk0, Nat.zero_mul, Nat.add_zero, huf1', hms, hq0v]
              · by_cases hpf0 : hp0 = 2 ^ (10 + b) - 1
                · have hpx0 : hpx = 0 := by
                    rw [hmodE, hcy1, hpf0,
                      show (2 : Nat) ^ (10 + b) - 1 + 1 = 2 ^ (10 + b) from by omega,
                      Nat.mod_self]
                  have hq0v : q0 = mf + 1 := by
                    rw [hdivE, hcy1, hpf0,
                      show (2 : Nat) ^ (10 + b) - 1 + 1 = 2 ^ (10 + b) from by omega,
                      Nat.div_self (pow2_pos _), Nat.add_comm]
                  have hpxp : hpx + 2 ≤ 2 ^ (10 + b) := by rw [hpx0]; omega
                  have hm : P / (D * 2 ^ (138 + s + b)) = q0 := by rw [hdZ]; exact hSig hpxp
                  have hT : D * (hpx * 2 ^ 128 + M) + Wnorm w * R < D * 2 ^ (137 + b) :=
                    below_far_scaled hDpos' hMlt' hWfR' (by rw [hpx0]; omega)
                  have hms := mm_zero hdZ hPdec hZeq hm hT
                  have huf1' : uf = 1 := huf1 (by rw [hhh0b]; omega)
                  rw [hk0, Nat.zero_mul, Nat.add_zero, huf1', hms, hq0v]
                · have hhplt : hp0 + 1 < 2 ^ (10 + b) := by omega
                  have hpx1 : hpx = hp0 + 1 := by rw [hmodE, hcy1, Nat.mod_eq_of_lt hhplt]
                  have hq0v : q0 = mf := by
                    rw [hdivE, hcy1, Nat.div_eq_of_lt hhplt, Nat.zero_add]
                  rcases Nat.lt_or_ge hp0 (hh0 + 1) with hbelow | habove
                  · have hT : D * (hpx * 2 ^ 128 + M) + Wnorm w * R < D * 2 ^ (137 + b) :=
                      below_far_scaled hDpos' hMlt' hWfR'
                        (by rw [hpx1]; rw [hhh0b] at hbelow; omega)
                    have hms := mm_zero hdZ hPdec hZeq hm hT
                    have huf0' : uf = 0 := huf0 (by omega)
                    rw [hk0, Nat.zero_mul, Nat.add_zero, huf0', hms, hq0v, Nat.add_zero]
                  · have hge : 2 ^ (9 + b) + 1 ≤ hpx := by
                      rw [hpx1]; rw [hhh0b] at habove; omega
                    have hTgt : D * 2 ^ (137 + b) < D * (hpx * 2 ^ 128 + M) + Wnorm w * R :=
                      Tgt_neg (M := M) hDpos' hge
                    by_cases hpxf : hpx = 2 ^ (10 + b) - 1
                    · have hTlt3 : D * (hpx * 2 ^ 128 + M) + Wnorm w * R
                          < 3 * (D * 2 ^ (137 + b)) := Tlt3_neg_full hDpos' hWfR' hMlt' hpxf
                      have hms := mm_succ hdZ hZpos hPdec hZeq hTgt hTlt3
                      have huf1' : uf = 1 := huf1 (by rw [hhh0b]; omega)
                      rw [hk0, Nat.zero_mul, Nat.add_zero, huf1', hms, hq0v]
                    · have hpxp2 : hpx + 2 ≤ 2 ^ (10 + b) := by omega
                      have hTlt3 : D * (hpx * 2 ^ 128 + M) + Wnorm w * R
                          < 3 * (D * 2 ^ (137 + b)) := Tlt3_neg_above hDpos' hWfR' hMlt' hpxp2
                      have hms := mm_succ hdZ hZpos hPdec hZeq hTgt hTlt3
                      have huf1' : uf = 1 := huf1 (by rw [hhh0b]; omega)
                      rw [hk0, Nat.zero_mul, Nat.add_zero, huf1', hms, hq0v]
          · have hz0 : ub0 = 0 := by
              rcases Nat.lt_or_ge ub0 1 with h | h
              · omega
              · exact absurd hAB (by omega)
            have hb1 : b = 1 := by
              rcases Nat.lt_or_ge b 1 with h | h
              · omega
              · omega
            have hsh10 : sh0 = 10 := by rw [← hsh0, hz0]
            have hhh512 : hh0 = 512 := by rw [← hhh0, hz0]
            have hRge : 2 ^ 63 - 1 ≤ exactRhi (Wnorm w) t.hi t.lo := by
              rcases Nat.lt_or_ge (exactRhi (Wnorm w) t.hi t.lo) (2 ^ 63 - 1) with h | h
              · exfalso
                have h3 : exactRhi (Wnorm w) t.hi t.lo ≤ 2 ^ 63 - 2 := by omega
                have h1 : b = 0 := by
                  rw [hb]
                  have h2 : ¬ (2 ^ 191 * eD q t ≤ Wnorm w * eN q t) := by
                    rw [hNsplit]
                    exact Nat.not_le.mpr (bit_zero hWlt hDpos hRlt hMlt' hWH' h3)
                  rw [ite_eq_right h2]
                omega
              · exact h
            have hA63 : 2 ^ 63 - 2 ≤ Ahi := by rw [hRhi_def] at hRge; omega
            have hAhi_cases : Ahi = 2 ^ 63 - 2 ∨ Ahi = 2 ^ 63 - 1 := by omega
            have hmf53 : mf = 2 ^ 53 - 1 := by
              have h1 : mf = Ahi / 2 ^ 10 := by rw [← hmf, hsh10]
              rw [h1]
              rcases hAhi_cases with h | h
              · rw [h]
              · rw [h]
            have huf1' : uf = 1 := by
              rw [← huf]
              have h1 : hp0 = Ahi % 2 ^ 10 := by rw [← hhp0, hsh10]
              rw [hhh512, ite_eq_left]
              rw [h1]
              rcases hAhi_cases with h | h
              · rw [h]; decide
              · rw [h]; decide
            rw [hz0, hb1, Nat.sub_zero, Nat.one_mul, huf1', hmf53]
            rcases hfull with h | h
            · rw [h, Nat.sub_add_cancel (show 1 ≤ (2 : Nat) ^ 53 from by decide)]
            · exact absurd h (by omega)
        have heu' : eu = 180 + ((10 + ub0 + (mf + uf) / 2 ^ 53 : Nat) : Int)
            + t.e - (lz w : Int) := by
          rw [← heu, ← hsh2]
        have hmant : (mf + uf) % 2 ^ 52 = (P / (d * ulp P d) + upDec P d) % 2 ^ 52 := by
          rw [hMM, Nat.add_mul_mod_self_right]
        have hov : ub0 + (mf + uf) / 2 ^ 53
            = b + (P / (d * ulp P d) + upDec P d) / 2 ^ 53 := by
          by_cases hbe : b = ub0
          · rw [hMM]
            exact carry_agree hbu hb_le hub0le (Nat.le_trans hq0lo (Nat.le_add_right _ _))
              (Or.inl hbe)
          · have hX : P / (d * ulp P d) + upDec P d = 2 ^ 52 := by
              rcases hfull with h | h
              · exact h
              · exact absurd h hbe
            have hk : b - ub0 = 1 := by omega
            have hmmv : mf + uf = 2 ^ 53 := by
              rw [hk, Nat.one_mul, hX] at hMM
              rw [hMM, show (2 : Nat) ^ 52 + 2 ^ 52 = 2 ^ 53 from by
                rw [← Nat.mul_two, ← Nat.pow_succ]]
            rw [hmmv, hX, show b = 1 from by omega, show ub0 = 0 from by omega]
        rw [hP1, hP2, hnc, normalCode_eq_form hB52 hq0lo hq0hi, hB, hc, heu']
        exact congrArg Mag.fin
          (code_agree (s := s) (e := t.e) (lzw := lz w) hs hmant hov)
      · exact absurd hg (by simp)

/-! ### Axiom footprint

Every declaration's footprint is a subset of `[propext, Quot.sound]`.  The
statement is computable, and the arithmetic stays at the standard footprint:
`omega` closes linear arithmetic without `Classical.choice` when its context
holds no existential, and `decide`-free rewriting adds nothing.

The composed binade theorems once carried `Classical.choice`:
`binade_prod`, `binade_quot` and, through them,
`binade_valueTicks_nonneg` and `binade_valueTicks_neg`.  The carrier was
`omega`, not any lemma: `ω` builds its atom list from the whole local context,
and a context holding the search's witness
`hex : ∃ B, B < 2100 ∧ P < 1 * 2 ^ (B + 1)` puts `Exists.choose` — that is,
`Classical.choose` — into that list.  The `ω` calls
that sat beside `hex` were only three index identities, so they are stated
above as `idx191`, `idx190` and `idx190_succ`, where no existential is in
scope, and applied by rewriting.  With that, the four theorems are at
`[propext, Quot.sound]` alongside the rest.

Stated positively as the rule this module follows: an `ω` call is made where its
local context holds no `∃` hypothesis.  Measured: the same `ω` goal closes at
`[propext, Quot.sound]` with an empty context and gains `Classical.choice` with
only `hex : ∃ B, B < 2100 ∧ P < 1 * 2 ^ (B + 1)` added beside it, whose proof
term mentions `hex.choose`.  `binade_unique` destructures `hex` through
`binade_spec` instead of through `ω`, which is why it never carried the
axiom. -/

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
#print axioms LeanLLVM.ElGuardRefine.ElGuardRefinesUnbounded
#print axioms LeanLLVM.ElGuardRefine.not_elGuardRefinesUnbounded
#print axioms LeanLLVM.ElGuardRefine.epowAt_bounds
#print axioms LeanLLVM.ElGuardRefine.pow10_45_lt
#print axioms LeanLLVM.ElGuardRefine.overflowTicks_ge
#print axioms LeanLLVM.ElGuardRefine.exactRhi_lt
#print axioms LeanLLVM.ElGuardRefine.slice_le
#print axioms LeanLLVM.ElGuardRefine.roundMag_eq_normalCode
#print axioms LeanLLVM.ElGuardRefine.elPack_range
#print axioms LeanLLVM.ElGuardRefine.carry_case_reachable
#print axioms LeanLLVM.ElGuardRefine.rem_lt_half
#print axioms LeanLLVM.ElGuardRefine.half_le_rem
#print axioms LeanLLVM.ElGuardRefine.discarded_lt
#print axioms LeanLLVM.ElGuardRefine.codeBits
#print axioms LeanLLVM.ElGuardRefine.epow_rows
#print axioms LeanLLVM.ElGuardRefine.rowB_row
#print axioms LeanLLVM.ElGuardRefine.row_of_epowAt
#print axioms LeanLLVM.ElGuardRefine.hi64_lt
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
#print axioms LeanLLVM.ElGuardRefine.idx191
#print axioms LeanLLVM.ElGuardRefine.idx190
#print axioms LeanLLVM.ElGuardRefine.idx190_succ
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
#print axioms LeanLLVM.ElGuardRefine.valueTicks_neg
#print axioms LeanLLVM.ElGuardRefine.valueTicks_d_neg
#print axioms LeanLLVM.ElGuardRefine.valueTicks_d_nonneg
#print axioms LeanLLVM.ElGuardRefine.binade_valueTicks
#print axioms LeanLLVM.ElGuardRefine.quot_split
#print axioms LeanLLVM.ElGuardRefine.sig_eq_m_nonneg
#print axioms LeanLLVM.ElGuardRefine.quot_residue_neg
#print axioms LeanLLVM.ElGuardRefine.sig_eq_m_neg
#print axioms LeanLLVM.ElGuardRefine.upDec
#print axioms LeanLLVM.ElGuardRefine.normalCode_eq_form
#print axioms LeanLLVM.ElGuardRefine.decomp_nonneg
#print axioms LeanLLVM.ElGuardRefine.decomp_neg
#print axioms LeanLLVM.ElGuardRefine.half_lt
#print axioms LeanLLVM.ElGuardRefine.half_gt
#print axioms LeanLLVM.ElGuardRefine.half_eq
#print axioms LeanLLVM.ElGuardRefine.half_le
#print axioms LeanLLVM.ElGuardRefine.mod_lt_half
#print axioms LeanLLVM.ElGuardRefine.mod_gt_half
#print axioms LeanLLVM.ElGuardRefine.mod_eq_half
#print axioms LeanLLVM.ElGuardRefine.above_far
#print axioms LeanLLVM.ElGuardRefine.at_edge
#print axioms LeanLLVM.ElGuardRefine.below_close
#print axioms LeanLLVM.ElGuardRefine.below_far
#print axioms LeanLLVM.ElGuardRefine.above_scaled
#print axioms LeanLLVM.ElGuardRefine.at_edge_scaled
#print axioms LeanLLVM.ElGuardRefine.close_shift
#print axioms LeanLLVM.ElGuardRefine.below_far_scaled
#print axioms LeanLLVM.ElGuardRefine.rhi_le_of_ub_zero
#print axioms LeanLLVM.ElGuardRefine.bit_one
#print axioms LeanLLVM.ElGuardRefine.bit_zero
#print axioms LeanLLVM.ElGuardRefine.pack_carry_agrees
#print axioms LeanLLVM.ElGuardRefine.sig_bounds
#print axioms LeanLLVM.ElGuardRefine.lor_eq_zero_iff
#print axioms LeanLLVM.ElGuardRefine.elTier2Code_reduce
#print axioms LeanLLVM.ElGuardRefine.sig_bounds_at
#print axioms LeanLLVM.ElGuardRefine.pack_exp
#print axioms LeanLLVM.ElGuardRefine.ulp_eq
#print axioms LeanLLVM.ElGuardRefine.Z0
#print axioms LeanLLVM.ElGuardRefine.ZD
#print axioms LeanLLVM.ElGuardRefine.upDec_zero_of_T_lt
#print axioms LeanLLVM.ElGuardRefine.upDec_one_of_T_gt
#print axioms LeanLLVM.ElGuardRefine.upDec_par_of_T_eq
#print axioms LeanLLVM.ElGuardRefine.carry_agree
#print axioms LeanLLVM.ElGuardRefine.code_agree
#print axioms LeanLLVM.ElGuardRefine.hi64_le
#print axioms LeanLLVM.ElGuardRefine.exactRhi_eq
#print axioms LeanLLVM.ElGuardRefine.pow_succ_mul
#print axioms LeanLLVM.ElGuardRefine.pow128
#print axioms LeanLLVM.ElGuardRefine.pow138
#print axioms LeanLLVM.ElGuardRefine.pow128_le
#print axioms LeanLLVM.ElGuardRefine.pow10_128
#print axioms LeanLLVM.ElGuardRefine.fullA
#print axioms LeanLLVM.ElGuardRefine.fullD
#print axioms LeanLLVM.ElGuardRefine.Tgt_neg
#print axioms LeanLLVM.ElGuardRefine.Tlt3_pos_above
#print axioms LeanLLVM.ElGuardRefine.Tlt3_neg_above
#print axioms LeanLLVM.ElGuardRefine.Tlt3_pos_full
#print axioms LeanLLVM.ElGuardRefine.Tlt3_neg_full
#print axioms LeanLLVM.ElGuardRefine.two_mul_two
#print axioms LeanLLVM.ElGuardRefine.mod_add_mul
#print axioms LeanLLVM.ElGuardRefine.split_of_two
#print axioms LeanLLVM.ElGuardRefine.div_slice
#print axioms LeanLLVM.ElGuardRefine.mm_of_T_between
#print axioms LeanLLVM.ElGuardRefine.mod_slice
#print axioms LeanLLVM.ElGuardRefine.div_slice'
#print axioms LeanLLVM.ElGuardRefine.mm_zero
#print axioms LeanLLVM.ElGuardRefine.mm_succ
#print axioms LeanLLVM.ElGuardRefine.elGuardRefinesOn

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

/-- What `roundMag` decides for a witness, in the same bits. -/
def witnessSpecBits (w : Nat) (q : Int) : Option Nat :=
  match roundMag (valueTicks w q).1 (valueTicks w q).2 with
  | .inf => none
  | .fin c => some (codeBits c)

/-- The guard's bits and the specification's, for a witness: `none` where the
guard refuses, and otherwise whether they are the same code. -/
def witnessAgrees (w : Nat) (q : Int) : Bool :=
  match witnessBits w q with
  | none => true
  | some b => witnessSpecBits w q == some b

-- Wherever the guard decides a witness, it decides what `roundMag` does.
#eval witnesses.all (fun (w, q) => witnessAgrees w q)
-- Each witness's two answers, so a disagreement is visible rather than counted.
#eval witnesses.map (fun (w, q) => (w, q, witnessBits w q, witnessSpecBits w q))

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
