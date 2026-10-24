import RCert.M3.Check

/-!
# M3 at period 27720 for the U3g/V4g modulus (core Lean)

The DP of M3 (`runDP`, `runDrop`, `tabTD`, `tabR`, the class-B group data) does not depend on the period; only the
accumulation by `g = gcd(L', PER)` and the table `teff` do.  This file repeats those definitions for `PER = 27720`
(96 divisors) and the modulus `l_G = 3·5·7·11·13·17·31·241·41·19·73·37·23·43·29`.

Change in `certOK`: for `l'` the orders 11 and 36 occur both among the primes of `l'` (23, 37) and among the other
primes (89, 109), so the condition "the orders of `gE` do not occur in `gA`" of M3 is replaced by "no prime of `gA`
divides `l'`" (the primes of `gA ++ gE` are then distinct because the `gE` primes divide `l'`).
-/

namespace R45.M3G

open R45.M3

/-- The period. -/
def PER : Nat := 27720

/-- The divisors of `27720`. -/
def divG : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 18, 20, 21, 22, 24, 28, 30, 33, 35, 36, 40, 42, 44, 45, 55, 56, 60,
  63, 66, 70, 72, 77, 84, 88, 90, 99, 105, 110, 120, 126, 132, 140, 154, 165, 168, 180, 198, 210, 220, 231, 252,
  264, 280, 308, 315, 330, 360, 385, 396, 420, 440, 462, 495, 504, 616, 630, 660, 693, 770, 792, 840, 924, 990,
  1155, 1260, 1320, 1386, 1540, 1848, 1980, 2310, 2520, 2772, 3080, 3465, 3960, 4620, 5544, 6930, 9240, 13860,
  27720]

/-- `acc_g += ⌈b g / L'⌉` with `L' = lcm(L, s)`, `g = gcd(L', 27720)`, over the entries with `1 ≤ L ≤ LMAX`
(96 accumulators, in the order of `divG`). -/
def accG (s : Nat) (tab : List Ent) : List Nat :=
  tab.foldl (fun acc x =>
    if 1 ≤ x.L ∧ x.L ≤ LMAX then
      let L2 := Nat.lcm x.L s
      let g := Nat.gcd L2 PER
      addAt g ((x.b * g + L2 - 1) / L2) divG acc
    else acc) (List.replicate 96 0)

/-- `Σ_{g ∣ c} acc_g`. -/
def sumDvd (acc : List Nat) (c : Nat) : Nat := sumDvdAux c divG acc

/-- The primes of `l'`. -/
def ellPs : List Nat := [3, 5, 7, 11, 13, 17, 31, 241, 41, 19, 73, 37, 23, 43, 29]

/-- The global check (as M3's `certOK`, with the disjointness of `gA` from the primes of `l'` in place of distinct
orders across `gA` and `gE`). -/
def certOK (D : Data) : Bool :=
  prattOK D.recs && D.groups.all grpOK && primeOK (D.recs.map (·.n)) (D.groups.flatMap (·.ps)) &&
    sortedLT (D.gA.map (·.t)) && sortedLT (D.gE.map (·.t)) && sortedLT (D.gB.map (·.1.t)) &&
    D.gA.all (fun g => g.ps.all fun p => !ellPs.contains p) &&
    D.gE.all (fun g => g.ps.all fun p => ellPs.contains p) &&
    (D.gA ++ D.gE).all (fun g => g.t ≤ 300) && D.gB.all (fun g => 300 < g.1.t && g.1.t ≤ 1200)

/-- The data of one class-B group (accumulators at period 27720). -/
def mkBD (tT tR : List Ent) (r0a : Nat) (gx : Grp × Bool) : BD :=
  let g := gx.1
  let FU := (g.ps.map fUp).sum
  let FL := (g.ps.map fLo).sum
  if gx.2 then ⟨FU, FL, g.t, true, accG g.t tT, sumR g.t tR⟩ else ⟨FU, FL, g.t, false, [], r0a / g.t⟩

/-- The pruned-mass term `⌈(∏ - Σ a) gcd(c, 27720) / LMAX⌉`. -/
def prC (prM c : Nat) : Nat := cdiv (prM * Nat.gcd c PER) LMAX

/-- The dropped-mass term `⌈gcd(c, 27720) ∏ D / SC⌉`. -/
def drC (piU dD c : Nat) : Nat := cdiv (Nat.gcd c PER * piU * dD) SC

/-- `T_b(c)`: `Σ_groups ⌈FU (A_t(c) + prune(c)) / SC⌉`. -/
def tbC (bs : List BD) (sB prc c : Nat) : Nat :=
  (bs.map fun d => mulUp d.FU ((if d.ex then sumDvd d.acc c else cdiv (sB * Nat.gcd c PER) d.t) + prc)).sum

/-- `teff` at period 27720 from the two tables, the dropped mass `dT` of the T table and the class-B data. -/
def teffOf (D : Data) (tT : List Ent) (dT : Nat) (tR : List Ent) (bs : List BD) : List Rat :=
  let acc := accG 1 tT
  let prM := piUp D.gA - sumA tT
  let piU := piUp D.gA
  let sB := sumB tT
  let tail : Rat := R0upQ - ((sumR 1 tR + r0bOf bs : Nat) : Rat) / (SC : Rat)
  (List.range PER).map fun c =>
    ((sumDvd acc c + (prC prM c + drC piU dT c) + tbC bs sB (prC prM c + drC piU dT c) c : Nat) : Rat) / (SC : Rat) +
      (Nat.gcd c PER : Rat) * tail

/-- The class-B data computed from the tables (period 27720). -/
def bsOf (D : Data) (tT tR : List Ent) : List BD := D.gB.map (mkBD tT tR (sumR 1 tR))

/-- The certified `teff` at period 27720. -/
def teffD (D : Data) : List Rat :=
  let st := tabTD D
  let tR := tabR D st.1
  teffOf D st.1 st.2 tR (bsOf D st.1 tR)

/-- The tail mass bound `R0up - (sumR 1 tR + r0bOf bs) / SC` of the tables. -/
def R0tD (D : Data) : Rat :=
  let st := tabTD D
  let tR := tabR D st.1
  R0upQ - ((sumR 1 tR + r0bOf (bsOf D st.1 tR) : Nat) : Rat) / (SC : Rat)

end R45.M3G
