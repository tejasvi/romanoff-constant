import RCert.M3.Core

/-!
# M3 checker: the certificate data, the global check and `teff`

* `gA`: groups of certified primes of order `≤ 300` not dividing `ell` (the T-DP);
* `gE`: groups of certified primes dividing `ell` (added to the T-DP table for the `R0` lower bound);
* `gB`: groups of certified primes of order in `(300, 1200]`, each flagged `exact` (one pass over the T table) or not
  (the crude bounds `lcm(L, t) ≥ t`, resp. `lcm(L, t) ≤ t L`).

`teff c = (T_a(c) + prune(c) + T_b(c)) / SC + gcd(c, 120) · R0tail`, `R0tail = R0up - (R0a + R0b) / SC`.
-/

namespace R45.M3

/-- The primes of `ell`. -/
def ellPs : List Nat := [3, 5, 7, 11, 13, 17, 31, 41, 241]

/-- The certificate data. -/
structure Data where
  recs : List PRec
  gA : List Grp
  gE : List Grp
  gB : List (Grp × Bool)

/-- All groups. -/
def Data.groups (D : Data) : List Grp := D.gA ++ D.gE ++ D.gB.map (·.1)

/-- The global check: Pratt records, exact orders, primes certified, orders distinct across the groups, the `gE` primes
divide `ell`, orders of `gA`, `gE` at most `300` and of `gB` in `(300, 1200]`. -/
def certOK (D : Data) : Bool :=
  prattOK D.recs && D.groups.all grpOK && primeOK (D.recs.map (·.n)) (D.groups.flatMap (·.ps)) &&
    sortedLT (D.gA.map (·.t)) && sortedLT (D.gE.map (·.t)) && sortedLT (D.gB.map (·.1.t)) &&
    D.gE.all (fun g => !(D.gA.map (·.t)).contains g.t) &&
    D.gE.all (fun g => g.ps.all fun p => ellPs.contains p) &&
    (D.gA ++ D.gE).all (fun g => g.t ≤ 300) && D.gB.all (fun g => 300 < g.1.t && g.1.t ≤ 1200)

/-- The T table with its dropped mass, and the R0 table. -/
def tabTD (D : Data) : List Ent × Nat := runDPD tab0 0 D.gA
def tabR (D : Data) (tT : List Ent) : List Ent := runDP tT D.gE

/-- The data of one class-B group: `Σ ⌈SC/(q-2)⌉`, `Σ ⌊SC/(q-2)⌋`, the order, exact or not, the 16 accumulators of the
pass over the T table (exact groups), and the R0 sum (exact: `Σ ⌊a / lcm(L, t)⌋`; crude: `⌊R0a / t⌋`). -/
structure BD where
  FU : Nat
  FL : Nat
  t : Nat
  ex : Bool
  acc : List Nat
  r : Nat

def mkBD (tT tR : List Ent) (r0a : Nat) (gx : Grp × Bool) : BD :=
  let g := gx.1
  let FU := (g.ps.map fUp).sum
  let FL := (g.ps.map fLo).sum
  if gx.2 then ⟨FU, FL, g.t, true, accG g.t tT, sumR g.t tR⟩ else ⟨FU, FL, g.t, false, [], r0a / g.t⟩

/-- The pruned-mass term `⌈(∏ - Σ a) gcd(c, 120) / LMAX⌉`. -/
def prC (prM c : Nat) : Nat := cdiv (prM * Nat.gcd c PER) LMAX

/-- The dropped-mass term `⌈gcd(c, 120) ∏ D / SC⌉`. -/
def drC (piU dD c : Nat) : Nat := cdiv (Nat.gcd c PER * piU * dD) SC

/-- `T_b(c)`: `Σ_groups ⌈FU (A_t(c) + prune(c)) / SC⌉`. -/
def tbC (bs : List BD) (sB prc c : Nat) : Nat :=
  (bs.map fun d => mulUp d.FU ((if d.ex then sumDvd d.acc c else cdiv (sB * Nat.gcd c PER) d.t) + prc)).sum

/-- `R0b`: `Σ_groups ⌊FL r / SC⌋`. -/
def r0bOf (bs : List BD) : Nat := (bs.map fun d => mulLo d.FL d.r).sum

/-- The upper bound `R0 < 1.93656`. -/
def R0upQ : Rat := (193656 : Rat) / 100000

/-- `teff` from the two tables, the dropped mass `dT` of the T table and the class-B data. -/
def teffOf (D : Data) (tT : List Ent) (dT : Nat) (tR : List Ent) (bs : List BD) : List Rat :=
  let acc := accG 1 tT
  let prM := piUp D.gA - sumA tT
  let piU := piUp D.gA
  let sB := sumB tT
  let tail : Rat := R0upQ - ((sumR 1 tR + r0bOf bs : Nat) : Rat) / (SC : Rat)
  (List.range PER).map fun c =>
    ((sumDvd acc c + (prC prM c + drC piU dT c) + tbC bs sB (prC prM c + drC piU dT c) c : Nat) : Rat) / (SC : Rat) +
      (Nat.gcd c PER : Rat) * tail

/-- The class-B data computed from the tables. -/
def bsOf (D : Data) (tT tR : List Ent) : List BD := D.gB.map (mkBD tT tR (sumR 1 tR))

/-- The certified `teff`. -/
def teffD (D : Data) : List Rat :=
  let st := tabTD D
  let tR := tabR D st.1
  teffOf D st.1 st.2 tR (bsOf D st.1 tR)

/-- The check on the computed tables: `Σ a ≤ ∏` (the pruned mass is a true difference). -/
def sumsOK (D : Data) (tT : List Ent) : Bool := sumA tT ≤ piUp D.gA

end R45.M3
