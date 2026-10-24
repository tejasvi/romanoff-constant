import Romanoff.TBoundSpec

/-!
# U3g and V4g: the modulus with 15 primes, period 27720, and the target statements

The U3g and V4g certificates (Theorems 1.1 and 1.2 of the paper, modulus l_3) work with
the modulus `l_G = 3·5·7·11·13·17·31·241·41·19·73·37·23·43·29` (every `ord_p(2)` divides `27720`).
Target theorems (native track):

  `romanoff_U3g (h1 : ESP28 G.ell) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.U3gStatement`,
  `romanoff_V4g (h1 : ESP28 G.ell) (h2 : JTProp2) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.V4gStatement`,

i.e. `0.110825 ≤ liminf dens` from (I1) ESP (28) and (I3) PNT in progressions for the fixed modulus `l_G` and (I5)
`R0 < 1.93656`, and `0.119178 ≤ liminf dens` with (I2) Johnston–Trudgian Prop. 2 in addition: the inputs of `U2Statement` and `V3Statement`
(Romanoff/Defs.lean) at the new modulus. `ESP28`, `JTProp2`, `PNTAP`, `R0Bound` and `dens` are the definitions of
Romanoff/Defs.lean. The list `ellPrimes` holds the primes of the certificates' `ELL` in another order (the core primes
before the independent primes 23, 43, 29); `ell` is their product. Inside `namespace Romanoff.G` the names `ellPrimes`,
`ell`, `tw`, `TBound` and `TBoundA` denote the period-27720 versions; they shadow the U2 ones of `namespace Romanoff`.
-/

open Filter

namespace Romanoff.G

/-- The primes of the U3g/V4g modulus: the base primes 3, 5, 7, 11, 13, 17, 31, 241, the core added primes 41, 19, 73, 37
and the independent added primes 23, 43, 29. -/
def ellPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 31, 241, 41, 19, 73, 37, 23, 43, 29]

/-- `l_G = 3·5·7·11·13·17·31·241·41·19·73·37·23·43·29`. -/
def ell : ℕ := ellPrimes.prod

/-- U3g (unconditional): `0.110825 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
def U3gStatement : Prop := (110825 / 1000000 : ℝ) ≤ liminf dens atTop

/-- V4g (conditional on (I2)): `0.119178 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
def V4gStatement : Prop := (119178 / 1000000 : ℝ) ≤ liminf dens atTop

/-- `f(m) [g ∣ c] g / o_m`, `g = gcd(o_m, 27720)`. -/
noncomputable def tw (c m : ℕ) : ℝ :=
  if Nat.gcd (ordm m) 27720 ∣ c then fm m * (Nat.gcd (ordm m) 27720 : ℝ) / (ordm m : ℝ) else 0

/-- The `T(c)` bound at period 27720: `teff` has 27720 entries and, for every `c < 27720` and every finite set `S` of odd
squarefree `m` coprime to `l_G`, `Σ_{m ∈ S} tw c m ≤ teff[c]`. -/
def TBound (teff : List ℚ) : Prop :=
  teff.length = 27720 ∧ ∀ c < 27720, ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ell) →
    ∑ m ∈ S, tw c m ≤ ((teff.getD c 0 : ℚ) : ℝ)

/-- The `T(c)` bound at period 27720 with the class-(c) tail in alpha form (one `α ≥ 0` on the divisors of 27720 with
`Σ α ≤ R0t`, for all `c`). -/
def TBoundA (tab : List ℚ) (R0t : ℚ) : Prop :=
  tab.length = 27720 ∧ ∃ α : ℕ → ℝ, (∀ g, 0 ≤ α g) ∧ (∑ g ∈ Nat.divisors 27720, α g) ≤ (R0t : ℝ) ∧
    ∀ c < 27720, ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ell) →
      ∑ m ∈ S, tw c m ≤ ((tab.getD c 0 : ℚ) : ℝ) + ∑ g ∈ (Nat.divisors 27720).filter (· ∣ c), (g : ℝ) * α g

end Romanoff.G
