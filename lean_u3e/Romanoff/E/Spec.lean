import Romanoff.TBoundSpec

/-!
# U3e (Tao page 45a): the modulus with 13 primes, period 3960, and the target statement

The U3e certificate (certs_u3de/cert_u3e_23_37.json, checker u3e v5) works with the modulus
`l' = 3·5·7·11·13·17·31·241·41·19·73·23·37` (every `ord_p(2)` divides `3960`).
Target theorem (native track):

  `romanoff_U3e (h1 : ESP28 E.ell) (h3 : PNTAP E.ell) (h5 : R0Bound) : E.U3eStatement`,

i.e. `0.110449 ≤ liminf dens` from (I1) ESP (28) and (I3) PNT in progressions for the fixed modulus `l'`, and (I5)
`R0 < 1.93656` — the inputs of U2 (Romanoff/Defs.lean) at the new modulus; `ESP28`, `PNTAP`, `R0Bound`, `dens` are the
approved definitions of Romanoff/Defs.lean.  Inside `namespace Romanoff.E` the names `ellPrimes`, `ell`, `tw`, `TBound`
denote the U3e versions (period `3960`); they shadow the U2 ones of `namespace Romanoff`.
-/

open Filter

namespace Romanoff.E

/-- The primes of the U3e modulus (the base primes of U2 without 41, then the added primes 41, 19, 73, 23, 37). -/
def ellPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 31, 241, 41, 19, 73, 23, 37]

/-- `l' = 3·5·7·11·13·17·31·241·41·19·73·23·37`. -/
def ell : ℕ := ellPrimes.prod

/-- U3e (unconditional): `0.110449 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
def U3eStatement : Prop := (110449 / 1000000 : ℝ) ≤ liminf dens atTop

/-- `f(m) [g ∣ c] g / o_m`, `g = gcd(o_m, 3960)`. -/
noncomputable def tw (c m : ℕ) : ℝ :=
  if Nat.gcd (ordm m) 3960 ∣ c then fm m * (Nat.gcd (ordm m) 3960 : ℝ) / (ordm m : ℝ) else 0

/-- The `T(c)` bound at period 3960: `teff` has 3960 entries and, for every `c < 3960` and every finite set `S` of odd
squarefree `m` coprime to `l'`, `Σ_{m ∈ S} tw c m ≤ teff[c]`. -/
def TBound (teff : List ℚ) : Prop :=
  teff.length = 3960 ∧ ∀ c < 3960, ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ell) →
    ∑ m ∈ S, tw c m ≤ ((teff.getD c 0 : ℚ) : ℝ)

/-- The `T(c)` bound at period 3960 with the class-(c) tail in alpha form (one `α ≥ 0` on the divisors of 3960 with
`Σ α ≤ R0t`, for all `c`). -/
def TBoundA (tab : List ℚ) (R0t : ℚ) : Prop :=
  tab.length = 3960 ∧ ∃ α : ℕ → ℝ, (∀ g, 0 ≤ α g) ∧ (∑ g ∈ Nat.divisors 3960, α g) ≤ (R0t : ℝ) ∧
    ∀ c < 3960, ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ell) →
      ∑ m ∈ S, tw c m ≤ ((tab.getD c 0 : ℚ) : ℝ) + ∑ g ∈ (Nat.divisors 3960).filter (· ∣ c), (g : ℝ) * α g

end Romanoff.E
