import Romanoff.Defs

/-!
# Interface of the singular-series bound `T(c)` (milestone M3)

`ordm m = ord_m(2)`; for `c < 120`, `tw c m = f(m) [g ∣ c] g / o_m`, `g = gcd(o_m, 120)`, `f(m) = ∏_{p ∣ m} 1/(p-2)`.
`TBound teff`: `teff` has 120 entries and, for every `c < 120` and every finite set `S` of odd squarefree `m` coprime
to `l`, `Σ_{m ∈ S} tw c m ≤ teff[c]`.  M3 delivers `TBound teffCert` from `R0Bound`, for a computed list
`teffCert : List ℚ` (`T_a(c) + T_b(c) + gcd(c, 120) · R0tail`); M4 runs the Lagrangian evaluation with these values.
-/

namespace Romanoff

/-- `o_m = ord_m(2)` (`= 1` for `m = 1`). -/
noncomputable def ordm (m : ℕ) : ℕ := orderOf (2 : ZMod m)

/-- `f(m) [g ∣ c] g / o_m`, `g = gcd(o_m, 120)`. -/
noncomputable def tw (c m : ℕ) : ℝ :=
  if Nat.gcd (ordm m) 120 ∣ c then fm m * (Nat.gcd (ordm m) 120 : ℝ) / (ordm m : ℝ) else 0

/-- The `T(c)` bound for a list of 120 rationals. -/
def TBound (teff : List ℚ) : Prop :=
  teff.length = 120 ∧ ∀ c < 120, ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ell) →
    ∑ m ∈ S, tw c m ≤ ((teff.getD c 0 : ℚ) : ℝ)

end Romanoff
