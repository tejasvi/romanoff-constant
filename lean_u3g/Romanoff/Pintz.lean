import Mathlib

/-!
# Pintz's inequality and the function `φ`

(I4) For integers `b ≥ 0` and `j ≥ 1`, `(b - j)(b - j - 1) ≥ 0` gives `b² ≥ (2j + 1) b - j(j + 1) [b > 0]`; summed,
`#{b > 0} j(j+1) ≥ (2j + 1) Σ b - Σ b²`.  `φ(D) = (2j + 1 - D)/(j(j + 1))` for `j = ⌊D⌋`, `D ≥ 1`, is the
piecewise-linear interpolation of `1/x` at the integers; it is affine on each `[j, j + 1]` and `1/2`-Lipschitz.
-/

open Finset

namespace Romanoff

theorem pintz_pointwise (b j : ℕ) (hj : 1 ≤ j) :
    (2 * (j : ℝ) + 1) * b - (j : ℝ) * (j + 1) * (if 0 < b then 1 else 0) ≤ (b : ℝ) ^ 2 := by
  split_ifs with hb
  · have h : 0 ≤ ((b : ℝ) - j) * ((b : ℝ) - j - 1) := by
      rcases le_or_gt b j with hbj | hbj
      · have h0 : (b : ℝ) ≤ j := by exact_mod_cast hbj
        have h1 : (b : ℝ) - j ≤ 0 := by linarith
        have h2 : (b : ℝ) - j - 1 ≤ 0 := by linarith
        nlinarith
      · have h1 : (j : ℝ) + 1 ≤ b := by exact_mod_cast hbj
        nlinarith
    nlinarith
  · have : b = 0 := by omega
    subst this
    simp

/-- Pintz (Lemma 4'): `j(j+1) #{b > 0} ≥ (2j + 1) Σ b - Σ b²`. -/
theorem pintz_sum {ι : Type*} (S : Finset ι) (b : ι → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    (2 * (j : ℝ) + 1) * ∑ i ∈ S, (b i : ℝ) - ∑ i ∈ S, (b i : ℝ) ^ 2 ≤
      (j : ℝ) * (j + 1) * ((S.filter fun i => 0 < b i).card : ℝ) := by
  have h := Finset.sum_le_sum (s := S) (fun i _ => pintz_pointwise (b i) j hj)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have hc : ∑ i ∈ S, (if 0 < b i then (1 : ℝ) else 0) = ((S.filter fun i => 0 < b i).card : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hc] at h
  linarith

/-- `φ(D) = (2j + 1 - D)/(j(j + 1))`, `j = ⌊D⌋` (for `D ≥ 1`). -/
noncomputable def phi (D : ℝ) : ℝ := (2 * (⌊D⌋₊ : ℝ) + 1 - D) / ((⌊D⌋₊ : ℝ) * ((⌊D⌋₊ : ℝ) + 1))

/-- On `[j, j + 1]`, `φ` is the affine function with index `j`. -/
theorem phi_eq_of_mem {D : ℝ} {j : ℕ} (hj : 1 ≤ j) (h1 : (j : ℝ) ≤ D) (h2 : D ≤ j + 1) :
    phi D = (2 * (j : ℝ) + 1 - D) / ((j : ℝ) * (j + 1)) := by
  unfold phi
  rcases eq_or_lt_of_le h2 with h | h
  · -- D = j + 1: both formulas give 1/(j+1)
    have hf : ⌊D⌋₊ = j + 1 := by rw [h]; exact_mod_cast Nat.floor_natCast (R := ℝ) (j + 1)
    rw [hf, h]; push_cast
    have : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp; ring
  · have hf : ⌊D⌋₊ = j := by
      rw [Nat.floor_eq_iff (by linarith)]; exact ⟨h1, h⟩
    rw [hf]

/-- Pintz with `j = ⌊D⌋`: if `Σ b² ≤ D Σ b` with `D ≥ 1`, then `#{b > 0} ≥ φ(D) Σ b`. -/
theorem pintz_phi {ι : Type*} (S : Finset ι) (b : ι → ℕ) {D : ℝ} (hD : 1 ≤ D)
    (h2 : ∑ i ∈ S, (b i : ℝ) ^ 2 ≤ D * ∑ i ∈ S, (b i : ℝ)) :
    phi D * ∑ i ∈ S, (b i : ℝ) ≤ ((S.filter fun i => 0 < b i).card : ℝ) := by
  set j := ⌊D⌋₊ with hjdef
  have hj : 1 ≤ j := by rw [hjdef]; exact Nat.le_floor (by exact_mod_cast hD)
  have hjpos : (0 : ℝ) < (j : ℝ) * (j + 1) := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    positivity
  have hp := pintz_sum S b j hj
  have hM : 0 ≤ ∑ i ∈ S, (b i : ℝ) := by positivity
  unfold phi
  rw [← hjdef, div_mul_eq_mul_div, div_le_iff₀ hjpos]
  nlinarith

end Romanoff
