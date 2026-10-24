import Mathlib

/-!
# `0.693147180559945309 < log 2 < 0.693147180559945310`

From `log(1 - x) = -Σ_{i ≥ 1} x^i / i` at `x = 1/2` with 64 terms (remainder `≤ 2^-64 < 5.5·10^-20`).
-/

namespace Romanoff

open Finset

/-- The partial sum `Σ_{i < 64} (1/2)^(i+1)/(i+1)` as an exact rational. -/
def log2Partial : ℚ := ∑ i ∈ range 64, (1 / 2 : ℚ) ^ (i + 1) / (i + 1)

theorem log2Partial_bounds :
    (693147180559945309 : ℚ) / 10 ^ 18 + 1 / 2 ^ 64 < log2Partial ∧
      log2Partial + 1 / 2 ^ 64 < (693147180559945310 : ℚ) / 10 ^ 18 := by
  unfold log2Partial
  constructor <;> norm_num [Finset.sum_range_succ]

theorem log_two_bounds :
    (693147180559945309 / 10 ^ 18 : ℝ) < Real.log 2 ∧ Real.log 2 < 693147180559945310 / 10 ^ 18 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num) 64
  have hlog : Real.log (1 - 1 / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  have hS : (∑ i ∈ range 64, (1 / 2 : ℝ) ^ (i + 1) / (i + 1)) = ((log2Partial : ℚ) : ℝ) := by
    unfold log2Partial; push_cast; rfl
  rw [hS] at h
  have hr : (1 / 2 : ℝ) ^ (64 + 1) / (1 - 1 / 2) = ((1 / 2 ^ 64 : ℚ) : ℝ) := by norm_num
  rw [hr] at h
  obtain ⟨b1, b2⟩ := log2Partial_bounds
  have b1' : ((693147180559945309 / 10 ^ 18 + 1 / 2 ^ 64 : ℚ) : ℝ) < ((log2Partial : ℚ) : ℝ) := by exact_mod_cast b1
  have b2' : ((log2Partial + 1 / 2 ^ 64 : ℚ) : ℝ) < ((693147180559945310 / 10 ^ 18 : ℚ) : ℝ) := by exact_mod_cast b2
  push_cast at b1' b2'
  have := abs_le.mp h
  constructor <;> linarith [this.1, this.2]

end Romanoff
