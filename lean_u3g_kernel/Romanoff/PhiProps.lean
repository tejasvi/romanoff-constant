import Romanoff.Pintz

/-!
# Properties of `φ` (the piecewise-linear interpolation of `1/D` at the integers)

`φ = max_{j ≥ 1} lin j` on `[1, ∞)`, where `lin j D = (2j + 1 - D)/(j(j+1))` is the secant of `1/x` through `j, j + 1`
(`lin j D - 1/D = -(D - j)(D - j - 1)/(D j (j+1))`).  Hence `φ ≥ 1/D > 0`, `φ` is antitone and its slopes are
`≥ -1/2`: `φ(D) - (D' - D)/2 ≤ φ(D')` for `1 ≤ D ≤ D'`.
-/

namespace Romanoff

/-- The secant of `1/x` through `j` and `j + 1`. -/
noncomputable def lin (j : ℕ) (D : ℝ) : ℝ := (2 * (j : ℝ) + 1 - D) / ((j : ℝ) * (j + 1))

theorem phi_eq_lin (D : ℝ) : phi D = lin ⌊D⌋₊ D := rfl

theorem lin_sub_inv {j : ℕ} (hj : 1 ≤ j) {D : ℝ} (hD : 0 < D) :
    lin j D - 1 / D = -((D - j) * (D - j - 1)) / (D * (j * (j + 1))) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  unfold lin
  field_simp
  ring

theorem lin_le_phi {j : ℕ} (hj : 1 ≤ j) {D : ℝ} (hD : 1 ≤ D) : lin j D ≤ phi D := by
  have hD0 : 0 < D := by linarith
  set J := ⌊D⌋₊ with hJ
  have hJ1 : 1 ≤ J := Nat.le_floor (by exact_mod_cast hD)
  have hJa : (J : ℝ) ≤ D := Nat.floor_le hD0.le
  have hJb : D < J + 1 := Nat.lt_floor_add_one D
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hden1 : 0 < D * ((j : ℝ) * (j + 1)) := by positivity
  have hden2 : 0 < D * ((J : ℝ) * (J + 1)) := by positivity
  -- `φ(D) ≥ 1/D`
  have h1 : 1 / D ≤ phi D := by
    rw [phi_eq_lin, ← hJ]
    have := lin_sub_inv hJ1 hD0
    have hnum : (D - J) * (D - J - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have : 0 ≤ -((D - J) * (D - J - 1)) / (D * (J * (J + 1))) := div_nonneg (by linarith) hden2.le
    linarith
  rcases Nat.lt_trichotomy j J with h | h | h
  · -- `j + 1 ≤ J ≤ D`
    have hjJ : (j : ℝ) + 1 ≤ J := by exact_mod_cast h
    have := lin_sub_inv hj hD0
    have hnum : 0 ≤ (D - j) * (D - j - 1) := mul_nonneg (by linarith) (by linarith)
    have : -((D - j) * (D - j - 1)) / (D * (j * (j + 1))) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hden1.le
    linarith
  · rw [h, phi_eq_lin, ← hJ]
  · -- `D < J + 1 ≤ j`
    have hjJ : (J : ℝ) + 1 ≤ j := by exact_mod_cast h
    have := lin_sub_inv hj hD0
    have hnum : 0 ≤ (D - j) * (D - j - 1) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have : -((D - j) * (D - j - 1)) / (D * (j * (j + 1))) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hden1.le
    linarith

theorem one_div_le_phi {D : ℝ} (hD : 1 ≤ D) : 1 / D ≤ phi D := by
  have hD0 : 0 < D := by linarith
  have hJ1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hD)
  have hJa : ((⌊D⌋₊ : ℕ) : ℝ) ≤ D := Nat.floor_le hD0.le
  have hJb : D < ⌊D⌋₊ + 1 := Nat.lt_floor_add_one D
  have hJ' : (0 : ℝ) < ⌊D⌋₊ := by exact_mod_cast hJ1
  have := lin_sub_inv hJ1 hD0
  have hnum : (D - ⌊D⌋₊) * (D - ⌊D⌋₊ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have : 0 ≤ -((D - ⌊D⌋₊) * (D - ⌊D⌋₊ - 1)) / (D * (⌊D⌋₊ * (⌊D⌋₊ + 1))) := div_nonneg (by linarith) (by positivity)
  rw [phi_eq_lin]; linarith

theorem phi_nonneg {D : ℝ} (hD : 1 ≤ D) : 0 ≤ phi D :=
  le_trans (by have : 0 < D := by linarith
               positivity) (one_div_le_phi hD)

theorem lin_sub {j : ℕ} (hj : 1 ≤ j) (D D' : ℝ) : lin j D' = lin j D - (D' - D) / ((j : ℝ) * (j + 1)) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  unfold lin; field_simp; ring

theorem phi_antitone {D D' : ℝ} (hD : 1 ≤ D) (hDD : D ≤ D') : phi D' ≤ phi D := by
  have hJ1 : 1 ≤ ⌊D'⌋₊ := Nat.le_floor (by exact_mod_cast (le_trans hD hDD))
  have hJ' : (0 : ℝ) < ⌊D'⌋₊ := by exact_mod_cast hJ1
  rw [phi_eq_lin D', lin_sub hJ1 D D']
  have : 0 ≤ (D' - D) / ((⌊D'⌋₊ : ℝ) * (⌊D'⌋₊ + 1)) := div_nonneg (by linarith) (by positivity)
  linarith [lin_le_phi hJ1 hD]

/-- The slopes of `φ` are `≥ -1/2`. -/
theorem phi_slope {D D' : ℝ} (hD : 1 ≤ D) (hDD : D ≤ D') : phi D - (D' - D) / 2 ≤ phi D' := by
  have hJ1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hD)
  have hJ' : (1 : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hJ1
  have h1 := lin_le_phi hJ1 (le_trans hD hDD)
  rw [lin_sub hJ1 D D', ← phi_eq_lin] at h1
  have h2 : (D' - D) / ((⌊D⌋₊ : ℝ) * (⌊D⌋₊ + 1)) ≤ (D' - D) / 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
    nlinarith
  linarith

end Romanoff
