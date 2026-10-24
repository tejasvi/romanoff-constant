import Romanoff.LagSound
import Romanoff.PhiProps

/-!
# The Lagrangian bound at one `N`, with perturbed caps

If the true normalized pair masses satisfy `Ỹ_k ≤ λ Ymax_k + ν` (caps inflated by the `ε`'s and `o(1)`'s of the inputs)
and `(1/l) Σ_k Ỹ_k ≤ B`, clip `Y'_k = min(Ỹ_k, Ymax_k) ∈ [0, Ymax_k]`.  The slope bound of `φ` gives
`s φ(1 + Ỹ/s) ≥ s φ(1 + Y'/s) - ((λ-1) Ymax + ν)/2`, and weak duality (`minQ_le`) for `Y'` gives
`Σ_k (norm/l) s_k φ(1 + Ỹ_k/s_k) ≥ Σ_k minQ_k - μ B - (norm/l) Σ_k ((λ-1) Ymax_k + ν)/2`.
-/

open Finset R45

namespace Romanoff

theorem lagrangian_perturbed {ι : Type*} (K : Finset ι) (P : Par) (s : ι → ℕ) (Yt : ι → ℝ) (ymax : ι → ℚ)
    (lam ν B : ℝ) (hlam : 1 ≤ lam) (hν : 0 ≤ ν) (hs : ∀ k ∈ K, 0 < s k) (hY0 : ∀ k ∈ K, 0 ≤ Yt k) (hym : ∀ k ∈ K, 0 ≤ ymax k)
    (hmu : 0 ≤ (P.mu : ℝ)) (hnorm : 0 ≤ (P.norm : ℝ)) (hell : 0 < (P.ell : ℝ))
    (hcap : ∀ k ∈ K, Yt k ≤ lam * ymax k + ν) (hbud : (1 / (P.ell : ℝ)) * ∑ k ∈ K, Yt k ≤ B) :
    ∑ k ∈ K, ((minQ P (s k) (ymax k) : ℚ) : ℝ) - P.mu * B -
        (P.norm : ℝ) / P.ell * ∑ k ∈ K, ((lam - 1) * ymax k + ν) / 2 ≤
      ∑ k ∈ K, (P.norm : ℝ) / P.ell * (s k) * phi (1 + Yt k / s k) := by
  -- clipped masses
  set Yc : ι → ℝ := fun k => min (Yt k) (ymax k) with hYc
  have hper : ∀ k ∈ K, ((minQ P (s k) (ymax k) : ℚ) : ℝ) - (1 / (P.ell : ℝ)) * P.mu * Yc k -
      (P.norm : ℝ) / P.ell * (((lam - 1) * ymax k + ν) / 2) ≤
      (P.norm : ℝ) / P.ell * (s k) * phi (1 + Yt k / s k) := by
    intro k hk
    have hsk : (0 : ℝ) < s k := by exact_mod_cast hs k hk
    have hymk : (0 : ℝ) ≤ ymax k := by exact_mod_cast hym k hk
    have hYc0 : 0 ≤ Yc k := le_min (hY0 k hk) hymk
    have hYc1 : Yc k ≤ ymax k := min_le_right _ _
    have hYcY : Yc k ≤ Yt k := min_le_left _ _
    -- weak duality at the clipped point
    have h1 := minQ_le P (s k) (hs k hk) (ymax k) (hym k hk) (Yc k) hYc0 hYc1
    unfold gR at h1
    -- the clipping loss
    have hdiff : Yt k - Yc k ≤ (lam - 1) * ymax k + ν := by
      rcases le_total (Yt k) (ymax k) with h | h
      · have : Yc k = Yt k := min_eq_left h
        rw [this, sub_self]
        have := mul_nonneg (sub_nonneg.mpr hlam) hymk
        linarith
      · have : Yc k = ymax k := min_eq_right h
        rw [this]
        have := hcap k hk
        linarith
    have hslope := phi_slope (D := 1 + Yc k / s k) (D' := 1 + Yt k / s k)
      (by have := div_nonneg hYc0 hsk.le; linarith)
      (by have := div_le_div_of_nonneg_right hYcY hsk.le; linarith)
    have hloss : (s k : ℝ) * phi (1 + Yc k / s k) - ((lam - 1) * ymax k + ν) / 2 ≤
        (s k : ℝ) * phi (1 + Yt k / s k) := by
      have e : (s k : ℝ) * ((1 + Yt k / s k - (1 + Yc k / s k)) / 2) = (Yt k - Yc k) / 2 := by
        field_simp; ring
      have := mul_le_mul_of_nonneg_left hslope hsk.le
      rw [mul_sub, e] at this
      linarith
    have hc : 0 ≤ (P.norm : ℝ) / P.ell := div_nonneg hnorm hell.le
    have := mul_le_mul_of_nonneg_left hloss hc
    have e2 : (P.norm : ℝ) * (1 / (P.ell : ℝ)) * (s k) * phi (1 + Yc k / s k) =
        (P.norm : ℝ) / P.ell * ((s k : ℝ) * phi (1 + Yc k / s k)) := by ring
    nlinarith
  have hsum := sum_le_sum hper
  rw [sum_sub_distrib, sum_sub_distrib] at hsum
  have e3 : ∑ k ∈ K, (P.norm : ℝ) / P.ell * (((lam - 1) * ymax k + ν) / 2) =
      (P.norm : ℝ) / P.ell * ∑ k ∈ K, ((lam - 1) * ymax k + ν) / 2 := (mul_sum _ _ _).symm
  rw [e3] at hsum
  -- the budget: `(1/l) Σ Y'_k ≤ (1/l) Σ Ỹ_k ≤ B`
  have hb : ∑ k ∈ K, (1 / (P.ell : ℝ)) * P.mu * Yc k ≤ P.mu * B := by
    have e : ∑ k ∈ K, (1 / (P.ell : ℝ)) * P.mu * Yc k = P.mu * ((1 / (P.ell : ℝ)) * ∑ k ∈ K, Yc k) := by
      rw [mul_sum, mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hmu
    refine le_trans ?_ hbud
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => min_le_left _ _) (by positivity)
  linarith

end Romanoff
