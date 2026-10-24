import Romanoff.M4Spec2

/-!
# M4 layer (E): the three limits of the assembly

`limitFacts : LimitFacts` (statement frozen in `Romanoff.M4Spec2`).  With `L = ⌊log₂ N⌋ → ∞` and `L log 2 ≤ log N`
(`2^L ≤ N`):
* `120/L → 0`;
* `0 ≤ L²/N ≤ (log N)²/(N (log 2)²) → 0`;
* from `R0Bound`, `E(L) ≤ δ L` for all large `L` (`EL_small`), so for `L ≥ 1`
  `(L/120 + 1) E(L)/log² N ≤ (L/120 + 1) δ L/(L log 2)² ≤ δ (1/120 + 1)/(log 2)²`; `E(L) ≥ 0` (`fm_nonneg`).
-/

open Filter Topology

namespace Romanoff

namespace M4E

theorem tendsto_log2 : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
  tendsto_atTop_atTop.mpr fun M => ⟨2 ^ M, fun _ hN => Nat.le_log_of_pow_le (by norm_num) hN⟩

theorem tendsto_log2_real : Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_log2

/-- `L log 2 ≤ log N` for `N ≥ 1`, `L = ⌊log₂ N⌋`. -/
theorem log_ge {N : ℕ} (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rwa [Real.log_pow] at h3

theorem EL_nonneg (l L : ℕ) : 0 ≤ EL l L := Finset.sum_nonneg fun m _ => fm_nonneg m

theorem limit_a : Tendsto (fun N : ℕ => (120 : ℝ) / (Nat.log 2 N : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_log2_real

theorem limit_b : Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) ^ 2 / N) atTop (𝓝 0) := by
  have h0 : Tendsto (fun N : ℕ => Real.log N ^ 2 / N) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, one_mul, add_zero]
  have hg : Tendsto (fun N : ℕ => Real.log N ^ 2 / N / Real.log 2 ^ 2) atTop (𝓝 0) := by
    have := h0.div_const (Real.log 2 ^ 2)
    rwa [zero_div] at this
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ((Nat.log 2 N : ℝ) * Real.log 2) ^ 2 ≤ Real.log N ^ 2 :=
    pow_le_pow_left₀ (by positivity) (log_ge hN) 2
  rw [div_div, div_le_div_iff₀ hN0 (mul_pos hN0 (pow_pos hl2 2))]
  nlinarith [mul_le_mul_of_nonneg_right hsq hN0.le]

theorem limit_c (hR : R0Bound) :
    Tendsto (fun N : ℕ => ((Nat.log 2 N : ℝ) / 120 + 1) * EL ell (Nat.log 2 N) / Real.log N ^ 2) atTop (𝓝 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun N => lt_of_lt_of_le ha ?_, fun ε hε => ?_⟩
  · exact div_nonneg (mul_nonneg (by positivity) (EL_nonneg _ _)) (by positivity)
  · set δ : ℝ := ε * Real.log 2 ^ 2 / (2 * (1 / 120 + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hE := tendsto_log2.eventually (EL_small hR ell δ hδ0)
    filter_upwards [hE, eventually_ge_atTop 2] with N hEN hN
    have hL1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
    have hx1 : (1 : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hL1
    have hlog := log_ge (by omega : 1 ≤ N)
    have hxc0 : 0 < (Nat.log 2 N : ℝ) * Real.log 2 := mul_pos (by linarith) hl2
    have hy : 0 < Real.log N := lt_of_lt_of_le hxc0 hlog
    have k1 : ((Nat.log 2 N : ℝ) / 120 + 1) * EL ell (Nat.log 2 N) ≤
        ((Nat.log 2 N : ℝ) / 120 + 1) * (δ * Nat.log 2 N) :=
      mul_le_mul_of_nonneg_left hEN (by positivity)
    have k2 : ε / 2 * ((Nat.log 2 N : ℝ) * Real.log 2) ^ 2 - ((Nat.log 2 N : ℝ) / 120 + 1) * (δ * Nat.log 2 N) =
        ε * Real.log 2 ^ 2 * (Nat.log 2 N : ℝ) * ((Nat.log 2 N : ℝ) - 1) * (60 / 121) := by
      rw [hδ]
      ring
    have k3 : 0 ≤ ε * Real.log 2 ^ 2 * (Nat.log 2 N : ℝ) * ((Nat.log 2 N : ℝ) - 1) * (60 / 121) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hε.le (sq_nonneg _)) (by linarith)) (by linarith))
        (by norm_num)
    have k4 : ((Nat.log 2 N : ℝ) * Real.log 2) ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ hxc0.le hlog 2
    rw [div_lt_iff₀ (pow_pos hy 2)]
    nlinarith [k1, k2, k3, mul_le_mul_of_nonneg_left k4 hε.le, mul_pos hε (pow_pos hy 2)]

end M4E

open M4E in
theorem limitFacts : LimitFacts := And.intro limit_a (And.intro limit_b limit_c)

end Romanoff
