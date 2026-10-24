import Romanoff.G.Reduce

/-!
# U3g/V4g: the reduction from `TBoundA` to the evaluator with a uniform budget multiplier `μ ≥ 0`

`liminf_ge_of_TBoundA_mu`: as `liminf_ge_of_TBoundA` (Romanoff/G/Reduce.lean), for the parameters `(C1, μ)` with `μ ≥ 0`
and `μ = 0 ∨ (JTProp2 ∧ C1 = C1R)` (the conditional case uses (I2) through `lagR_le_liminf`).
-/

open Filter Topology R45 R45.PG R45.D45 R45.U3G

namespace Romanoff.G

theorem liminf_ge_of_TBoundA_mu {tab : List ℚ} {R0t δ claim c1 mu : ℚ} (hT : TBoundA tab R0t) (hδ : 0 < δ)
    (hmu : (0 : ℝ) ≤ mu)
    (hval : ∀ α : ℕ → ℚ, (∀ g, 0 ≤ α g) → (R45.M3G.divG.map α).sum ≤ R0t + δ →
      claim ≤ lagBound (parOf (teffA tab α) c1 mu) (orbits 27720 ellPrimes))
    (hESP : ESP28 ell) (hPNT : PNTAP ell) (hR0 : R0Bound) (hJT : mu = 0 ∨ (JTProp2 ∧ (c1 : ℝ) = C1R)) :
    (claim : ℝ) ≤ liminf dens atTop := by
  obtain ⟨_, αR, hα0, hαs, hbound⟩ := hT
  have hδ' : (0 : ℝ) < (δ : ℝ) / 96 := by
    have : (0 : ℝ) < δ := by exact_mod_cast hδ
    positivity
  have hq : ∀ g, ∃ q : ℚ, αR g < q ∧ (q : ℝ) < αR g + (δ : ℝ) / 96 := fun g =>
    exists_rat_btwn (by linarith)
  choose α' hα'1 hα'2 using hq
  have hα'0 : ∀ g, 0 ≤ α' g := fun g => by
    have : (0 : ℝ) ≤ (α' g : ℝ) := ((hα0 g).trans (hα'1 g).le)
    exact_mod_cast this
  have hsum : (R45.M3G.divG.map α').sum ≤ R0t + δ := by
    have h1 : (((R45.M3G.divG.map α').sum : ℚ) : ℝ) = ∑ g ∈ Nat.divisors 27720, (α' g : ℝ) := by
      rw [Rat.cast_list_sum, List.map_map, divisors27720_eq', List.sum_toFinset _ divG_nodup]
      rfl
    have h2 : ∑ g ∈ Nat.divisors 27720, (α' g : ℝ) ≤ ∑ g ∈ Nat.divisors 27720, (αR g + (δ : ℝ) / 96) :=
      Finset.sum_le_sum fun g _ => (hα'2 g).le
    have h3 : ∑ g ∈ Nat.divisors 27720, (αR g + (δ : ℝ) / 96) = ∑ g ∈ Nat.divisors 27720, αR g + δ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, divisors27720_eq', List.card_toFinset,
        List.dedup_eq_self.mpr divG_nodup, divG_length]
      simp
      ring
    have : (((R45.M3G.divG.map α').sum : ℚ) : ℝ) ≤ ((R0t + δ : ℚ) : ℝ) := by
      rw [h1]; push_cast; linarith
    exact_mod_cast this
  have hTB : TBound (teffA tab α') := by
    refine ⟨teffA_length tab α', fun c hc S hS => ?_⟩
    rw [teffA_getD tab α' hc]
    push_cast
    rw [tailA_cast]
    refine (hbound c hc S hS).trans ?_
    refine add_le_add (le_refl _) ?_
    apply Finset.sum_le_sum
    intro g _
    exact mul_le_mul_of_nonneg_left (hα'1 g).le (Nat.cast_nonneg _)
  have h := lagR_le_liminf xuESP sumXUJT orbSumLink ncQLink lagBoundSplit dataFacts limitFacts hTB c1 mu hmu
    hESP hPNT hR0 hJT
  have h2 : (claim : ℝ) ≤ lagR (teffA tab α') c1 mu := by
    unfold lagR; exact_mod_cast hval α' hα'0 hsum
  exact h2.trans h

end Romanoff.G
