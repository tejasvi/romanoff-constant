import Romanoff.E.Final
import Romanoff.E.M4B
import Romanoff.E.M4C
import Romanoff.E.M4E
import Romanoff.E.Tables

/-!
# U3e: the reduction from `TBoundA` to the evaluator at period 3960 (no computation)

`liminf_ge_of_TBoundA`: from `TBoundA tab R0t` and a lower bound `claim` for
`lagBound (parOf (teffA tab α) 8 0) (orbits 3960 ellPrimes)` at every rational `α ≥ 0` with
`Σ_{g ∈ divE} α_g ≤ R0t + δ` (`δ > 0`), `claim ≤ liminf dens`.  As in Romanoff/U3/Reduce.lean: the real `α` of `TBoundA`
is rounded up to rationals within `δ / 48` per divisor, the table `teffA tab α'` has `TBound` (period 3960), and the
period-3960 copy of `lagR_le_liminf` applies.
-/

open Filter Topology R45 R45.PE R45.D45 R45.U3E

namespace Romanoff.E

/-- `tailA α c` as a real sum over the divisors of 3960 that divide `c`. -/
theorem tailA_cast (α : ℕ → ℚ) (c : ℕ) :
    ((tailA α c : ℚ) : ℝ) = ∑ g ∈ (Nat.divisors 3960).filter (· ∣ c), (g : ℝ) * (α g : ℝ) := by
  rw [tailA_eq, Rat.cast_list_sum, List.map_map, Finset.sum_filter, divisors3960_eq',
    List.sum_toFinset _ divE_nodup]
  apply congrArg
  apply List.map_congr_left
  intro g _
  have hmod : c % g = 0 ↔ g ∣ c := (Nat.dvd_iff_mod_eq_zero).symm
  simp only [Function.comp_apply]
  by_cases h : g ∣ c
  · rw [if_pos (hmod.mpr h), if_pos h]; push_cast; ring
  · rw [if_neg (fun h' => h (hmod.mp h')), if_neg h]; simp

theorem divE_length : R45.M3E.divE.length = 48 := by decide

theorem liminf_ge_of_TBoundA {tab : List ℚ} {R0t δ claim : ℚ} (hT : TBoundA tab R0t) (hδ : 0 < δ)
    (hval : ∀ α : ℕ → ℚ, (∀ g, 0 ≤ α g) → (R45.M3E.divE.map α).sum ≤ R0t + δ →
      claim ≤ lagBound (parOf (teffA tab α) 8 0) (orbits 3960 ellPrimes))
    (hESP : ESP28 ell) (hPNT : PNTAP ell) (hR0 : R0Bound) : (claim : ℝ) ≤ liminf dens atTop := by
  obtain ⟨_, αR, hα0, hαs, hbound⟩ := hT
  have hδ' : (0 : ℝ) < (δ : ℝ) / 48 := by
    have : (0 : ℝ) < δ := by exact_mod_cast hδ
    positivity
  have hq : ∀ g, ∃ q : ℚ, αR g < q ∧ (q : ℝ) < αR g + (δ : ℝ) / 48 := fun g =>
    exists_rat_btwn (by linarith)
  choose α' hα'1 hα'2 using hq
  have hα'0 : ∀ g, 0 ≤ α' g := fun g => by
    have : (0 : ℝ) ≤ (α' g : ℝ) := ((hα0 g).trans (hα'1 g).le)
    exact_mod_cast this
  have hsum : (R45.M3E.divE.map α').sum ≤ R0t + δ := by
    have h1 : (((R45.M3E.divE.map α').sum : ℚ) : ℝ) = ∑ g ∈ Nat.divisors 3960, (α' g : ℝ) := by
      rw [Rat.cast_list_sum, List.map_map, divisors3960_eq', List.sum_toFinset _ divE_nodup]
      rfl
    have h2 : ∑ g ∈ Nat.divisors 3960, (α' g : ℝ) ≤ ∑ g ∈ Nat.divisors 3960, (αR g + (δ : ℝ) / 48) :=
      Finset.sum_le_sum fun g _ => (hα'2 g).le
    have h3 : ∑ g ∈ Nat.divisors 3960, (αR g + (δ : ℝ) / 48) = ∑ g ∈ Nat.divisors 3960, αR g + δ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, divisors3960_eq', List.card_toFinset,
        List.dedup_eq_self.mpr divE_nodup, divE_length]
      simp
      ring
    have : (((R45.M3E.divE.map α').sum : ℚ) : ℝ) ≤ ((R0t + δ : ℚ) : ℝ) := by
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
  have h := lagR_le_liminf xuESP sumXUJT orbSumLink ncQLink lagBoundSplit dataFacts limitFacts hTB 8 0 (by norm_num)
    hESP hPNT hR0 (Or.inl rfl)
  have h2 : (claim : ℝ) ≤ lagR (teffA tab α') 8 0 := by
    unfold lagR; exact_mod_cast hval α' hα'0 hsum
  exact h2.trans h

end Romanoff.E
