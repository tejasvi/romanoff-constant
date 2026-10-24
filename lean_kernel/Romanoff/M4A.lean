import Romanoff.M4Spec

/-!
# (A) The singular series per class: `WUBound`

Group the pairs `(a₁, a₂)` by their residues `(r₁, r₂) ∈ U_k²` mod 120, bound each group by `sing_series_pair` with the
`TBound` table, and collect the residue pairs by their difference (`sum_pairs_eq_sum_nC`).
-/

open Finset

namespace Romanoff

/-- Regrouping a pair sum with both residues in `U` by the residues. -/
theorem regroup (S U : Finset ℕ) (m : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ a1 ∈ S, ∑ a2 ∈ S.erase a1, (if a1 % m ∈ U ∧ a2 % m ∈ U then f a1 a2 else 0) =
      ∑ r1 ∈ U, ∑ r2 ∈ U, ∑ a1 ∈ S.filter (· % m = r1), ∑ a2 ∈ (S.erase a1).filter (· % m = r2), f a1 a2 := by
  have h1 : ∀ a1 a2, (if a1 % m ∈ U ∧ a2 % m ∈ U then f a1 a2 else 0) =
      ∑ r1 ∈ U, ∑ r2 ∈ U, if a1 % m = r1 ∧ a2 % m = r2 then f a1 a2 else 0 := by
    intro a1 a2
    have e : ∀ r1, ∑ r2 ∈ U, (if a1 % m = r1 ∧ a2 % m = r2 then f a1 a2 else 0) =
        if a1 % m = r1 then (if a2 % m ∈ U then f a1 a2 else 0) else 0 := by
      intro r1
      by_cases h : a1 % m = r1
      · simp only [h, true_and, ite_true, sum_ite_eq]
      · simp only [h, false_and, ite_false, sum_const_zero]
    rw [sum_congr rfl fun r1 _ => e r1, sum_ite_eq]
    by_cases ha : a1 % m ∈ U <;> by_cases hb : a2 % m ∈ U <;> simp [ha, hb]
  simp only [h1]
  rw [sum_congr rfl fun a1 _ => sum_comm, sum_comm]
  refine sum_congr rfl fun r1 _ => ?_
  rw [sum_congr rfl fun a1 _ => sum_comm, sum_comm]
  refine sum_congr rfl fun r2 _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun a1 _ => ?_
  rw [sum_filter]
  split_ifs with h
  · exact sum_congr rfl fun a2 _ => by simp [h]
  · exact sum_eq_zero fun a2 _ => by simp [h]

theorem wuBound : WUBound := by
  intro teff hT L k
  set U := Uset 120 ellPrimes k with hUdef
  have hU : ∀ r ∈ U, r < 120 := fun r hr => mem_range.mp (mem_filter.mp hr).1
  unfold WU
  rw [regroup (Icc 1 L) U 120 (fun a1 a2 => singP ellPrimes (hsh a1 a2))]
  set A := ((L : ℝ) / 120 + 1) * ((L : ℝ) / 120) with hA
  set B := ((L : ℝ) / 120 + 1) * EL ell L with hB
  have hpair : ∀ r1 ∈ U, ∀ r2 ∈ U,
      ∑ a1 ∈ (Icc 1 L).filter (· % 120 = r1), ∑ a2 ∈ ((Icc 1 L).erase a1).filter (· % 120 = r2),
        singP ellPrimes (hsh a1 a2) ≤ A * ((teff.getD ((r2 + 120 - r1) % 120) 0 : ℚ) : ℝ) + B := by
    intro r1 hr1 r2 _
    exact sing_series_pair distinctPrimes_ell (hU r1 hr1) _
      (fun S hS => hT.2 _ (Nat.mod_lt _ (by norm_num)) S hS)
  refine (sum_le_sum fun r1 hr1 => sum_le_sum fun r2 hr2 => hpair r1 hr1 r2 hr2).trans (le_of_eq ?_)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  rw [sum_pairs_eq_sum_nC (by norm_num : 0 < 120) ellPrimes k (fun c => ((teff.getD c 0 : ℚ) : ℝ))]
  unfold TK
  ring

end Romanoff
