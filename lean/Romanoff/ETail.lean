import Romanoff.SingSeries

/-!
# `E(L) = o(L)` from the bounded partial sums of `R₀` alone

With `a(m) = f(m)/ord_m(2)` on odd squarefree `m` (`0` elsewhere), `R0Bound` bounds every partial sum, so `a` is summable
and its tails `Σ_{k} a(k + K)` tend to `0`.  Splitting `E(L) = Σ_{ord_m(2) ≤ L} f(m)` at a fixed `K`:
`E(L) ≤ Σ_{m < K} f(m) + L Σ_{m ≥ K} a(m)`, since `f(m) ≤ L f(m)/ord_m(2)` when `ord_m(2) ≤ L`.  No Mertens-type input.
-/

open Finset Filter Topology

namespace Romanoff

/-- The terms of `R₀`. -/
noncomputable def r0term (m : ℕ) : ℝ := if Odd m ∧ Squarefree m then fm m / (ordm m : ℝ) else 0

theorem r0term_nonneg (m : ℕ) : 0 ≤ r0term m := by
  unfold r0term; split_ifs
  · exact div_nonneg (fm_nonneg m) (Nat.cast_nonneg _)
  · exact le_refl 0

theorem r0term_summable (hR : R0Bound) : Summable r0term := by
  refine summable_of_sum_range_le r0term_nonneg (c := 193656 / 100000) fun n => ?_
  have := hR ((range n).filter fun m => Odd m ∧ Squarefree m) fun m hm => (mem_filter.mp hm).2
  unfold r0term
  rw [← sum_filter]
  exact this

theorem EL_small (hR : R0Bound) (l : ℕ) : ∀ δ > (0 : ℝ), ∀ᶠ L : ℕ in atTop, EL l L ≤ δ * L := by
  intro δ hδ
  have hsum := r0term_summable hR
  -- a tail below `δ/2`
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_sum_nat_add r0term)).2 (δ / 2) (by positivity))
  have hK' := hK K le_rfl
  set C : ℝ := ∑ m ∈ range K, fm m with hC
  have hC0 : 0 ≤ C := sum_nonneg fun m _ => fm_nonneg m
  refine eventually_atTop.mpr ⟨⌈2 * C / δ⌉₊ + 1, fun L hL => ?_⟩
  have hL1 : (2 * C / δ) ≤ L := by
    have := Nat.le_ceil (2 * C / δ)
    have : (⌈2 * C / δ⌉₊ : ℝ) + 1 ≤ L := by exact_mod_cast hL
    linarith
  have hCL : C ≤ δ / 2 * L := by
    rw [div_le_iff₀ hδ] at hL1; linarith
  unfold EL
  set S := (SL l L).filter (fun m => ordm m ≤ L) with hS
  rw [← sum_filter_add_sum_filter_not S (fun m => m < K)]
  -- small moduli: a fixed finite sum
  have h1 : ∑ m ∈ S.filter (fun m => m < K), fm m ≤ C := by
    refine sum_le_sum_of_subset_of_nonneg (fun m hm => mem_range.mpr (mem_filter.mp hm).2) fun m _ _ => fm_nonneg m
  -- large moduli: `f(m) ≤ L a(m)` and the tail
  have h2 : ∑ m ∈ S.filter (fun m => ¬ m < K), fm m ≤ L * ∑' k, r0term (k + K) := by
    have e1 : ∀ m ∈ S.filter (fun m => ¬ m < K), fm m ≤ L * r0term m := by
      intro m hm
      obtain ⟨hmS, _⟩ := mem_filter.mp hm
      obtain ⟨hmSL, hoL⟩ := mem_filter.mp hmS
      have hodd : Odd m := (mem_filter.mp hmSL).2.1
      have hsq : Squarefree m := (mem_filter.mp hmSL).2.2.1
      have ho : (0 : ℝ) < ordm m := by exact_mod_cast ordm_pos hodd
      have hoL' : (ordm m : ℝ) ≤ L := by exact_mod_cast hoL
      unfold r0term
      rw [ite_eq_left ⟨hodd, hsq⟩]
      calc fm m = fm m / ordm m * ordm m := by field_simp
        _ ≤ fm m / ordm m * L := mul_le_mul_of_nonneg_left hoL' (div_nonneg (fm_nonneg m) ho.le)
        _ = L * (fm m / ordm m) := by ring
    refine (sum_le_sum e1).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L)
    have e2 : ∑ m ∈ S.filter (fun m => ¬ m < K), r0term m =
        ∑ k ∈ (S.filter (fun m => ¬ m < K)).image (· - K), r0term (k + K) := by
      rw [sum_image fun x hx y hy hxy => by
        have := (mem_filter.mp hx).2; have := (mem_filter.mp hy).2; omega]
      exact sum_congr rfl fun m hm => by rw [Nat.sub_add_cancel (by have := (mem_filter.mp hm).2; omega)]
    rw [e2]
    exact Summable.sum_le_tsum _ (fun k _ => r0term_nonneg _) ((summable_nat_add_iff K).mpr hsum)
  have h3 : (L : ℝ) * ∑' k, r0term (k + K) ≤ L * (δ / 2) :=
    mul_le_mul_of_nonneg_left hK'.le (Nat.cast_nonneg L)
  linarith

end Romanoff
