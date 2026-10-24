import Romanoff.OrbSound
import K45.Defs

/-!
# A fast `nShift`: the cyclic autocorrelation of the bits from one product

`spread per u = Σ_{e < per, u_e} 256^e`, `rspread per u = Σ_{e < per, u_e} 256^(per-1-e)`.  The base-256 digit `t` of
`spread · rspread` counts the pairs `(e, e')` of set bits with `e + (per - 1 - e') = t` (at most `per ≤ 255` of them, so
there are no carries), and `n(c) = #{e : u_e, u_{(e+c) mod per}}` is the sum of the digits `per - 1 - c` and
`2 per - 1 - c`.
-/

namespace K45

open R45 Romanoff Finset

theorem foldl_add_ite (P : ℕ → Bool) (g : ℕ → ℕ) :
    ∀ n a, (List.range n).foldl (fun acc e => if P e then acc + g e else acc) a =
      a + ∑ e ∈ range n, if P e then g e else 0
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_add_ite P g n a,
      Finset.sum_range_succ]
    split_ifs <;> omega

theorem dig_eq (p j : ℕ) : dig p j = p / 256 ^ j % 256 := by
  unfold dig
  rw [Nat.shiftRight_eq_div_pow, show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  norm_num

/-- A sum of digits below `b`. -/
theorem sum_digits_lt (b : ℕ) (a : ℕ → ℕ) (ha : ∀ t, a t < b) :
    ∀ K, ∑ t ∈ range K, a t * b ^ t < b ^ K
  | 0 => by simp
  | K + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := sum_digits_lt b a ha K
    have h2 : a K * b ^ K ≤ (b - 1) * b ^ K := Nat.mul_le_mul_right _ (by have := ha K; omega)
    have hb : 1 ≤ b := by have := ha 0; omega
    calc ∑ t ∈ range K, a t * b ^ t + a K * b ^ K < b ^ K + (b - 1) * b ^ K := by omega
      _ = b ^ K * b := by
        rw [Nat.sub_mul, one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left _ (by omega))]
        ring

theorem digit_of_sum (b : ℕ) (a : ℕ → ℕ) (ha : ∀ t, a t < b) :
    ∀ K j, (∑ t ∈ range K, a t * b ^ t) / b ^ j % b = if j < K then a j else 0
  | 0, j => by simp
  | K + 1, j => by
    have hb : 0 < b := by have := ha 0; omega
    have hS := sum_digits_lt b a ha K
    rw [Finset.sum_range_succ]
    rcases lt_trichotomy j K with h | h | h
    · -- `j < K`: the new top term is a multiple of `b^(j+1)`
      have e : a K * b ^ K = (a K * b ^ (K - j - 1) * b) * b ^ j := by
        have hp : b ^ K = b ^ (K - j - 1) * b * b ^ j := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        rw [hp]
        ring
      rw [e, Nat.add_mul_div_right _ _ (pow_pos hb j), Nat.add_mul_mod_self_right, digit_of_sum b a ha K j,
        ite_eq_left h, ite_eq_left (show j < K + 1 by omega)]
    · subst h
      rw [Nat.add_mul_div_right _ _ (pow_pos hb j), Nat.div_eq_of_lt hS, zero_add, Nat.mod_eq_of_lt (ha j),
        ite_eq_left (show j < j + 1 by omega)]
    · have hlt : ∑ t ∈ range K, a t * b ^ t + a K * b ^ K < b ^ j := by
        have := sum_digits_lt b a ha (K + 1)
        rw [Finset.sum_range_succ] at this
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right hb h)
      rw [Nat.div_eq_of_lt hlt, Nat.zero_mod, ite_eq_right (show ¬ j < K + 1 by omega)]

/-- The pairs of set bits `(e, e')` with exponent `e + (per - 1 - e') = t`. -/
def pairsAt (per u t : ℕ) : Finset (ℕ × ℕ) :=
  (range per ×ˢ range per).filter fun ee => u.testBit ee.1 ∧ u.testBit ee.2 ∧ ee.1 + (per - 1 - ee.2) = t

theorem pairsAt_card_le (per u t : ℕ) : (pairsAt per u t).card ≤ per := by
  calc (pairsAt per u t).card ≤ (range per).card := by
        refine card_le_card_of_injOn Prod.fst (fun ee he => (mem_product.mp (mem_filter.mp he).1).1) ?_
        intro x hx y hy hxy
        have hx' := mem_filter.mp hx
        have hy' := mem_filter.mp hy
        have hx2 := mem_range.mp (mem_product.mp hx'.1).2
        have hy2 := mem_range.mp (mem_product.mp hy'.1).2
        have : x.2 = y.2 := by
          have h1 := hx'.2.2.2
          have h2 := hy'.2.2.2
          rw [hxy] at h1
          omega
        exact Prod.ext hxy this
    _ = per := card_range per

theorem spread_mul (per u : ℕ) :
    spread per u * rspread per u = ∑ t ∈ range (2 * per - 1), (pairsAt per u t).card * 256 ^ t := by
  unfold spread rspread
  rw [foldl_add_ite _ _ per 0, foldl_add_ite _ _ per 0, zero_add, zero_add, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (s := range per ×ˢ range per) (t := range (2 * per - 1))
    (g := fun ee => ee.1 + (per - 1 - ee.2))]
  · refine sum_congr rfl fun t _ => ?_
    have hf : ∀ ee ∈ (range per ×ˢ range per).filter (fun ee => ee.1 + (per - 1 - ee.2) = t),
        ((if u.testBit ee.1 then 256 ^ ee.1 else 0) * (if u.testBit ee.2 then 256 ^ (per - 1 - ee.2) else 0)) =
          if u.testBit ee.1 ∧ u.testBit ee.2 then 256 ^ t else 0 := by
      intro ee hee
      have ht := (mem_filter.mp hee).2
      by_cases h1 : u.testBit ee.1 <;> by_cases h2 : u.testBit ee.2 <;> simp [h1, h2, ← pow_add, ht]
    rw [sum_congr rfl hf, Finset.sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, filter_filter]
    congr 1
    unfold pairsAt
    congr 1
    exact Finset.filter_congr fun ee _ => by tauto
  · intro ee he
    have h1 := mem_range.mp (mem_product.mp he).1
    have h2 := mem_range.mp (mem_product.mp he).2
    exact mem_range.mpr (by omega)

theorem dig_spread_mul {per : ℕ} (hper : per ≤ 255) (u j : ℕ) :
    dig (spread per u * rspread per u) j = if j < 2 * per - 1 then (pairsAt per u j).card else 0 := by
  rw [dig_eq, spread_mul]
  exact digit_of_sum 256 (fun t => (pairsAt per u t).card) (fun t => by have := pairsAt_card_le per u t; omega) _ j

/-- The count of `nShift` as the two digits. -/
theorem count_eq_pairs {per : ℕ} (u c : ℕ) (hc : c < per) :
    ((range per).filter fun e => u.testBit e && u.testBit ((e + c) % per)).card =
      (pairsAt per u (per - 1 - c)).card + (pairsAt per u (2 * per - 1 - c)).card := by
  have hdisj : Disjoint (pairsAt per u (per - 1 - c)) (pairsAt per u (2 * per - 1 - c)) := by
    rw [Finset.disjoint_left]
    intro ee h1 h2
    have := (mem_filter.mp h1).2.2.2
    have := (mem_filter.mp h2).2.2.2
    omega
  rw [← card_union_of_disjoint hdisj]
  apply card_nbij (fun e => (e, (e + c) % per))
  · intro e he
    have he' := mem_filter.mp he
    have hel := mem_range.mp he'.1
    have hb := he'.2
    simp only [Bool.and_eq_true] at hb
    show (e, (e + c) % per) ∈ pairsAt per u (per - 1 - c) ∪ pairsAt per u (2 * per - 1 - c)
    rw [mem_union]
    by_cases hlt : e + c < per
    · left
      rw [Nat.mod_eq_of_lt hlt] at hb ⊢
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hel, mem_range.mpr hlt⟩, hb.1, hb.2, by omega⟩
    · right
      have e2 : (e + c) % per = e + c - per := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e2] at hb ⊢
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hel, mem_range.mpr (by omega)⟩, hb.1, hb.2, by omega⟩
  · intro x _ y _ h
    exact (Prod.mk.inj h).1
  · intro ee hee
    rw [coe_union, Set.mem_union] at hee
    rcases hee with h | h <;>
    · have h' := mem_filter.mp (mem_coe.mp h)
      have h1 := mem_range.mp (mem_product.mp h'.1).1
      have h2 := mem_range.mp (mem_product.mp h'.1).2
      refine ⟨ee.1, ?_, ?_⟩
      · refine mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr h1, ?_⟩)
        have hm : (ee.1 + c) % per = ee.2 := by
          by_cases hlt : ee.1 + c < per
          · rw [Nat.mod_eq_of_lt hlt]; have := h'.2.2.2; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; have := h'.2.2.2; omega
        rw [hm]
        simp [h'.2.1, h'.2.2.1]
      · have hm : (ee.1 + c) % per = ee.2 := by
          by_cases hlt : ee.1 + c < per
          · rw [Nat.mod_eq_of_lt hlt]; have := h'.2.2.2; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; have := h'.2.2.2; omega
        show (ee.1, (ee.1 + c) % per) = ee
        rw [hm]

theorem nFast_eq {per : ℕ} (hper : per ≤ 255) (u : ℕ) : nFast per u = nShift per u := by
  apply List.ext_getElem
  · simp [nFast, nFromProd, nShift_length]
  · intro c h1 h2
    have hc : c < per := by simpa [nFast, nFromProd] using h1
    have e := nShift_getD per u c hc
    rw [List.getD_eq_getElem _ _ h2] at e
    rw [e, count_eq_pairs u c hc]
    simp only [nFast, nFromProd, List.getElem_map, List.getElem_range]
    rw [dig_spread_mul hper, dig_spread_mul hper, ite_eq_left (show per - 1 - c < 2 * per - 1 by omega)]
    by_cases h0 : c = 0
    · subst h0
      rw [ite_eq_right (show ¬ (2 * per - 1 - 0 < 2 * per - 1) by omega)]
      have : pairsAt per u (2 * per - 1 - 0) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ee hee
        have h' := mem_filter.mp hee
        have := mem_range.mp (mem_product.mp h'.1).1
        have := mem_range.mp (mem_product.mp h'.1).2
        have := h'.2.2.2
        omega
      rw [this, card_empty]
    · rw [ite_eq_left (show 2 * per - 1 - c < 2 * per - 1 by omega)]

end K45
