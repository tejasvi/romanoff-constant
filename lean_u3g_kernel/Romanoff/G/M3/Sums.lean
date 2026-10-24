import Romanoff.M3.Sums
import Romanoff.G.Spec
import RCert.M3G.Defs

/-!
# M3 at period 27720, part 4: `phic` and the 96 accumulators

The period-120 file Romanoff/M3/Sums.lean with `120 → 27720`, `div120 → divG` (96 divisors); the period-free lemmas
(`sumA_eq`, `sumB_eq`, `sumR_le`, `length_addAt`, `sumDvdAux_addAt`) are reused from it.
-/

namespace Romanoff.G.M3

open R45.M3 hiding PER accG sumDvd
open R45.M3G
open Romanoff.M3 hiding phic phic_nonneg tw_eq phic_le phic_big phic_lcm_big accG_aux accG_ge

/-- `[gcd(L, 27720) ∣ c] gcd(L, 27720) / L`. -/
noncomputable def phic (c L : ℕ) : ℝ := if Nat.gcd L 27720 ∣ c then (Nat.gcd L 27720 : ℝ) / (L : ℝ) else 0

theorem phic_nonneg (c L : ℕ) : 0 ≤ phic c L := by
  unfold phic; split_ifs <;> positivity

theorem tw_eq (c m : ℕ) : tw c m = fm m * phic c (ordm m) := by
  unfold tw phic
  split_ifs <;> ring

/-- `phic c L ≤ gcd(c, 27720) / L`. -/
theorem phic_le (c L : ℕ) : phic c L ≤ (Nat.gcd c 27720 : ℝ) / (L : ℝ) := by
  unfold phic
  split_ifs with h
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) (Nat.dvd_gcd h (Nat.gcd_dvd_right _ _))
  · positivity

/-- The bound at `0` and above `LMAX`. -/
theorem phic_big (c L : ℕ) (hL : L = 0 ∨ LMAX < L) : phic c L ≤ (Nat.gcd c 27720 : ℝ) / (LMAX : ℝ) := by
  rcases hL with rfl | hL
  · simp [phic]; positivity
  · refine le_trans (phic_le c L) (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by unfold LMAX; norm_num) ?_)
    exact_mod_cast hL.le

theorem phic_lcm_big (c t L : ℕ) (ht : 1 ≤ t) (hL : L = 0 ∨ LMAX < L) :
    phic c (Nat.lcm t L) ≤ (Nat.gcd c 27720 : ℝ) / (LMAX : ℝ) := by
  apply phic_big
  rcases hL with rfl | hL
  · left; simp
  · right
    exact lt_of_lt_of_le hL (Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_right t L))

/-! ## The 96 accumulators -/

theorem divG_complete : (List.range 27721).all (fun g => (g == 0) || (27720 % g != 0) || divG.contains g) = true := by
  decide +kernel

theorem mem_divG (g : ℕ) (hg : g ∣ 27720) : g ∈ divG := by
  have hle : g ≤ 27720 := Nat.le_of_dvd (by norm_num) hg
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have h := List.all_eq_true.mp divG_complete g (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with (h0 | h1) | h2
  · omega
  · exact absurd (Nat.mod_eq_zero_of_dvd hg) h1
  · simpa using h2

theorem accG_aux (c s : ℕ) : ∀ (tab : List Ent) (acc : List ℕ), acc.length = 96 →
    (sumDvd (tab.foldl (fun acc x =>
      if 1 ≤ x.L ∧ x.L ≤ LMAX then
        addAt (Nat.gcd (Nat.lcm x.L s) PER) ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s)
          divG acc
      else acc) acc) c : ℝ) ≥ sumDvd acc c + wS Ent.b (fun L => phic c (Nat.lcm L s) * chi L) tab
  | [], acc, _ => by simp [wS_nil]
  | x :: tab, acc, hlen => by
    simp only [List.foldl_cons, wS_cons]
    split_ifs with hx
    · have hlen' : (addAt (Nat.gcd (Nat.lcm x.L s) PER)
          ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s) divG acc).length = 96 := by
        rw [length_addAt]; exact hlen
      refine le_trans ?_ (accG_aux c s tab _ hlen')
      unfold sumDvd
      rw [sumDvdAux_addAt c _ _ divG acc (by simp [divG, hlen])]
      have hmem : Nat.gcd (Nat.lcm x.L s) PER ∈ divG := mem_divG _ (Nat.gcd_dvd_right _ _)
      have hchi : chi x.L = 1 := by unfold chi; rw [if_pos hx]
      rw [hchi, mul_one]
      push_cast
      -- the entry's contribution
      have key : (x.b : ℝ) * phic c (Nat.lcm x.L s) ≤
          ((if Nat.gcd (Nat.lcm x.L s) PER ∈ divG ∧ c % Nat.gcd (Nat.lcm x.L s) PER = 0 then
            (x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s else 0 : ℕ) : ℝ) := by
        unfold phic PER
        by_cases hd : Nat.gcd (Nat.lcm x.L s) 27720 ∣ c
        · rw [if_pos hd, if_pos ⟨hmem, Nat.mod_eq_zero_of_dvd hd⟩]
          rcases Nat.eq_zero_or_pos (Nat.lcm x.L s) with h0 | hpos
          · simp [h0]
          · have := cdiv_ge (x.b * Nat.gcd (Nat.lcm x.L s) 27720) (Nat.lcm x.L s) hpos
            push_cast at this
            calc (x.b : ℝ) * ((Nat.gcd (Nat.lcm x.L s) 27720 : ℝ) / (Nat.lcm x.L s : ℝ))
                = (x.b : ℝ) * (Nat.gcd (Nat.lcm x.L s) 27720 : ℝ) / (Nat.lcm x.L s : ℝ) := by ring
              _ ≤ _ := this
        · rw [if_neg hd]
          split_ifs <;> simp
      push_cast at key ⊢
      linarith
    · have hchi : chi x.L = 0 := by unfold chi; rw [if_neg hx]
      rw [hchi, mul_zero, mul_zero, zero_add]
      exact accG_aux c s tab acc hlen

theorem accG_ge (c s : ℕ) (tab : List Ent) :
    wS Ent.b (fun L => phic c (Nat.lcm L s) * chi L) tab ≤ (sumDvd (accG s tab) c : ℝ) := by
  have := accG_aux c s tab (List.replicate 96 0) (by simp)
  have h0 : sumDvd (List.replicate 96 0) c = 0 := by
    unfold sumDvd divG; simp [sumDvdAux]
  unfold accG
  rw [h0] at this
  simpa using this

end Romanoff.G.M3
