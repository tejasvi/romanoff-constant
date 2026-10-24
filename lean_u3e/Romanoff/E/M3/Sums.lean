import Romanoff.M3.Sums
import Romanoff.E.Spec
import RCert.M3E.Defs

/-!
# M3 at period 3960, part 4: `phic` and the 48 accumulators

The period-120 file Romanoff/M3/Sums.lean with `120 → 3960`, `div120 → divE` (48 divisors); the period-free lemmas
(`sumA_eq`, `sumB_eq`, `sumR_le`, `length_addAt`, `sumDvdAux_addAt`) are reused from it.
-/

namespace Romanoff.E.M3

open R45.M3 hiding PER accG sumDvd
open R45.M3E
open Romanoff.M3 hiding phic phic_nonneg tw_eq phic_le phic_big phic_lcm_big accG_aux accG_ge

/-- `[gcd(L, 3960) ∣ c] gcd(L, 3960) / L`. -/
noncomputable def phic (c L : ℕ) : ℝ := if Nat.gcd L 3960 ∣ c then (Nat.gcd L 3960 : ℝ) / (L : ℝ) else 0

theorem phic_nonneg (c L : ℕ) : 0 ≤ phic c L := by
  unfold phic; split_ifs <;> positivity

theorem tw_eq (c m : ℕ) : tw c m = fm m * phic c (ordm m) := by
  unfold tw phic
  split_ifs <;> ring

/-- `phic c L ≤ gcd(c, 3960) / L`. -/
theorem phic_le (c L : ℕ) : phic c L ≤ (Nat.gcd c 3960 : ℝ) / (L : ℝ) := by
  unfold phic
  split_ifs with h
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) (Nat.dvd_gcd h (Nat.gcd_dvd_right _ _))
  · positivity

/-- The bound at `0` and above `LMAX`. -/
theorem phic_big (c L : ℕ) (hL : L = 0 ∨ LMAX < L) : phic c L ≤ (Nat.gcd c 3960 : ℝ) / (LMAX : ℝ) := by
  rcases hL with rfl | hL
  · simp [phic]; positivity
  · refine le_trans (phic_le c L) (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by unfold LMAX; norm_num) ?_)
    exact_mod_cast hL.le

theorem phic_lcm_big (c t L : ℕ) (ht : 1 ≤ t) (hL : L = 0 ∨ LMAX < L) :
    phic c (Nat.lcm t L) ≤ (Nat.gcd c 3960 : ℝ) / (LMAX : ℝ) := by
  apply phic_big
  rcases hL with rfl | hL
  · left; simp
  · right
    exact lt_of_lt_of_le hL (Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_right t L))

/-! ## The 48 accumulators -/

theorem divE_complete : (List.range 3961).all (fun g => (g == 0) || (3960 % g != 0) || divE.contains g) = true := by
  decide +kernel

theorem mem_divE (g : ℕ) (hg : g ∣ 3960) : g ∈ divE := by
  have hle : g ≤ 3960 := Nat.le_of_dvd (by norm_num) hg
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have h := List.all_eq_true.mp divE_complete g (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with (h0 | h1) | h2
  · omega
  · exact absurd (Nat.mod_eq_zero_of_dvd hg) h1
  · simpa using h2

theorem accG_aux (c s : ℕ) : ∀ (tab : List Ent) (acc : List ℕ), acc.length = 48 →
    (sumDvd (tab.foldl (fun acc x =>
      if 1 ≤ x.L ∧ x.L ≤ LMAX then
        addAt (Nat.gcd (Nat.lcm x.L s) PER) ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s)
          divE acc
      else acc) acc) c : ℝ) ≥ sumDvd acc c + wS Ent.b (fun L => phic c (Nat.lcm L s) * chi L) tab
  | [], acc, _ => by simp [wS_nil]
  | x :: tab, acc, hlen => by
    simp only [List.foldl_cons, wS_cons]
    split_ifs with hx
    · have hlen' : (addAt (Nat.gcd (Nat.lcm x.L s) PER)
          ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s) divE acc).length = 48 := by
        rw [length_addAt]; exact hlen
      refine le_trans ?_ (accG_aux c s tab _ hlen')
      unfold sumDvd
      rw [sumDvdAux_addAt c _ _ divE acc (by simp [divE, hlen])]
      have hmem : Nat.gcd (Nat.lcm x.L s) PER ∈ divE := mem_divE _ (Nat.gcd_dvd_right _ _)
      have hchi : chi x.L = 1 := by unfold chi; rw [if_pos hx]
      rw [hchi, mul_one]
      push_cast
      -- the entry's contribution
      have key : (x.b : ℝ) * phic c (Nat.lcm x.L s) ≤
          ((if Nat.gcd (Nat.lcm x.L s) PER ∈ divE ∧ c % Nat.gcd (Nat.lcm x.L s) PER = 0 then
            (x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s else 0 : ℕ) : ℝ) := by
        unfold phic PER
        by_cases hd : Nat.gcd (Nat.lcm x.L s) 3960 ∣ c
        · rw [if_pos hd, if_pos ⟨hmem, Nat.mod_eq_zero_of_dvd hd⟩]
          rcases Nat.eq_zero_or_pos (Nat.lcm x.L s) with h0 | hpos
          · simp [h0]
          · have := cdiv_ge (x.b * Nat.gcd (Nat.lcm x.L s) 3960) (Nat.lcm x.L s) hpos
            push_cast at this
            calc (x.b : ℝ) * ((Nat.gcd (Nat.lcm x.L s) 3960 : ℝ) / (Nat.lcm x.L s : ℝ))
                = (x.b : ℝ) * (Nat.gcd (Nat.lcm x.L s) 3960 : ℝ) / (Nat.lcm x.L s : ℝ) := by ring
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
  have := accG_aux c s tab (List.replicate 48 0) (by simp)
  have h0 : sumDvd (List.replicate 48 0) c = 0 := by
    unfold sumDvd divE; simp [sumDvdAux]
  unfold accG
  rw [h0] at this
  simpa using this

end Romanoff.E.M3
