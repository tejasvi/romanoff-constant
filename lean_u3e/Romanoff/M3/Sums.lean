import Romanoff.M3.DP

/-!
# M3 soundness, part 4: the computed class sums

`sumA`, `sumB`, `sumR` and the 16 accumulators of `accG` against the linear functionals `wS` of `DP.lean`;
`phic c L = [gcd(L, 120) ∣ c] gcd(L, 120) / L`, so that `tw c m = fm m · phic c (ordm m)`.
-/

namespace Romanoff.M3

open R45.M3

/-- `[gcd(L, 120) ∣ c] gcd(L, 120) / L`. -/
noncomputable def phic (c L : ℕ) : ℝ := if Nat.gcd L 120 ∣ c then (Nat.gcd L 120 : ℝ) / (L : ℝ) else 0

theorem phic_nonneg (c L : ℕ) : 0 ≤ phic c L := by
  unfold phic; split_ifs <;> positivity

theorem tw_eq (c m : ℕ) : tw c m = fm m * phic c (ordm m) := by
  unfold tw phic
  split_ifs <;> ring

/-- `phic c L ≤ gcd(c, 120) / L`. -/
theorem phic_le (c L : ℕ) : phic c L ≤ (Nat.gcd c 120 : ℝ) / (L : ℝ) := by
  unfold phic
  split_ifs with h
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) (Nat.dvd_gcd h (Nat.gcd_dvd_right _ _))
  · positivity

/-- The bound at `0` and above `LMAX`. -/
theorem phic_big (c L : ℕ) (hL : L = 0 ∨ LMAX < L) : phic c L ≤ (Nat.gcd c 120 : ℝ) / (LMAX : ℝ) := by
  rcases hL with rfl | hL
  · simp [phic]; positivity
  · refine le_trans (phic_le c L) (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by unfold LMAX; norm_num) ?_)
    exact_mod_cast hL.le

theorem phic_lcm_big (c t L : ℕ) (ht : 1 ≤ t) (hL : L = 0 ∨ LMAX < L) :
    phic c (Nat.lcm t L) ≤ (Nat.gcd c 120 : ℝ) / (LMAX : ℝ) := by
  apply phic_big
  rcases hL with rfl | hL
  · left; simp
  · right
    exact lt_of_lt_of_le hL (Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_right t L))

/-! ## Sums over the tables -/

theorem sumA_aux : ∀ (tab : List Ent) (s : ℕ),
    ((tab.foldl (fun s x => if 1 ≤ x.L ∧ x.L ≤ LMAX then s + x.a else s) s : ℕ) : ℝ) = s + wS Ent.a chi tab
  | [], s => by simp [wS_nil]
  | x :: tab, s => by
    simp only [List.foldl_cons, wS_cons]
    rw [sumA_aux tab]
    unfold chi
    split_ifs <;> push_cast <;> ring

theorem sumA_eq (tab : List Ent) : (sumA tab : ℝ) = wS Ent.a chi tab := by
  unfold sumA; rw [sumA_aux]; simp

theorem sumB_aux : ∀ (tab : List Ent) (s : ℕ),
    ((tab.foldl (fun s x => if 1 ≤ x.L ∧ x.L ≤ LMAX then s + x.b else s) s : ℕ) : ℝ) = s + wS Ent.b chi tab
  | [], s => by simp [wS_nil]
  | x :: tab, s => by
    simp only [List.foldl_cons, wS_cons]
    rw [sumB_aux tab]
    unfold chi
    split_ifs <;> push_cast <;> ring

theorem sumB_eq (tab : List Ent) : (sumB tab : ℝ) = wS Ent.b chi tab := by
  unfold sumB; rw [sumB_aux]; simp

theorem sumR_aux (u : ℕ) : ∀ (tab : List Ent) (s : ℕ),
    ((tab.foldl (fun acc x => if 1 ≤ x.L ∧ x.L ≤ LMAX then acc + x.a / Nat.lcm x.L u else acc) s : ℕ) : ℝ) ≤
      s + wS Ent.a (fun L => 1 / (Nat.lcm u L : ℝ) * chi L) tab
  | [], s => by simp [wS_nil]
  | x :: tab, s => by
    simp only [List.foldl_cons, wS_cons]
    refine le_trans (sumR_aux u tab _) ?_
    unfold chi
    split_ifs
    · push_cast
      have h := floor_le x.a (Nat.lcm x.L u)
      rw [Nat.lcm_comm x.L u] at h ⊢
      have : (x.a : ℝ) / (Nat.lcm u x.L : ℝ) = (x.a : ℝ) * (1 / (Nat.lcm u x.L : ℝ) * 1) := by ring
      linarith
    · simp

theorem sumR_le (u : ℕ) (tab : List Ent) :
    (sumR u tab : ℝ) ≤ wS Ent.a (fun L => 1 / (Nat.lcm u L : ℝ) * chi L) tab := by
  unfold sumR
  have := sumR_aux u tab 0
  simpa using this

/-! ## The 16 accumulators -/

theorem length_addAt (g v : ℕ) : ∀ (ds xs : List ℕ), (addAt g v ds xs).length = xs.length
  | d :: ds, x :: xs => by
    unfold addAt; split_ifs
    · simp
    · simp [length_addAt g v ds xs]
  | [], xs => by simp [addAt]
  | _ :: _, [] => by simp [addAt]

theorem sumDvdAux_addAt (c g v : ℕ) : ∀ (ds xs : List ℕ), ds.length ≤ xs.length →
    sumDvdAux c ds (addAt g v ds xs) = sumDvdAux c ds xs + (if g ∈ ds ∧ c % g = 0 then v else 0)
  | [], xs, _ => by simp [addAt, sumDvdAux]
  | d :: ds, [], h => by simp at h
  | d :: ds, x :: xs, h => by
    have hlen : ds.length ≤ xs.length := by simpa using h
    by_cases h1 : d = g
    · subst h1
      have : addAt d v (d :: ds) (x :: xs) = (x + v) :: xs := by simp [addAt]
      rw [this]
      simp only [sumDvdAux, List.mem_cons, true_or, true_and]
      by_cases hc : c % d = 0 <;> simp [hc] <;> omega
    · have : addAt g v (d :: ds) (x :: xs) = x :: addAt g v ds xs := by simp [addAt, h1]
      rw [this]
      simp only [sumDvdAux]
      rw [sumDvdAux_addAt c g v ds xs hlen]
      have hm : (g ∈ d :: ds) ↔ g ∈ ds := by
        simp only [List.mem_cons]; constructor
        · rintro (h' | h')
          · exact absurd h'.symm h1
          · exact h'
        · exact fun h' => Or.inr h'
      simp only [hm]
      ring

theorem mem_div120 (g : ℕ) (hg : g ∣ 120) : g ∈ div120 := by
  have hle : g ≤ 120 := Nat.le_of_dvd (by norm_num) hg
  interval_cases g <;> simp_all (config := { decide := true }) [div120]

theorem accG_aux (c s : ℕ) : ∀ (tab : List Ent) (acc : List ℕ), acc.length = 16 →
    (sumDvd (tab.foldl (fun acc x =>
      if 1 ≤ x.L ∧ x.L ≤ LMAX then
        addAt (Nat.gcd (Nat.lcm x.L s) PER) ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s)
          div120 acc
      else acc) acc) c : ℝ) ≥ sumDvd acc c + wS Ent.b (fun L => phic c (Nat.lcm L s) * chi L) tab
  | [], acc, _ => by simp [wS_nil]
  | x :: tab, acc, hlen => by
    simp only [List.foldl_cons, wS_cons]
    split_ifs with hx
    · have hlen' : (addAt (Nat.gcd (Nat.lcm x.L s) PER)
          ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s) div120 acc).length = 16 := by
        rw [length_addAt]; exact hlen
      refine le_trans ?_ (accG_aux c s tab _ hlen')
      unfold sumDvd
      rw [sumDvdAux_addAt c _ _ div120 acc (by simp [div120, hlen])]
      have hmem : Nat.gcd (Nat.lcm x.L s) PER ∈ div120 := mem_div120 _ (Nat.gcd_dvd_right _ _)
      have hchi : chi x.L = 1 := by unfold chi; rw [if_pos hx]
      rw [hchi, mul_one]
      push_cast
      -- the entry's contribution
      have key : (x.b : ℝ) * phic c (Nat.lcm x.L s) ≤
          ((if Nat.gcd (Nat.lcm x.L s) PER ∈ div120 ∧ c % Nat.gcd (Nat.lcm x.L s) PER = 0 then
            (x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s else 0 : ℕ) : ℝ) := by
        unfold phic PER
        by_cases hd : Nat.gcd (Nat.lcm x.L s) 120 ∣ c
        · rw [if_pos hd, if_pos ⟨hmem, Nat.mod_eq_zero_of_dvd hd⟩]
          rcases Nat.eq_zero_or_pos (Nat.lcm x.L s) with h0 | hpos
          · simp [h0]
          · have := cdiv_ge (x.b * Nat.gcd (Nat.lcm x.L s) 120) (Nat.lcm x.L s) hpos
            push_cast at this
            calc (x.b : ℝ) * ((Nat.gcd (Nat.lcm x.L s) 120 : ℝ) / (Nat.lcm x.L s : ℝ))
                = (x.b : ℝ) * (Nat.gcd (Nat.lcm x.L s) 120 : ℝ) / (Nat.lcm x.L s : ℝ) := by ring
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
  have := accG_aux c s tab (List.replicate 16 0) (by simp)
  have h0 : sumDvd (List.replicate 16 0) c = 0 := by
    unfold sumDvd div120; simp [sumDvdAux]
  unfold accG
  rw [h0] at this
  simpa using this

end Romanoff.M3
