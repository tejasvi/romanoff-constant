import Romanoff.M3.Bound

/-!
# M3: `TBound` from the checked certificate

`tbound_of D hD hs h5 : TBound (teffOf D tT tR (bsOf D tT tR))` for the DP tables `tT = runDP tab0 D.gA`,
`tR = runDP tT D.gE`, given `certOK D = true`, `sumsOK D tT = true` and `R0Bound`.
-/

namespace Romanoff.M3

open R45.M3

theorem teffOf_length (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) :
    (teffOf D tT dT tR bs).length = 120 := by
  unfold teffOf
  rw [List.length_map, List.length_range]
  rfl

theorem getD_map_range (f : ℕ → ℚ) (n c : ℕ) (hc : c < n) : ((List.range n).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

theorem teffOf_getD (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) (c : ℕ) (hc : c < 120) :
    (((teffOf D tT dT tR bs).getD c 0 : ℚ) : ℝ) =
      ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) +
        tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) +
      (Nat.gcd c 120 : ℝ) * (193656 / 100000 - ((sumR 1 tR + r0bOf bs : ℕ) : ℝ) / (SC : ℝ)) := by
  have hc' : c < PER := hc
  unfold teffOf
  rw [getD_map_range _ _ _ hc']
  simp only [R0upQ, PER, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]

theorem tbound_of (D : Data) (hD : certOK D = true) (hs : sumsOK D (runDP tab0 D.gA) = true) (h5 : R0Bound) :
    TBound (teffOf D (runDP tab0 D.gA) (runDrop tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)
      (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE))) := by
  classical
  refine ⟨teffOf_length _ _ _ _ _, fun c hc S hS => ?_⟩
  rw [teffOf_getD _ _ _ _ _ c hc]
  set A : ℕ → Prop := fun m => ∀ q ∈ m.primeFactors, q ∈ (PA D).map Prod.fst with hAdef
  set Bm : ℕ → Prop := fun m => ∃ x ∈ LB D, x.1 ∣ m ∧ ∀ r ∈ (m / x.1).primeFactors, r ∈ (PA D).map Prod.fst
    with hBdef
  rw [← Finset.sum_filter_add_sum_filter_not S A,
    ← Finset.sum_filter_add_sum_filter_not (S.filter (fun m => ¬ A m)) Bm]
  have ha := classA_le D hD hs c (S.filter A) (fun m hm => by
    rw [Finset.mem_filter] at hm
    exact ⟨(hS m hm.1).2.1, hm.2⟩)
  have hb := classB_le D hD hs c ((S.filter (fun m => ¬ A m)).filter Bm) (fun m hm => by
    simp only [Finset.mem_filter] at hm
    exact ⟨(hS m hm.1.1).2.1, hm.2⟩)
  have hcc := classC_le D hD h5 ((S.filter (fun m => ¬ A m)).filter (fun m => ¬ Bm m))
    (fun m hm => by simp only [Finset.mem_filter] at hm; exact hS m hm.1.1)
    (fun m hm => by simp only [Finset.mem_filter] at hm; exact hm.1.2)
    (fun m hm => by simp only [Finset.mem_filter] at hm; exact hm.2)
  have htw : ∑ m ∈ (S.filter (fun m => ¬ A m)).filter (fun m => ¬ Bm m), tw c m ≤
      (Nat.gcd c 120 : ℝ) * ∑ m ∈ (S.filter (fun m => ¬ A m)).filter (fun m => ¬ Bm m), fm m / (ordm m : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    rw [tw_eq]
    calc fm m * phic c (ordm m) ≤ fm m * ((Nat.gcd c 120 : ℝ) / (ordm m : ℝ)) :=
          mul_le_mul_of_nonneg_left (phic_le c _) (fm_nonneg m)
      _ = (Nat.gcd c 120 : ℝ) * (fm m / (ordm m : ℝ)) := by ring
  have hR0a := R0a_le D hD
  have hR0b := R0b_le D hD
  have hg : (0 : ℝ) ≤ Nat.gcd c 120 := Nat.cast_nonneg _
  have hSC := SC_pos
  set dT := runDrop tab0 D.gA
  set tT := runDP tab0 D.gA
  set tR := runDP tT D.gE
  set bs := bsOf D tT tR
  set FsR := Fs (PR D) (fun L => 1 / (L : ℝ))
  set SLB := ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum
  have ha' : ∑ m ∈ S.filter A, tw c m ≤
      ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) : ℕ) : ℝ) / (SC : ℝ) := by
    rw [le_div_iff₀ hSC]; linarith
  have hb' : ∑ m ∈ (S.filter (fun m => ¬ A m)).filter Bm, tw c m ≤
      ((tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) := by
    rw [le_div_iff₀ hSC]; linarith
  have hR0a' : (sumR 1 tR : ℝ) / (SC : ℝ) ≤ FsR := by rw [div_le_iff₀ hSC]; linarith
  have hR0b' : (r0bOf bs : ℝ) / (SC : ℝ) ≤ SLB := by rw [div_le_iff₀ hSC]; linarith
  have hcfin : (Nat.gcd c 120 : ℝ) * (193656 / 100000 - FsR - SLB) ≤
      (Nat.gcd c 120 : ℝ) * (193656 / 100000 - ((sumR 1 tR + r0bOf bs : ℕ) : ℝ) / (SC : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hg
    push_cast; rw [add_div]; linarith
  have hcsum := le_trans htw (mul_le_mul_of_nonneg_left hcc hg)
  have hsplit : ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) +
      tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) =
      ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) : ℕ) : ℝ) / (SC : ℝ) +
      ((tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) := by
    rw [← add_div]; push_cast; ring
  rw [hsplit]
  linarith

end Romanoff.M3
