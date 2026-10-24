import Romanoff.E.M3.Sound
import Romanoff.E.Spec

/-!
# U3e: `TBoundA` at period 3960 from the checked M3 certificate (copy of Romanoff/U3/M3A.lean) (the class-(c) tail in alpha form)

`tboundA_of D hD hs h5 : TBoundA (tabOf D tT dT tR bs) (R0tOf tR bs)` for the DP tables of `tbound_of`.  The classes
(a') and (b') are bounded as in `tbound_of` (`classA_le`, `classB_le`).  For class (c'), group `m` by
`g = gcd(o_m, 3960)`: `tw c m = f(m) [g ∣ c] g / o_m`, so `Σ_{m ∈ S ∩ (c')} tw c m ≤ Σ_{g ∣ 3960, g ∣ c} g α_g` with
`α_g = Σ'_{m ∈ (c'), g_m = g} f(m) / o_m` (summable: its partial sums are bounded by `classC_le`), and
`Σ_g α_g = Σ'_{m ∈ (c')} f(m) / o_m ≤ R0up - R0a - R0b`.
-/

namespace Romanoff.E.M3

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD
open R45.M3E
open Romanoff.M3 hiding phic phic_nonneg tw_eq phic_le phic_big phic_lcm_big accG_aux accG_ge

/-- The tail mass bound `R0up - (sumR 1 tR + r0bOf bs) / SC` of the tables. -/
def R0tOf (tR : List Ent) (bs : List BD) : ℚ := R0upQ - ((sumR 1 tR + r0bOf bs : ℕ) : ℚ) / (SC : ℚ)

/-- `teff` without the tail term: `(T_a(c) + prune(c) + drop(c) + T_b(c)) / SC`. -/
def tabOf (D : Data) (tT : List Ent) (dT : ℕ) (_tR : List Ent) (bs : List BD) : List ℚ :=
  (List.range PER).map fun c =>
    ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) +
      tbC bs (sumB tT) (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) c : ℕ) : ℚ) / (SC : ℚ)

theorem tabOf_length (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) :
    (tabOf D tT dT tR bs).length = 3960 := by
  unfold tabOf; rw [List.length_map, List.length_range]; rfl

theorem tabOf_getD (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) (c : ℕ) (hc : c < 3960) :
    (tabOf D tT dT tR bs).getD c 0 = (teffOf D tT dT tR bs).getD c 0 - (Nat.gcd c 3960 : ℚ) * R0tOf tR bs := by
  have hc' : c < PER := hc
  unfold tabOf teffOf R0tOf
  rw [getD_map_range _ _ _ hc', getD_map_range _ _ _ hc']
  simp only [PER]
  ring

theorem tabOf_getD' (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) (c : ℕ) (hc : c < 3960) :
    (((tabOf D tT dT tR bs).getD c 0 : ℚ) : ℝ) =
      ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) +
        tbC bs (sumB tT) (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) c : ℕ) : ℝ) / (SC : ℝ) := by
  have hc' : c < PER := hc
  unfold tabOf
  rw [getD_map_range _ _ _ hc']
  push_cast
  rfl

theorem R0tOf_cast_ge (D : Data) (hD : certOK D = true) :
    (193656 / 100000 : ℝ) - Fs (PR D) (fun L => 1 / (L : ℝ)) -
      ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum ≤
      ((R0tOf (runDP (runDP tab0 D.gA) D.gE) (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)) : ℚ) : ℝ) := by
  have hR0a := R0a_le D hD
  have hR0b := R0b_le D hD
  have hSC := SC_pos
  unfold R0tOf R0upQ
  push_cast
  rw [add_div]
  have h1 : (sumR 1 (runDP (runDP tab0 D.gA) D.gE) : ℝ) / (SC : ℝ) ≤ Fs (PR D) (fun L => 1 / (L : ℝ)) := by
    rw [div_le_iff₀ hSC]; linarith
  have h2 : (r0bOf (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)) : ℝ) / (SC : ℝ) ≤
      ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum := by
    rw [div_le_iff₀ hSC]; linarith
  linarith

theorem tboundA_of (D : Data) (hD : certOK D = true) (hs : sumsOK D (runDP tab0 D.gA) = true) (h5 : R0Bound) :
    TBoundA (tabOf D (runDP tab0 D.gA) (runDrop tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)
      (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)))
      (R0tOf (runDP (runDP tab0 D.gA) D.gE) (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE))) := by
  classical
  set A : ℕ → Prop := fun m => ∀ q ∈ m.primeFactors, q ∈ (PA D).map Prod.fst with hAdef
  set Bm : ℕ → Prop := fun m => ∃ x ∈ LB D, x.1 ∣ m ∧ ∀ r ∈ (m / x.1).primeFactors, r ∈ (PA D).map Prod.fst
    with hBdef
  set Cp : ℕ → Prop := fun m => (Odd m ∧ Squarefree m ∧ Nat.Coprime m ell) ∧ ¬ A m ∧ ¬ Bm m with hCdef
  set Bnd : ℝ := 193656 / 100000 - Fs (PR D) (fun L => 1 / (L : ℝ)) -
    ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum with hBnd
  -- the class-(c') terms and their partial sums
  have hterm0 : ∀ m, 0 ≤ fm m / (ordm m : ℝ) := fun m => div_nonneg (fm_nonneg m) (Nat.cast_nonneg _)
  have hfin : ∀ T : Finset ℕ, ∑ m ∈ T, (if Cp m then fm m / (ordm m : ℝ) else 0) ≤ Bnd := by
    intro T
    rw [← Finset.sum_filter]
    exact classC_le D hD h5 (T.filter Cp)
      (fun m hm => by simp only [Finset.mem_filter] at hm; exact hm.2.1)
      (fun m hm => by simp only [Finset.mem_filter] at hm; exact hm.2.2.1)
      (fun m hm => by simp only [Finset.mem_filter] at hm; exact hm.2.2.2)
  set F : ℕ → ℕ → ℝ := fun g m => if Cp m ∧ Nat.gcd (ordm m) 3960 = g then fm m / (ordm m : ℝ) else 0 with hFdef
  have hF0 : ∀ g m, 0 ≤ F g m := fun g m => by
    simp only [hFdef]; split_ifs
    · exact hterm0 m
    · exact le_refl 0
  have hFle : ∀ g m, F g m ≤ if Cp m then fm m / (ordm m : ℝ) else 0 := fun g m => by
    simp only [hFdef]
    split_ifs with h1 h2
    · exact le_refl _
    · exact absurd h1.1 h2
    · exact hterm0 m
    · exact le_refl 0
  have hFsum : ∀ g (T : Finset ℕ), ∑ m ∈ T, F g m ≤ Bnd := fun g T =>
    (Finset.sum_le_sum fun m _ => hFle g m).trans (hfin T)
  have hsumm : ∀ g, Summable (F g) := fun g => summable_of_sum_le (hF0 g) (hFsum g)
  have hCs : Summable fun m => if Cp m then fm m / (ordm m : ℝ) else 0 :=
    summable_of_sum_le (fun m => by split_ifs; exact hterm0 m; exact le_refl 0) hfin
  set α : ℕ → ℝ := fun g => ∑' m, F g m with hαdef
  have hα0 : ∀ g, 0 ≤ α g := fun g => tsum_nonneg (hF0 g)
  -- Σ_g α_g ≤ Bnd ≤ R0tOf
  have hfib : ∀ m, ∑ g ∈ Nat.divisors 3960, F g m = if Cp m then fm m / (ordm m : ℝ) else 0 := by
    intro m
    have hmem : Nat.gcd (ordm m) 3960 ∈ Nat.divisors 3960 :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, by norm_num⟩
    rw [Finset.sum_eq_single (Nat.gcd (ordm m) 3960)]
    · simp only [hFdef, and_true]
    · intro g _ hg
      simp only [hFdef]
      rw [ite_eq_right_iff]
      intro h; exact absurd h.2.symm hg
    · intro h; exact absurd hmem h
  have hαsum : ∑ g ∈ Nat.divisors 3960, α g ≤ Bnd := by
    simp only [hαdef]
    rw [← Summable.tsum_finsetSum (fun g _ => hsumm g)]
    simp only [hfib]
    exact hCs.tsum_le_of_sum_le hfin
  refine ⟨tabOf_length _ _ _ _ _, α, hα0, hαsum.trans (R0tOf_cast_ge D hD), fun c hc S hS => ?_⟩
  rw [tabOf_getD' _ _ _ _ _ c hc]
  rw [← Finset.sum_filter_add_sum_filter_not S A,
    ← Finset.sum_filter_add_sum_filter_not (S.filter (fun m => ¬ A m)) Bm]
  have ha := classA_le D hD hs c (S.filter A) (fun m hm => by
    rw [Finset.mem_filter] at hm
    exact ⟨(hS m hm.1).2.1, hm.2⟩)
  have hb := classB_le D hD hs c ((S.filter (fun m => ¬ A m)).filter Bm) (fun m hm => by
    simp only [Finset.mem_filter] at hm
    exact ⟨(hS m hm.1.1).2.1, hm.2⟩)
  -- class (c'): Σ tw ≤ Σ_{g ∣ c} g α_g
  set SC' := (S.filter (fun m => ¬ A m)).filter (fun m => ¬ Bm m) with hSC'
  have hCm : ∀ m ∈ SC', Cp m := fun m hm => by
    simp only [hSC', Finset.mem_filter] at hm
    exact ⟨hS m hm.1.1, hm.1.2, hm.2⟩
  have hcc : ∑ m ∈ SC', tw c m ≤ ∑ g ∈ (Nat.divisors 3960).filter (· ∣ c), (g : ℝ) * α g := by
    have hmaps : ∀ m ∈ SC', Nat.gcd (ordm m) 3960 ∈ Nat.divisors 3960 := fun m _ =>
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, by norm_num⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro g _
    have hfiber : ∑ m ∈ SC' with Nat.gcd (ordm m) 3960 = g, tw c m =
        if g ∣ c then (g : ℝ) * ∑ m ∈ SC' with Nat.gcd (ordm m) 3960 = g, fm m / (ordm m : ℝ) else 0 := by
      split_ifs with hgc
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_filter] at hm
        rw [tw_eq]
        unfold phic
        rw [hm.2, if_pos hgc]
        ring
      · apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_filter] at hm
        rw [tw_eq]
        unfold phic
        rw [hm.2, if_neg hgc, mul_zero]
    rw [hfiber]
    split_ifs with hgc
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc ∑ m ∈ SC' with Nat.gcd (ordm m) 3960 = g, fm m / (ordm m : ℝ)
          = ∑ m ∈ SC' with Nat.gcd (ordm m) 3960 = g, F g m := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mem_filter] at hm
            simp only [hFdef]
            rw [if_pos ⟨hCm m hm.1, hm.2⟩]
        _ ≤ α g := (hsumm g).sum_le_tsum _ (fun m _ => hF0 g m)
    · exact le_refl 0
  have hSC := SC_pos
  set dT := runDrop tab0 D.gA
  set tT := runDP tab0 D.gA
  set tR := runDP tT D.gE
  set bs := bsOf D tT tR
  have ha' : ∑ m ∈ S.filter A, tw c m ≤
      ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) : ℕ) : ℝ) / (SC : ℝ) := by
    rw [le_div_iff₀ hSC]; linarith
  have hb' : ∑ m ∈ (S.filter (fun m => ¬ A m)).filter Bm, tw c m ≤
      ((tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) := by
    rw [le_div_iff₀ hSC]; linarith
  have hsplit : ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) +
      tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) =
      ((sumDvd (accG 1 tT) c + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c) : ℕ) : ℝ) / (SC : ℝ) +
      ((tbC bs (sumB tT) ((prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) dT c)) c : ℕ) : ℝ) / (SC : ℝ) := by
    rw [← add_div]; push_cast; ring
  rw [hsplit]
  linarith

end Romanoff.E.M3
