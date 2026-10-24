import Romanoff.M3.Main

/-!
# M3 soundness, part 6: the class bounds and `TBound`

`tbound_of`: `certOK D`, `sumsOK D tT`, `R0Bound` ⊢ `TBound (teffOf D tT tR (bsOf D tT tR))` for the DP tables
`tT = runDP tab0 D.gA`, `tR = runDP tT D.gE`.
-/

namespace Romanoff.M3

open R45.M3

theorem wS_mono (sel : Ent → ℕ) (H H' : ℕ → ℝ) (h : ∀ L, H L ≤ H' L) (tab : List Ent) :
    wS sel H tab ≤ wS sel H' tab := by
  unfold wS
  apply List.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x.L) (Nat.cast_nonneg _)

theorem wS_smul (sel : Ent → ℕ) (k : ℝ) (H : ℕ → ℝ) (tab : List Ent) :
    wS sel (fun L => k * H L) tab = k * wS sel H tab := by
  unfold wS
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro x _
  ring

theorem wS_congr (sel : Ent → ℕ) (H H' : ℕ → ℝ) (h : ∀ L, H L = H' L) (tab : List Ent) :
    wS sel H tab = wS sel H' tab := by
  rw [show H = H' from funext h]

/-- Products of `q ∈ ys` with the sublist products of `P`. -/
def UbF (P : List (ℕ × ℕ)) : List (ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | y :: ys => (prodSet P).image (y.1 * ·) ∪ UbF P ys

theorem mem_UbF (P : List (ℕ × ℕ)) : ∀ (ys : List (ℕ × ℕ)) (m : ℕ),
    m ∈ UbF P ys ↔ ∃ y ∈ ys, ∃ m' ∈ prodSet P, y.1 * m' = m
  | [], m => by simp [UbF]
  | y :: ys, m => by
    simp only [UbF, Finset.mem_union, Finset.mem_image, mem_UbF P ys m, List.mem_cons, exists_eq_or_imp]

theorem sum_UbF (P : List (ℕ × ℕ)) (hP : PList P) (φ : ℕ → ℝ) : ∀ (ys : List (ℕ × ℕ)), PList ys →
    (∀ y ∈ ys, y.1 ∉ P.map Prod.fst) →
    ∑ m ∈ UbF P ys, fm m * φ (ordm m) = (ys.map fun y => fp y.1 * Fs P (fun L => φ (Nat.lcm y.2 L))).sum
  | [], _, _ => by simp [UbF]
  | y :: ys, hys, hyP => by
    obtain ⟨hp, _, hord⟩ := hys.head
    have hyP' : ∀ z ∈ ys, z.1 ∉ P.map Prod.fst := fun z hz => hyP z (List.mem_cons_of_mem _ hz)
    simp only [UbF, List.map_cons, List.sum_cons]
    have hdisj : Disjoint ((prodSet P).image (y.1 * ·)) (UbF P ys) := by
      rw [Finset.disjoint_left]
      intro m hm hm'
      obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨z, hz, m2, hm2, hzm⟩ := (mem_UbF P ys _).mp hm'
      have hzp := (hys.tail.1 z hz).1
      have hyz : y.1 ≠ z.1 := by
        intro h; apply hys.not_mem; rw [h]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
      have hdvd : y.1 ∣ z.1 * m2 := ⟨m1, hzm⟩
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact hyz ((Nat.prime_dvd_prime_iff_eq hp hzp).mp h)
      · obtain ⟨h0, _, hpf⟩ := prodSet_spec P hP m2 hm2
        exact hyP y (by simp) (hpf y.1 (Nat.mem_primeFactors.mpr ⟨hp, h, h0⟩))
    rw [Finset.sum_union hdisj, sum_image_prodSet y.1 y.2 hp hord P hP (hyP y (by simp)) φ (sum_prodSet P hP),
      sum_UbF P hP φ ys hys.tail hyP']

section
variable (D : Data) (hD : certOK D = true)
include hD

theorem threeA : ∀ g ∈ D.gA, ∀ p ∈ g.ps, 3 ≤ p :=
  fun g hg p hp => (groups_prime D hD g (groups_mem_A D g hg) p hp).2.1

theorem threeAE : ∀ g ∈ D.gA ++ D.gE, ∀ p ∈ g.ps, 3 ≤ p := by
  intro g hg p hp
  rcases List.mem_append.mp hg with h | h
  · exact (groups_prime D hD g (groups_mem_A D g h) p hp).2.1
  · exact (groups_prime D hD g (groups_mem_E D g h) p hp).2.1

/-- The upper bound for `Fs PA φ` from the T table, with the pruned mass as a natural number. -/
theorem FsA_le (hs : sumsOK D (runDP tab0 D.gA) = true) (φ : ℕ → ℝ) (hφ0 : ∀ L, 0 ≤ φ L) (B : ℝ)
    (hB : ∀ L, (L = 0 ∨ LMAX < L) → φ L ≤ B) (K : ℝ) (hK0 : 0 ≤ K) (hK : Decay φ K) :
    (SC : ℝ) * Fs (PA D) φ ≤ wS Ent.b (fun L => φ L * chi L) (runDP tab0 D.gA) +
      K * ((piUp D.gA : ℝ) / SC) * (runDrop tab0 D.gA : ℝ) + B * ((piUp D.gA - sumA (runDP tab0 D.gA) : ℕ) : ℝ) := by
  have := T_bound D.gA (threeA D hD) φ hφ0 B hB K hK0 hK
  unfold sumsOK at hs
  rw [Nat.cast_sub (by simpa using hs), sumA_eq]
  exact this

omit hD in
theorem drop_le (piU dD c : ℕ) : (Nat.gcd c 120 : ℝ) * ((piU : ℝ) / SC) * (dD : ℝ) ≤ (drC piU dD c : ℝ) := by
  unfold drC cdiv PER
  have := cdiv_ge (Nat.gcd c 120 * piU * dD) SC (by unfold SC; positivity)
  push_cast at this
  calc (Nat.gcd c 120 : ℝ) * ((piU : ℝ) / SC) * (dD : ℝ) = (Nat.gcd c 120 : ℝ) * (piU : ℝ) * (dD : ℝ) / SC := by ring
    _ ≤ _ := this

omit hD in
theorem decay_phic (c : ℕ) : Decay (phic c) (Nat.gcd c 120) := fun L _ => phic_le c L

omit hD in
theorem decay_phic_lcm (c t : ℕ) (ht : 1 ≤ t) : Decay (fun L => phic c (Nat.lcm t L)) (Nat.gcd c 120) := by
  intro L hL
  have hpos : 0 < Nat.lcm t L := Nat.lcm_pos (by omega) (by omega)
  refine le_trans (phic_le c _) (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hL) ?_)
  exact_mod_cast Nat.le_of_dvd hpos (Nat.dvd_lcm_right t L)

omit hD in
theorem prune_le (prM c : ℕ) : (Nat.gcd c 120 : ℝ) / (LMAX : ℝ) * (prM : ℝ) ≤ (prC prM c : ℝ) := by
  unfold prC cdiv PER
  have := cdiv_ge (prM * Nat.gcd c 120) LMAX (by unfold LMAX; norm_num)
  push_cast at this
  calc (Nat.gcd c 120 : ℝ) / (LMAX : ℝ) * (prM : ℝ) = (prM : ℝ) * (Nat.gcd c 120 : ℝ) / (LMAX : ℝ) := by ring
    _ ≤ _ := this

/-- Class (a'). -/
theorem classA_le (hs : sumsOK D (runDP tab0 D.gA) = true) (c : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ ∀ q ∈ m.primeFactors, q ∈ (PA D).map Prod.fst) :
    (SC : ℝ) * ∑ m ∈ S, tw c m ≤
      (sumDvd (accG 1 (runDP tab0 D.gA)) c + (prC (piUp D.gA - sumA (runDP tab0 D.gA)) c + drC (piUp D.gA) (runDrop tab0 D.gA) c) : ℕ) := by
  have h1 : ∑ m ∈ S, tw c m ≤ Fs (PA D) (phic c) := by
    simp only [tw_eq]
    exact sum_le_Fs (PA D) (plist_PA D hD) (phic c) (phic_nonneg c) S hS
  have h2 := FsA_le D hD hs (phic c) (phic_nonneg c) _ (phic_big c) _ (Nat.cast_nonneg _) (decay_phic c)
  have h3 := accG_ge c 1 (runDP tab0 D.gA)
  simp only [Nat.lcm_one_right] at h3
  have h4 := prune_le (piUp D.gA - sumA (runDP tab0 D.gA)) c
  have h5 := drop_le (piUp D.gA) (runDrop tab0 D.gA) c
  have h1' := mul_le_mul_of_nonneg_left h1 SC_pos.le
  push_cast
  linarith

/-- One class-B group. -/
theorem classB_grp (hs : sumsOK D (runDP tab0 D.gA) = true) (c : ℕ) (gx : Grp × Bool) (hgx : gx ∈ D.gB) :
    (SC : ℝ) * Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L)) ≤
      (((if gx.2 then sumDvd (accG gx.1.t (runDP tab0 D.gA)) c
        else cdiv (sumB (runDP tab0 D.gA) * Nat.gcd c PER) gx.1.t) +
        (prC (piUp D.gA - sumA (runDP tab0 D.gA)) c + drC (piUp D.gA) (runDrop tab0 D.gA) c) : ℕ) : ℝ) := by
  have ht : 1 ≤ gx.1.t := groups_tpos D hD gx.1 (groups_mem_B D gx.1 (List.mem_map.mpr ⟨gx, hgx, rfl⟩))
  have h2 := FsA_le D hD hs (fun L => phic c (Nat.lcm gx.1.t L)) (fun L => phic_nonneg c _) _
    (fun L hL => phic_lcm_big c gx.1.t L ht hL) _ (Nat.cast_nonneg _) (decay_phic_lcm c gx.1.t ht)
  have h4 := prune_le (piUp D.gA - sumA (runDP tab0 D.gA)) c
  have h5 := drop_le (piUp D.gA) (runDrop tab0 D.gA) c
  set tT := runDP tab0 D.gA
  have hA : wS Ent.b (fun L => phic c (Nat.lcm gx.1.t L) * chi L) tT ≤
      ((if gx.2 then sumDvd (accG gx.1.t tT) c else cdiv (sumB tT * Nat.gcd c PER) gx.1.t : ℕ) : ℝ) := by
    split_ifs with hex
    · have h3 := accG_ge c gx.1.t tT
      rw [wS_congr Ent.b _ (fun L => phic c (Nat.lcm gx.1.t L) * chi L) (fun L => by rw [Nat.lcm_comm])] at h3
      exact h3
    · have hle : wS Ent.b (fun L => phic c (Nat.lcm gx.1.t L) * chi L) tT ≤
          wS Ent.b (fun L => (Nat.gcd c 120 : ℝ) / (gx.1.t : ℝ) * chi L) tT := by
        apply wS_mono
        intro L
        unfold chi
        split_ifs with hL
        · rw [mul_one, mul_one]
          refine le_trans (phic_le c _) (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast ht) ?_)
          exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_left _ _)
        · simp
      rw [wS_smul, ← sumB_eq] at hle
      refine le_trans hle ?_
      unfold cdiv PER
      have := cdiv_ge (sumB tT * Nat.gcd c 120) gx.1.t (by omega)
      push_cast at this ⊢
      calc (Nat.gcd c 120 : ℝ) / (gx.1.t : ℝ) * (sumB tT : ℝ)
          = (sumB tT : ℝ) * (Nat.gcd c 120 : ℝ) / (gx.1.t : ℝ) := by ring
        _ ≤ _ := this
  push_cast at hA ⊢
  linarith

omit hD in
/-- The class-B weight sum of a group: `Σ_q f(q) ≤ FU / SC`. -/
theorem sum_fp_le (ps : List ℕ) (h : ∀ p ∈ ps, 3 ≤ p) : (SC : ℝ) * (ps.map fp).sum ≤ ((ps.map fUp).sum : ℕ) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    push_cast
    have h1 := fUp_ge p (h p (by simp))
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    push_cast at h2
    nlinarith

omit hD in
theorem sum_fp_ge (ps : List ℕ) (h : ∀ p ∈ ps, 3 ≤ p) : (((ps.map fLo).sum : ℕ) : ℝ) ≤ (SC : ℝ) * (ps.map fp).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    push_cast
    have h1 := fLo_le p (h p (by simp))
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    push_cast at h2
    nlinarith

omit hD in
theorem LB_sum (F : ℕ × ℕ → ℝ) :
    ((LB D).map F).sum = (D.gB.map fun gx => (gx.1.ps.map fun q => F (q, gx.1.t)).sum).sum := by
  unfold LB
  generalize D.gB = l
  induction l with
  | nil => simp [flatG]
  | cons gx l ih =>
    simp only [List.map_cons, flatG_cons, List.map_append, List.sum_append, List.sum_cons, ih, List.map_map,
      Function.comp_def]

/-- Class (b'). -/
theorem classB_le (hs : sumsOK D (runDP tab0 D.gA) = true) (c : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧
      ∃ x ∈ LB D, x.1 ∣ m ∧ ∀ r ∈ (m / x.1).primeFactors, r ∈ (PA D).map Prod.fst) :
    (SC : ℝ) * ∑ m ∈ S, tw c m ≤
      (tbC (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)) (sumB (runDP tab0 D.gA))
        ((prC (piUp D.gA - sumA (runDP tab0 D.gA)) c + drC (piUp D.gA) (runDrop tab0 D.gA) c)) c : ℝ) := by
  classical
  set tT := runDP tab0 D.gA
  set tR := runDP (runDP tab0 D.gA) D.gE
  -- cover by the class-B primes
  have hcov := sum_le_cover S (LB D) (fun x m => x.1 ∣ m ∧ ∀ r ∈ (m / x.1).primeFactors, r ∈ (PA D).map Prod.fst)
    (tw c) (fun m => by rw [tw_eq]; exact mul_nonneg (fm_nonneg m) (phic_nonneg c _)) (fun m hm => (hS m hm).2)
  have hone : ∀ x ∈ LB D, ∑ m ∈ S.filter (fun m => x.1 ∣ m ∧ ∀ r ∈ (m / x.1).primeFactors, r ∈ (PA D).map Prod.fst),
      tw c m ≤ fp x.1 * Fs (PA D) (fun L => phic c (Nat.lcm x.2 L)) := by
    intro x hx
    obtain ⟨hq, _, hord⟩ := (plist_LB D hD).1 x hx
    have hqA : x.1 ∉ (PA D).map Prod.fst := fun h => LB_not_PR D hD x hx (PA_sub_PR D x.1 h)
    rw [← sum_image_prodSet x.1 x.2 hq hord (PA D) (plist_PA D hD) hqA (phic c) (sum_prodSet _ (plist_PA D hD))]
    simp only [tw_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨hmS, hdvd, hpf⟩ := hm
      refine Finset.mem_image.mpr ⟨m / x.1, ?_, Nat.mul_div_cancel' hdvd⟩
      apply mem_prodSet (PA D) (plist_PA D hD) _ _ hpf
      have hsq := (hS m hmS).1
      rw [← Nat.mul_div_cancel' hdvd] at hsq
      exact hsq.of_mul_right
    · intro m _ _; exact mul_nonneg (fm_nonneg m) (phic_nonneg c _)
  have hB1 : ∑ m ∈ S, tw c m ≤ ((LB D).map fun x => fp x.1 * Fs (PA D) (fun L => phic c (Nat.lcm x.2 L))).sum :=
    le_trans hcov (List.sum_le_sum (fun x hx => hone x hx))
  rw [LB_sum D] at hB1
  have hgrp : ∀ gx ∈ D.gB,
      (SC : ℝ) * (gx.1.ps.map fun q => fp q * Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L))).sum ≤
      ((fun d : BD => ((mulUp d.FU ((if d.ex then sumDvd d.acc c else cdiv (sumB tT * Nat.gcd c PER) d.t) +
          (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) (runDrop tab0 D.gA) c)) : ℕ) : ℝ)) (mkBD tT tR (sumR 1 tR) gx)) := by
    intro gx hgx
    have hFU : (mkBD tT tR (sumR 1 tR) gx).FU = (gx.1.ps.map fUp).sum := by
      unfold mkBD; split_ifs <;> rfl
    have hV : (if (mkBD tT tR (sumR 1 tR) gx).ex then sumDvd (mkBD tT tR (sumR 1 tR) gx).acc c
          else cdiv (sumB tT * Nat.gcd c PER) (mkBD tT tR (sumR 1 tR) gx).t) =
        (if gx.2 then sumDvd (accG gx.1.t tT) c else cdiv (sumB tT * Nat.gcd c PER) gx.1.t) := by
      unfold mkBD
      cases gx.2 <;> rfl
    simp only
    rw [hFU, hV]
    have hY := classB_grp D hD hs c gx hgx
    have h3 : ∀ p ∈ gx.1.ps, 3 ≤ p := fun p hp =>
      (groups_prime D hD gx.1 (groups_mem_B D gx.1 (List.mem_map.mpr ⟨gx, hgx, rfl⟩)) p hp).2.1
    have hF := sum_fp_le gx.1.ps h3
    rw [List.sum_map_mul_right]
    have hY0 : 0 ≤ Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L)) :=
      Fs_nonneg _ (plist_PA D hD).three _ (fun L => phic_nonneg c _)
    have hmul := mulUp_ge (gx.1.ps.map fUp).sum
      ((if gx.2 then sumDvd (accG gx.1.t tT) c else cdiv (sumB tT * Nat.gcd c PER) gx.1.t) +
        (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) (runDrop tab0 D.gA) c))
    calc (SC : ℝ) * ((gx.1.ps.map fp).sum * Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L)))
        = ((SC : ℝ) * (gx.1.ps.map fp).sum) * ((SC : ℝ) * Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L))) / SC := by
          field_simp
      _ ≤ (((gx.1.ps.map fUp).sum : ℕ) : ℝ) *
            ((((if gx.2 then sumDvd (accG gx.1.t tT) c else cdiv (sumB tT * Nat.gcd c PER) gx.1.t) +
              (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) (runDrop tab0 D.gA) c) : ℕ) : ℝ)) / SC := by
          apply div_le_div_of_nonneg_right _ SC_pos.le
          exact mul_le_mul hF hY (mul_nonneg SC_pos.le hY0) (Nat.cast_nonneg _)
      _ ≤ _ := hmul
  calc (SC : ℝ) * ∑ m ∈ S, tw c m
      ≤ (SC : ℝ) * (D.gB.map fun gx =>
          (gx.1.ps.map fun q => fp q * Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L))).sum).sum :=
        mul_le_mul_of_nonneg_left hB1 SC_pos.le
    _ = (D.gB.map fun gx => (SC : ℝ) *
          (gx.1.ps.map fun q => fp q * Fs (PA D) (fun L => phic c (Nat.lcm gx.1.t L))).sum).sum := by
        rw [List.sum_map_mul_left]
    _ ≤ (D.gB.map fun gx => ((fun d : BD => ((mulUp d.FU ((if d.ex then sumDvd d.acc c
          else cdiv (sumB tT * Nat.gcd c PER) d.t) + (prC (piUp D.gA - sumA tT) c + drC (piUp D.gA) (runDrop tab0 D.gA) c)) : ℕ) : ℝ))
          (mkBD tT tR (sumR 1 tR) gx))).sum := List.sum_le_sum hgrp
    _ = _ := by
        unfold tbC bsOf
        rw [Nat.cast_list_sum, List.map_map, List.map_map]
        rfl

end

end Romanoff.M3
