import Romanoff.M3.Final

/-!
# M3 soundness, part 7: class (c'), the R0 lower bounds and `TBound`
-/

namespace Romanoff.M3

open R45.M3

section
variable (D : Data) (hD : certOK D = true)
include hD

/-- A product of R0 primes coprime to `ell` has all its prime factors among the `gA` primes. -/
theorem prodSet_coprime_PA (m : ℕ) (hm : m ∈ prodSet (PR D)) (hc : Nat.Coprime m ell) :
    ∀ q ∈ m.primeFactors, q ∈ (PA D).map Prod.fst := by
  intro q hq
  obtain ⟨h0, _, hpf⟩ := prodSet_spec (PR D) (plist_PR D hD) m hm
  by_contra hn
  have hell := PR_ell D hD q (hpf q hq) hn
  have hqm : q ∣ m := (Nat.mem_primeFactors.mp hq).2.1
  have h1 : q ∣ Nat.gcd m ell := Nat.dvd_gcd hqm hell
  rw [hc] at h1
  exact (Nat.mem_primeFactors.mp hq).1.one_lt.ne' (Nat.dvd_one.mp h1)

theorem odd_sqf_prodSet (m : ℕ) (hm : m ∈ prodSet (PR D)) : Odd m ∧ Squarefree m := by
  obtain ⟨h0, hsq, hpf⟩ := prodSet_spec (PR D) (plist_PR D hD) m hm
  refine ⟨odd_of_primeFactors m h0 (fun q hq => ?_), hsq⟩
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (hpf q hq)
  exact ((plist_PR D hD).1 y hy).2.1

/-- Class (c'): `R0Bound` on (c') ∪ `prodSet PR` ∪ `q · prodSet PR`. -/
theorem classC_le (h5 : R0Bound) (S : Finset ℕ) (hS : ∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ell)
    (hA : ∀ m ∈ S, ¬ ∀ q ∈ m.primeFactors, q ∈ (PA D).map Prod.fst)
    (hB : ∀ m ∈ S, ¬ ∃ x ∈ LB D, x.1 ∣ m ∧ ∀ r ∈ (m / x.1).primeFactors, r ∈ (PA D).map Prod.fst) :
    ∑ m ∈ S, fm m / (ordm m : ℝ) ≤ 193656 / 100000 - Fs (PR D) (fun L => 1 / (L : ℝ)) -
      ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum := by
  have hPR := plist_PR D hD
  have hLB := plist_LB D hD
  have hLBn : ∀ y ∈ LB D, y.1 ∉ (PR D).map Prod.fst := fun y hy => LB_not_PR D hD y hy
  set U1 := prodSet (PR D)
  set U2 := UbF (PR D) (LB D)
  have hd12 : Disjoint U1 U2 := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    obtain ⟨y, hy, m', _, rfl⟩ := (mem_UbF _ _ _).mp hm2
    obtain ⟨h0, _, hpf⟩ := prodSet_spec (PR D) hPR _ hm1
    exact hLBn y hy (hpf y.1 (Nat.mem_primeFactors.mpr ⟨(hLB.1 y hy).1, dvd_mul_right _ _, h0⟩))
  have hdS : Disjoint S (U1 ∪ U2) := by
    rw [Finset.disjoint_left]
    intro m hmS hmU
    rcases Finset.mem_union.mp hmU with hm1 | hm2
    · exact hA m hmS (prodSet_coprime_PA D hD m hm1 (hS m hmS).2.2)
    · obtain ⟨y, hy, m', hm', rfl⟩ := (mem_UbF _ _ _).mp hm2
      have hq := (hLB.1 y hy).1
      have hc' : Nat.Coprime m' ell := Nat.Coprime.coprime_dvd_left (dvd_mul_left m' y.1) (hS _ hmS).2.2
      refine hB _ hmS ⟨y, hy, dvd_mul_right _ _, ?_⟩
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact prodSet_coprime_PA D hD m' hm' hc'
  have hU : ∀ m ∈ S ∪ (U1 ∪ U2), Odd m ∧ Squarefree m := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact ⟨(hS m hm).1, (hS m hm).2.1⟩
    rcases Finset.mem_union.mp hm with hm1 | hm2
    · exact odd_sqf_prodSet D hD m hm1
    · obtain ⟨y, hy, m', hm', rfl⟩ := (mem_UbF _ _ _).mp hm2
      obtain ⟨hq, hq3, _⟩ := hLB.1 y hy
      obtain ⟨hodd, hsq⟩ := odd_sqf_prodSet D hD m' hm'
      obtain ⟨h0, _, hpf⟩ := prodSet_spec (PR D) hPR m' hm'
      have hndvd : ¬ y.1 ∣ m' := fun hd => hLBn y hy (hpf y.1 (Nat.mem_primeFactors.mpr ⟨hq, hd, h0⟩))
      refine ⟨(hq.odd_of_ne_two (by omega)).mul hodd, ?_⟩
      exact Nat.squarefree_mul_iff.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd, hq.squarefree, hsq⟩
  have hbound := h5 (S ∪ (U1 ∪ U2)) hU
  rw [Finset.sum_union hdS, Finset.sum_union hd12] at hbound
  have hs1 : ∑ m ∈ U1, fm m / (orderOf (2 : ZMod m) : ℝ) = Fs (PR D) (fun L => 1 / (L : ℝ)) := by
    rw [← sum_prodSet (PR D) hPR]
    apply Finset.sum_congr rfl
    intro m _
    unfold ordm; ring
  have hs2 : ∑ m ∈ U2, fm m / (orderOf (2 : ZMod m) : ℝ) =
      ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum := by
    rw [← sum_UbF (PR D) hPR (fun L => 1 / (L : ℝ)) (LB D) hLB hLBn]
    apply Finset.sum_congr rfl
    intro m _
    unfold ordm; ring
  rw [hs1, hs2] at hbound
  have : ∑ m ∈ S, fm m / (ordm m : ℝ) = ∑ m ∈ S, fm m / (orderOf (2 : ZMod m) : ℝ) := rfl
  linarith

omit hD in
theorem one_div_lcm_ge (t L : ℕ) (ht : 1 ≤ t) (hL : 1 ≤ L) :
    1 / (t : ℝ) * (1 / (L : ℝ)) ≤ 1 / (Nat.lcm t L : ℝ) := by
  have hpos : 0 < Nat.lcm t L := Nat.lcm_pos (by omega) (by omega)
  have hle : Nat.lcm t L ≤ t * L := Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul t L)
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (by exact_mod_cast hpos)
  exact_mod_cast hle

/-- The R0 lower bound of the all-small-primes class. -/
theorem R0a_le : (sumR 1 (runDP (runDP tab0 D.gA) D.gE) : ℝ) ≤ (SC : ℝ) * Fs (PR D) (fun L => 1 / (L : ℝ)) := by
  have h1 := sumR_le 1 (runDP (runDP tab0 D.gA) D.gE)
  simp only [Nat.lcm_one_left] at h1
  have h2 := lo_bound (D.gA ++ D.gE) (threeAE D hD) (fun L => 1 / (L : ℝ)) (fun L => by positivity)
  rw [runDP_append] at h2
  exact le_trans h1 h2

/-- The R0 lower bound of one class-B group. -/
theorem R0b_grp (gx : Grp × Bool) (hgx : gx ∈ D.gB) :
    ((mkBD (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE) (sumR 1 (runDP (runDP tab0 D.gA) D.gE)) gx).r : ℝ) ≤
      (SC : ℝ) * Fs (PR D) (fun L => 1 / (Nat.lcm gx.1.t L : ℝ)) := by
  set tR := runDP (runDP tab0 D.gA) D.gE
  have ht : 1 ≤ gx.1.t := groups_tpos D hD gx.1 (groups_mem_B D gx.1 (List.mem_map.mpr ⟨gx, hgx, rfl⟩))
  have hlo := lo_bound (D.gA ++ D.gE) (threeAE D hD) (fun L => 1 / (Nat.lcm gx.1.t L : ℝ)) (fun L => by positivity)
  rw [runDP_append] at hlo
  unfold mkBD
  cases hex : gx.2
  · -- crude: ⌊R0a / t⌋
    simp only [Bool.false_eq_true, if_false]
    refine le_trans (floor_le _ _) ?_
    refine le_trans ?_ hlo
    have h1 := sumR_le 1 tR
    simp only [Nat.lcm_one_left] at h1
    have h2 : wS Ent.a (fun L => 1 / (L : ℝ) * chi L) tR / (gx.1.t : ℝ) ≤
        wS Ent.a (fun L => 1 / (Nat.lcm gx.1.t L : ℝ) * chi L) tR := by
      rw [div_eq_mul_one_div, mul_comm, ← wS_smul]
      apply wS_mono
      intro L
      unfold chi
      split_ifs with hL
      · simp only [mul_one]; exact one_div_lcm_ge gx.1.t L ht hL.1
      · simp
    calc (sumR 1 tR : ℝ) / (gx.1.t : ℝ) ≤ wS Ent.a (fun L => 1 / (L : ℝ) * chi L) tR / (gx.1.t : ℝ) :=
          div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ ≤ _ := h2
  · simp only [if_true]
    refine le_trans (sumR_le gx.1.t tR) hlo

theorem R0b_le : (r0bOf (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)) : ℝ) ≤
    (SC : ℝ) * ((LB D).map fun y => fp y.1 * Fs (PR D) (fun L => 1 / (Nat.lcm y.2 L : ℝ))).sum := by
  rw [LB_sum D]
  unfold r0bOf bsOf
  rw [Nat.cast_list_sum, List.map_map, List.map_map, ← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro gx hgx
  simp only [Function.comp]
  have h3 : ∀ p ∈ gx.1.ps, 3 ≤ p := fun p hp =>
    (groups_prime D hD gx.1 (groups_mem_B D gx.1 (List.mem_map.mpr ⟨gx, hgx, rfl⟩)) p hp).2.1
  have hFL : ((mkBD (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)
      (sumR 1 (runDP (runDP tab0 D.gA) D.gE)) gx).FL : ℝ) ≤ (SC : ℝ) * (gx.1.ps.map fp).sum := by
    have : (mkBD (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)
        (sumR 1 (runDP (runDP tab0 D.gA) D.gE)) gx).FL = (gx.1.ps.map fLo).sum := by
      unfold mkBD; split_ifs <;> rfl
    rw [this]; exact sum_fp_ge gx.1.ps h3
  have hr := R0b_grp D hD gx hgx
  have hY0 : 0 ≤ Fs (PR D) (fun L => 1 / (Nat.lcm gx.1.t L : ℝ)) :=
    Fs_nonneg _ (plist_PR D hD).three _ (fun L => by positivity)
  rw [List.sum_map_mul_right]
  refine le_trans (mulLo_le _ _) ?_
  calc _ ≤ ((SC : ℝ) * (gx.1.ps.map fp).sum) * ((SC : ℝ) * Fs (PR D) (fun L => 1 / (Nat.lcm gx.1.t L : ℝ))) / SC := by
        apply div_le_div_of_nonneg_right _ SC_pos.le
        exact mul_le_mul hFL hr (Nat.cast_nonneg _) (mul_nonneg SC_pos.le
          (List.sum_nonneg (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact fp_nonneg (h3 p hp))))
    _ = _ := by field_simp

end

end Romanoff.M3
