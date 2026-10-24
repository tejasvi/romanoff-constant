import Romanoff.E.S2.Value
import RCert.E.BLit

/-!
# U3e stage 2: the minorant of one row

`mino`: for every `α ≥ 0` with `Σ_{g ∈ divE} α_g ≤ R0t + δ`, every exclusion mask `X` and every `J ≥ 1`,
`vt J |U| Q(U) ≤ phiCls (parOf (teffA (tabB BLit) α) 8 0) 3960 X`: with `μ = 0` the class term is
`(norm/l') s φ(1 + Ymax/s)`; Pintz's inequality `φ(D) ≥ (2J + 1 - D)/(J (J+1))`; `Ymax = 8 κ Σ_g (B_g + g α_g) S_g`
(divisor lemma, `N_g(n_U) = S_g`), `B_g ≤ bn_g / 2^36` and `g S_g ≤ 3960 s`.
-/

open Finset R45 R45.EV R45.U3E

namespace Romanoff.E.S2

/-- `0 ≤ B_g ≤ bn_g / 2^36` for the 48 divisors. -/
theorem bn_ok : ∀ i < 48, 0 ≤ BLit (dA.getD i 0) ∧ BLit (dA.getD i 0) ≤ (bnA.getD i 0 : ℚ) / 2 ^ 36 := by
  decide +kernel

theorem divE_eq_dA : R45.M3E.divE = dA.toList := rfl

theorem divE_sum (f : ℕ → ℚ) : (R45.M3E.divE.map f).sum = ∑ i ∈ range 48, f (dA.getD i 0) := by
  rw [divE_eq_dA, ← range_map_sum]
  have h : dA.toList = (List.range 48).map fun i => dA.getD i 0 := by decide
  rw [h, List.map_map]
  rfl

theorem dA_mem (i : ℕ) (hi : i < 48) : dA.getD i 0 ∈ R45.M3E.divE := by
  rw [divE_eq_dA]
  have h : dA.toList = (List.range 48).map fun i => dA.getD i 0 := by decide
  rw [h]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem normE_nonneg : (0 : ℚ) ≤ PE.norm := by
  unfold PE.norm PE.ellN PE.philN PE.per R45.D45.log2hi
  norm_num [PE.ellPO]

theorem kapE_nonneg : (0 : ℚ) ≤ PE.kap := by
  unfold PE.kap PE.pell PE.per R45.D45.C0up R45.D45.log2lo
  norm_num [PE.ellPO]

theorem ellE_pos : (0 : ℚ) < (PE.ellN : ℚ) := by
  unfold PE.ellN; norm_num [PE.ellPO]

theorem foldl_min_zero (f : ℚ → ℚ) (hf : ∀ y, f y = 0) : ∀ (L : List ℚ), L.foldl (fun b y => min b (f y)) 0 = 0
  | [] => rfl
  | y :: L => by rw [List.foldl_cons, hf, min_self, foldl_min_zero f hf L]

/-- With `μ = 0`, `minQ P 0 _ = 0`. -/
theorem minQ_zero_s (P : Par) (hmu : P.mu = 0) (y : ℚ) : minQ P 0 y = 0 := by
  have hg : ∀ Y, gQ P 0 Y = 0 := by intro Y; unfold gQ; rw [hmu]; simp
  unfold minQ
  rw [hg]
  exact foldl_min_zero _ hg _

theorem S_zero_of (X : ℕ) (h : cnt X 1 0 = 0) {g : ℕ} (hg0 : 0 < g) : S X g = 0 := by
  have h1 := sum_cnt X hg0
  rw [h] at h1
  unfold S
  apply sum_eq_zero
  intro a ha
  have : cnt X g a = 0 := (sum_eq_zero_iff.mp h1) a ha
  rw [this]; rfl

theorem Qs_zero_of (X : ℕ) (h : cnt X 1 0 = 0) : Qs X = 0 := by
  unfold Qs
  apply sum_eq_zero
  intro i hi
  rw [S_zero_of X h (dA_facts i (mem_range.mp hi)).1, mul_zero]

/-- `Σ_{g ∈ divE} (B_g + g α_g) S_g ≤ Q / 2^36 + 3960 s (R0t + δ)`. -/
theorem dot_bound (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3E.divE.map α).sum ≤ M3E.R0tLit + delta) (X : ℕ) :
    (R45.M3E.divE.map fun g => (BLit g + (g : ℚ) * α g) * (S X g : ℚ)).sum ≤
      (Qs X : ℚ) / 2 ^ 36 + 3960 * (cnt X 1 0 : ℚ) * (M3E.R0tLit + delta) := by
  rw [divE_sum]
  have h1 : ∀ i ∈ range 48, (BLit (dA.getD i 0) + (dA.getD i 0 : ℚ) * α (dA.getD i 0)) * (S X (dA.getD i 0) : ℚ) ≤
      (bnA.getD i 0 : ℚ) / 2 ^ 36 * (S X (dA.getD i 0) : ℚ) + α (dA.getD i 0) * (3960 * (cnt X 1 0 : ℚ)) := by
    intro i hi
    have hi' := mem_range.mp hi
    obtain ⟨_, hb⟩ := bn_ok i hi'
    obtain ⟨hg0, hg⟩ := dA_facts i hi'
    have hS : (dA.getD i 0 : ℚ) * (S X (dA.getD i 0) : ℚ) ≤ 3960 * (cnt X 1 0 : ℚ) := by
      exact_mod_cast S_le X hg hg0
    have hS0 : (0 : ℚ) ≤ (S X (dA.getD i 0) : ℚ) := Nat.cast_nonneg _
    calc (BLit (dA.getD i 0) + (dA.getD i 0 : ℚ) * α (dA.getD i 0)) * (S X (dA.getD i 0) : ℚ)
        = BLit (dA.getD i 0) * (S X (dA.getD i 0) : ℚ) +
            α (dA.getD i 0) * ((dA.getD i 0 : ℚ) * (S X (dA.getD i 0) : ℚ)) := by ring
      _ ≤ (bnA.getD i 0 : ℚ) / 2 ^ 36 * (S X (dA.getD i 0) : ℚ) + α (dA.getD i 0) * (3960 * (cnt X 1 0 : ℚ)) :=
          add_le_add (mul_le_mul_of_nonneg_right hb hS0) (mul_le_mul_of_nonneg_left hS (hα _))
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib]
  have e1 : ∑ i ∈ range 48, (bnA.getD i 0 : ℚ) / 2 ^ 36 * (S X (dA.getD i 0) : ℚ) = (Qs X : ℚ) / 2 ^ 36 := by
    unfold Qs; push_cast; rw [sum_div]; apply sum_congr rfl; intro i _; ring
  have e2 : ∑ i ∈ range 48, α (dA.getD i 0) * (3960 * (cnt X 1 0 : ℚ)) =
      3960 * (cnt X 1 0 : ℚ) * (R45.M3E.divE.map α).sum := by
    rw [divE_sum, ← sum_mul, mul_comm]
  rw [e1, e2]
  have hc : (0 : ℚ) ≤ 3960 * (cnt X 1 0 : ℚ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hαs hc)

theorem parOf_ymax (t : List ℚ) (n : List ℕ) : ymaxQ (PE.parOf t 8 0) n = 8 * PE.kap * dotNQ n t := rfl

/-- The algebra of the minorant (all quantities abstracted). -/
theorem mino_alg {nrm E k R sN Qn Ym φv J : ℚ} (hn : 0 ≤ nrm) (hE : 0 < E) (hs : 0 < sN) (hJ : 1 ≤ J)
    (hφ : (2 * J + 1 - (1 + Ym / sN)) / (J * (J + 1)) ≤ φv)
    (hYb : Ym ≤ 8 * k * (Qn / 2 ^ 36 + 3960 * sN * R)) :
    nrm / E / (J * (J + 1)) * ((2 * J - 8 * k * 3960 * R) * sN - 8 * k * Qn / 2 ^ 36) ≤
      nrm * (1 / E) * sN * φv + 1 / E * 0 * Ym := by
  have hJJ : 0 < J * (J + 1) := by nlinarith
  have hc : 0 ≤ nrm / E / (J * (J + 1)) := div_nonneg (div_nonneg hn hE.le) hJJ.le
  have hA : (2 * J - 8 * k * 3960 * R) * sN - 8 * k * Qn / 2 ^ 36 ≤ 2 * J * sN - Ym := by
    have e : 8 * k * (Qn / 2 ^ 36 + 3960 * sN * R) = 8 * k * Qn / 2 ^ 36 + 8 * k * 3960 * R * sN := by ring
    nlinarith [hYb, e]
  have hB : nrm / E / (J * (J + 1)) * (2 * J * sN - Ym) =
      nrm * (1 / E) * sN * ((2 * J + 1 - (1 + Ym / sN)) / (J * (J + 1))) := by
    field_simp
    ring
  have hC : nrm * (1 / E) * sN * ((2 * J + 1 - (1 + Ym / sN)) / (J * (J + 1))) ≤ nrm * (1 / E) * sN * φv :=
    mul_le_mul_of_nonneg_left hφ (mul_nonneg (mul_nonneg hn (by positivity)) hs.le)
  calc nrm / E / (J * (J + 1)) * ((2 * J - 8 * k * 3960 * R) * sN - 8 * k * Qn / 2 ^ 36)
      ≤ nrm / E / (J * (J + 1)) * (2 * J * sN - Ym) := mul_le_mul_of_nonneg_left hA hc
    _ = nrm * (1 / E) * sN * ((2 * J + 1 - (1 + Ym / sN)) / (J * (J + 1))) := hB
    _ ≤ nrm * (1 / E) * sN * φv := hC
    _ = nrm * (1 / E) * sN * φv + 1 / E * 0 * Ym := by ring

/-- The minorant of one row. -/
theorem mino (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3E.divE.map α).sum ≤ M3E.R0tLit + delta)
    (X J : ℕ) (hJ : 1 ≤ J) :
    vt J (cnt X 1 0) (Qs X) ≤ phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960 X := by
  have hmu : (PE.parOf (teffA (tabB BLit) α) 8 0).mu = 0 := rfl
  by_cases hs : cnt X 1 0 = 0
  · rw [hs, Qs_zero_of X hs, vt_zero]
    unfold phiCls
    split_ifs
    · exact le_refl _
    · rw [popcount_fx, hs, minQ_zero_s _ hmu]
  · have hs0 : 0 < cnt X 1 0 := Nat.pos_of_ne_zero hs
    have hu : full 3960 ^^^ X ≠ 0 := by
      intro h0
      have : popcount 3960 (full 3960 ^^^ X) = 0 := by rw [h0]; simp [popcount_eq]
      rw [popcount_fx] at this; exact hs this
    unfold phiCls
    rw [if_neg hu, popcount_fx]
    have hnl : (nShift 3960 (full 3960 ^^^ X)).length = 3960 := nShift_length _ _
    have hY : ymaxQ (PE.parOf (teffA (tabB BLit) α) 8 0) (nShift 3960 (full 3960 ^^^ X)) = 8 * PE.kap *
        (R45.M3E.divE.map fun g => (BLit g + (g : ℚ) * α g) * (S X g : ℚ)).sum := by
      rw [parOf_ymax, dotNQ_teffA_tabB _ hnl BLit α]
      refine congrArg (fun t => 8 * PE.kap * t) (congrArg List.sum (List.map_congr_left ?_))
      intro g hg
      rw [ngOf_nShift X (divE_dvd hg) (divE_pos hg)]
    have hdot0 : (0 : ℚ) ≤ (R45.M3E.divE.map fun g => (BLit g + (g : ℚ) * α g) * (S X g : ℚ)).sum := by
      rw [divE_sum]
      apply sum_nonneg
      intro i hi
      have hb := (bn_ok i (mem_range.mp hi)).1
      have : (0 : ℚ) ≤ BLit (dA.getD i 0) + (dA.getD i 0 : ℚ) * α (dA.getD i 0) :=
        add_nonneg hb (mul_nonneg (Nat.cast_nonneg _) (hα _))
      exact mul_nonneg this (Nat.cast_nonneg _)
    have hY0 : 0 ≤ ymaxQ (PE.parOf (teffA (tabB BLit) α) 8 0) (nShift 3960 (full 3960 ^^^ X)) := by
      rw [hY]; exact mul_nonneg (mul_nonneg (by norm_num) kapE_nonneg) hdot0
    rw [minQ_mu0 _ hmu normE_nonneg hs0 hY0]
    have hYb : ymaxQ (PE.parOf (teffA (tabB BLit) α) 8 0) (nShift 3960 (full 3960 ^^^ X)) ≤
        8 * PE.kap * ((Qs X : ℚ) / 2 ^ 36 + 3960 * (cnt X 1 0 : ℚ) * (M3E.R0tLit + delta)) := by
      rw [hY]
      exact mul_le_mul_of_nonneg_left (dot_bound α hα hαs X) (mul_nonneg (by norm_num) kapE_nonneg)
    have hs' : (0 : ℚ) < (cnt X 1 0 : ℚ) := by exact_mod_cast hs0
    have hD1 : (1 : ℚ) ≤ 1 + ymaxQ (PE.parOf (teffA (tabB BLit) α) 8 0) (nShift 3960 (full 3960 ^^^ X)) /
        (cnt X 1 0 : ℚ) := by
      have := div_nonneg hY0 hs'.le; linarith
    have hφ := lin_le_phiQ hJ hD1
    unfold gQ vt cJ K0
    rw [hmu]
    generalize ymaxQ (PE.parOf (teffA (tabB BLit) α) 8 0) (nShift 3960 (full 3960 ^^^ X)) = Ym at hφ hYb ⊢
    generalize phiQ (1 + Ym / (cnt X 1 0 : ℚ)) = φv at hφ ⊢
    generalize (cnt X 1 0 : ℚ) = sN at hφ hYb hs' ⊢
    generalize (Qs X : ℚ) = Qn at hYb ⊢
    have hJ' : (1 : ℚ) ≤ (J : ℚ) := by exact_mod_cast hJ
    exact mino_alg normE_nonneg ellE_pos hs' hJ' hφ hYb

end Romanoff.E.S2
