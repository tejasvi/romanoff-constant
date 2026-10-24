import Romanoff.M4A
import Romanoff.Log2

/-!
# M4 assembly at one `N`

`A_N = N/(120 φ(l) log 2)`, `K = {k < l : U_k ≠ ∅}`, `Ỹ_k = XU_k/((1-η) A_N)`.
* `count_bound`: Pintz per class with `D_k = 1 + Ỹ_k/|U_k|` (valid because `S2 = S1 + XU` and `S1 ≥ (1-η)|U_k| A_N`) gives
  `count N ≥ (1-η) A_N Σ_{k ∈ K} |U_k| φ(1 + Ỹ_k/|U_k|)`.
-/

open Finset

namespace Romanoff

/-- `A_N = N/(120 φ(l) log 2)`. -/
noncomputable def AN (N : ℕ) : ℝ := (N : ℝ) / (120 * Nat.totient ell * Real.log 2)

/-- The classes with `U_k ≠ ∅`. -/
def Kset : Finset ℕ := (range ell).filter fun k => (Uset 120 ellPrimes k).Nonempty

/-- The normalized pair mass `Ỹ_k = XU_k/((1-η) A_N)`. -/
noncomputable def Yt (η : ℝ) (N k : ℕ) : ℝ := (XU ell N k : ℝ) / ((1 - η) * AN N)

theorem ell_pos : 0 < ell := prod_pos_of_primes ellPrimes distinctPrimes_ell.2

theorem totient_ell_pos : (0 : ℝ) < Nat.totient ell := Nat.cast_pos.mpr (Nat.totient_pos.mpr ell_pos)

theorem Kset_subset : Kset ⊆ range ell := filter_subset _ _

theorem AN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < AN N := by
  unfold AN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos hN0 (mul_pos (mul_pos (by norm_num) totient_ell_pos) hlog)

theorem XU_eq (N k : ℕ) : S2 ell N k = S1 ell N k + XU ell N k := S2_eq ell N k

theorem count_bound {η : ℝ} (hη1 : η < 1) {N : ℕ} (hN : 1 ≤ N)
    (hFM : ∀ k < ell, (Uset 120 ellPrimes k).Nonempty →
      (1 - η) * (Uset 120 ellPrimes k).card * AN N ≤ S1 ell N k) :
    (1 - η) * AN N * ∑ k ∈ Kset, ((Uset 120 ellPrimes k).card : ℝ) *
      phi (1 + Yt η N k / (Uset 120 ellPrimes k).card) ≤ count N := by
  have hA := AN_pos hN
  have hη0 : 0 < 1 - η := by linarith
  rw [count_eq_sum ell N ell_pos, mul_sum]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg Kset_subset fun _ _ _ => Nat.cast_nonneg _)
  refine sum_le_sum fun k hk => ?_
  obtain ⟨hkl, hne⟩ := mem_filter.mp hk
  set s : ℝ := ((Uset 120 ellPrimes k).card : ℝ) with hs
  have hs1 : (1 : ℝ) ≤ s := by rw [hs]; exact_mod_cast hne.card_pos
  have hs0 : (0 : ℝ) < s := by linarith
  have hXU : (0 : ℝ) ≤ XU ell N k := Nat.cast_nonneg _
  have hY0 : 0 ≤ Yt η N k := div_nonneg hXU (by positivity)
  set D := 1 + Yt η N k / s with hD
  have hD1 : 1 ≤ D := by have := div_nonneg hY0 hs0.le; linarith
  have hS1 := hFM k (mem_range.mp hkl) hne
  -- `S2 ≤ D S1`
  have h2 : (S2 ell N k : ℝ) ≤ D * S1 ell N k := by
    rw [XU_eq, Nat.cast_add, hD, add_mul, one_mul]
    have hc : (0 : ℝ) < (1 - η) * AN N * s := by positivity
    have : (XU ell N k : ℝ) ≤ Yt η N k / s * S1 ell N k := by
      unfold Yt
      rw [div_div, show (1 - η) * AN N * s = (1 - η) * s * AN N by ring, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (by linarith [hS1]) hXU
    linarith
  have hcc := class_count_ge ell N k hD1 h2
  have hphi := phi_nonneg hD1
  calc (1 - η) * AN N * (s * phi D) = phi D * ((1 - η) * s * AN N) := by ring
    _ ≤ phi D * S1 ell N k := mul_le_mul_of_nonneg_left (by linarith [hS1]) hphi
    _ ≤ _ := hcc

/-! ## The per-class caps at one `N` -/

/-- `κ` of the evaluator, as a real number. -/
noncomputable def kapR : ℝ := ((R45.P45.kap : ℚ) : ℝ)

/-- `λ_N = (1 + ε/8)(1 + 120/L)/(1 - η)`. -/
noncomputable def lamC (η ε : ℝ) (L : ℕ) : ℝ := (1 + ε / 8) * (1 + 120 / (L : ℝ)) / (1 - η)

/-- `ν_N`: the pairs outside `U_k²` and the `E(L)` part of the singular series. -/
noncomputable def nuC (η ε : ℝ) (N : ℕ) : ℝ :=
  (9 * (Nat.log 2 N : ℝ) ^ 2 * (120 * Nat.totient ell * Real.log 2) / N +
    (8 + ε) * C0up * Pl ellPrimes * 120 * Real.log 2 * ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 *
      EL ell (Nat.log 2 N) / Real.log N ^ 2) / (1 - η)

theorem kapR_eq (hD : DataFacts) :
    kapR = C0up * Pl ellPrimes / (120 * (693147180559945309 / 10 ^ 18)) := by
  obtain ⟨_, _, hpell, hC0, hlo, _⟩ := hD
  unfold kapR R45.P45.kap
  push_cast
  rw [hC0, hpell, hlo, show ((R45.P45.per : ℕ) : ℝ) = (120 : ℝ) by simp [R45.P45.per]]

theorem TK_nonneg {teff : List ℚ} (hT : TBound teff) (k : ℕ) : 0 ≤ TK teff k := by
  unfold TK
  refine sum_nonneg fun c hc => mul_nonneg (Nat.cast_nonneg _) ?_
  have := hT.2 c (mem_range.mp hc) ∅ (by simp)
  simpa using this

theorem EL_nonneg (l L : ℕ) : 0 ≤ EL l L := sum_nonneg fun m _ => fm_nonneg m

theorem Pl_pos : 0 < Pl ellPrimes := by
  unfold Pl
  refine prod_pos fun p hp => ?_
  have h2 : 2 < p := lt_of_le_of_ne (distinctPrimes_ell.2 p (List.mem_toFinset.mp hp)).two_le
    (fun e => (goodPrimes_ell p (List.mem_toFinset.mp hp)).2.1 e.symm)
  have : (2 : ℝ) < p := by exact_mod_cast h2
  exact div_pos (by linarith) (by linarith)

theorem C0up_pos : (0 : ℝ) < C0up := by unfold C0up; norm_num

theorem card_Uset_le (k : ℕ) : ((Uset 120 ellPrimes k).card : ℝ) ≤ 120 := by
  have := card_le_card (filter_subset (fun e => ∀ p ∈ ellPrimes, 2 ^ e % p ≠ k % p) (range 120))
  rw [card_range] at this
  exact_mod_cast this

theorem log_ge_L {N : ℕ} (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h2L : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast h2L
  calc (Nat.log 2 N : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 N) := by rw [Real.log_pow]
    _ ≤ Real.log N := Real.log_le_log (by positivity) (by exact_mod_cast this)

theorem coef_le {Lr l2 l2lo lN : ℝ} (hLr : 1 ≤ Lr) (hlo0 : 0 < l2lo) (hlo : l2lo ≤ l2) (hlN : Lr * l2 ≤ lN) :
    120 * l2 * ((Lr / 120 + 1) * (Lr / 120)) / lN ^ 2 ≤ (1 + 120 / Lr) / (120 * l2lo) := by
  have hl2 : 0 < l2 := lt_of_lt_of_le hlo0 hlo
  have hLl : 0 < Lr * l2 := by positivity
  have h1 : 120 * l2 * ((Lr / 120 + 1) * (Lr / 120)) / lN ^ 2 ≤
      120 * l2 * ((Lr / 120 + 1) * (Lr / 120)) / (Lr * l2) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hLl.le hlN 2)
  have h2 : 120 * l2 * ((Lr / 120 + 1) * (Lr / 120)) / (Lr * l2) ^ 2 = (1 + 120 / Lr) / (120 * l2) := by
    field_simp
  have h3 : (1 + 120 / Lr) / (120 * l2) ≤ (1 + 120 / Lr) / (120 * l2lo) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

/-- The algebra of the per-class cap (plain real variables). -/
theorem cap_alg {XU TK EL Pl C0 φ l2 l2lo lN Lr N η ε kap : ℝ} (hη : 0 < 1 - η) (hε : 0 < ε) (hTK : 0 ≤ TK)
    (hPl : 0 < Pl) (hC0 : 0 < C0) (hφ : 0 < φ) (hl2lo : 0 < l2lo) (hlo : l2lo ≤ l2) (hN : 0 < N)
    (hLr : 1 ≤ Lr) (hlN : Lr * l2 ≤ lN) (hkap : kap = C0 * Pl / (120 * l2lo))
    (hXU : XU ≤ 9 * Lr ^ 2 + (8 + ε) * C0 * N / (φ * lN ^ 2) * Pl * ((Lr / 120 + 1) * (Lr / 120) * TK) +
      (8 + ε) * C0 * N / (φ * lN ^ 2) * Pl * ((Lr / 120 + 1) * 14400 * EL)) :
    XU / ((1 - η) * (N / (120 * φ * l2))) ≤ (1 + ε / 8) * (1 + 120 / Lr) / (1 - η) * (8 * kap * TK) +
      (9 * Lr ^ 2 * (120 * φ * l2) / N + (8 + ε) * C0 * Pl * 120 * l2 * (Lr / 120 + 1) * 14400 * EL / lN ^ 2) /
        (1 - η) := by
  have hl2 : 0 < l2 := lt_of_lt_of_le hl2lo hlo
  have hlN0 : 0 < lN := lt_of_lt_of_le (by positivity) hlN
  have hA : 0 < (1 - η) * (N / (120 * φ * l2)) := by positivity
  have hdiv := div_le_div_of_nonneg_right hXU hA.le
  have hc := coef_le hLr hl2lo hlo hlN
  have e1 : (9 * Lr ^ 2 + (8 + ε) * C0 * N / (φ * lN ^ 2) * Pl * ((Lr / 120 + 1) * (Lr / 120) * TK) +
      (8 + ε) * C0 * N / (φ * lN ^ 2) * Pl * ((Lr / 120 + 1) * 14400 * EL)) / ((1 - η) * (N / (120 * φ * l2))) =
      (8 + ε) * C0 * Pl * TK / (1 - η) * (120 * l2 * ((Lr / 120 + 1) * (Lr / 120)) / lN ^ 2) +
      (9 * Lr ^ 2 * (120 * φ * l2) / N + (8 + ε) * C0 * Pl * 120 * l2 * (Lr / 120 + 1) * 14400 * EL / lN ^ 2) /
        (1 - η) := by
    field_simp; ring
  have e2 : (1 + ε / 8) * (1 + 120 / Lr) / (1 - η) * (8 * kap * TK) =
      (8 + ε) * C0 * Pl * TK / (1 - η) * ((1 + 120 / Lr) / (120 * l2lo)) := by
    rw [hkap]; field_simp
  rw [e1] at hdiv
  rw [e2]
  have := mul_le_mul_of_nonneg_left hc (show 0 ≤ (8 + ε) * C0 * Pl * TK / (1 - η) by positivity)
  linarith

/-- The per-class cap at one `N`: `Ỹ_k ≤ λ_N · 8 κ T_k + ν_N` (ESP (28) at `N`). -/
theorem cap_bound (hB1 : XUESPBound) (hD : DataFacts) {teff : List ℚ} (hT : TBound teff)
    {η ε : ℝ} (hη1 : η < 1) (hε : 0 < ε) {N : ℕ} (hN2 : 2 ≤ N)
    (hESP : ∀ h : ℤ, 0 < h → h < N → ∀ k : ℕ, Nat.Coprime k ell →
      (pairCountMod N h k ell : ℝ) ≤
        (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * sing (ell * h.natAbs))
    {k : ℕ} (hk : k ∈ Kset) :
    Yt η N k ≤ lamC η ε (Nat.log 2 N) * (8 * kapR * TK teff k) + nuC η ε N := by
  have hkl : k < ell := mem_range.mp (mem_filter.mp hk).1
  have hL1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN2)
  have hLr1 : (1 : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hTK := TK_nonneg hT k
  have hEL := EL_nonneg ell (Nat.log 2 N)
  have hX := hB1 N ε hε hESP k hkl
  have hW := wuBound teff hT (Nat.log 2 N) k
  have hs2 : ((Uset 120 ellPrimes k).card : ℝ) ^ 2 ≤ 14400 := by
    have h0 : (0 : ℝ) ≤ (Uset 120 ellPrimes k).card := Nat.cast_nonneg _
    have := card_Uset_le k
    nlinarith
  have hE0 : 0 ≤ (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * Pl ellPrimes := by
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by linarith) C0up_pos.le) hN0.le)
      (mul_nonneg totient_ell_pos.le (sq_nonneg _))) Pl_pos.le
  have hW' : WU (Nat.log 2 N) k ≤ ((Nat.log 2 N : ℝ) / 120 + 1) * ((Nat.log 2 N : ℝ) / 120) * TK teff k +
      ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N) := by
    refine hW.trans ?_
    have : ((Nat.log 2 N : ℝ) / 120 + 1) * ((Uset 120 ellPrimes k).card : ℝ) ^ 2 * EL ell (Nat.log 2 N) ≤
        ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by positivity)) hEL
    linarith
  have hXU : (XU ell N k : ℝ) ≤ 9 * (Nat.log 2 N : ℝ) ^ 2 +
      (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * Pl ellPrimes *
        (((Nat.log 2 N : ℝ) / 120 + 1) * ((Nat.log 2 N : ℝ) / 120) * TK teff k) +
      (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * Pl ellPrimes *
        (((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N)) := by
    have := mul_le_mul_of_nonneg_left hW' hE0
    linarith
  have := cap_alg (XU := (XU ell N k : ℝ)) (η := η) (ε := ε) (l2lo := 693147180559945309 / 10 ^ 18) (by linarith) hε
    hTK Pl_pos
    C0up_pos totient_ell_pos (by norm_num) log_two_bounds.1.le hN0 hLr1 (log_ge_L (by omega)) (kapR_eq hD) hXU
  unfold Yt lamC nuC AN
  exact this

/-! ## The budget at one `N` (JT Prop. 2) -/

/-- `C1 = 6.7814` (JT Prop. 2). -/
noncomputable def C1R : ℝ := 67814 / 10000

/-- `λ'_N = (1 + ε/C1)(1 + 120/L)/(1 - η)`. -/
noncomputable def lamB (η ε : ℝ) (L : ℕ) : ℝ := (1 + ε / C1R) * (1 + 120 / (L : ℝ)) / (1 - η)

/-- `ν'_N`: the `E(L)` part of the singular series in the budget. -/
noncomputable def nuB (η ε : ℝ) (N : ℕ) : ℝ :=
  (C1R + ε) * C0up * Pl ellPrimes * 120 * Real.log 2 * ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 *
    EL ell (Nat.log 2 N) / ((1 - η) * Real.log N ^ 2)

/-- The budget of the evaluator in class form: `C1 κ (1/l) Σ_{k < l} T_k`. -/
noncomputable def Beval (teff : List ℚ) : ℝ := C1R * kapR * ((1 / (ell : ℝ)) * ∑ k ∈ range ell, TK teff k)

theorem phi_mul_prod (hD : DataFacts) :
    (Nat.totient ell : ℝ) * ∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2) = Pl ellPrimes := by
  obtain ⟨_, hphil, _⟩ := hD
  rw [← hphil]
  unfold Pl R45.P45.philN
  rw [List.prod_toFinset _ distinctPrimes_ell.1, List.prod_toFinset _ distinctPrimes_ell.1]
  simp [ellPrimes, R45.D45.ellPO]
  norm_num

/-- The algebra of the budget (plain real variables). -/
theorem budget_alg {SX ST EL Pl C0 Q φ l2 l2lo lN Lr N η ε kap ellr C1 : ℝ} (hη : 0 < 1 - η) (hε : 0 < ε)
    (hC1 : 0 < C1) (hST : 0 ≤ ST) (hPl : 0 < Pl) (hC0 : 0 < C0) (hφ : 0 < φ) (hl2lo : 0 < l2lo) (hlo : l2lo ≤ l2)
    (hN : 0 < N) (hLr : 1 ≤ Lr) (hlN : Lr * l2 ≤ lN) (hkap : kap = C0 * Pl / (120 * l2lo)) (hellr : 0 < ellr)
    (hφQ : φ * Q = Pl)
    (hSX : SX ≤ (C1 + ε) * C0 * N / lN ^ 2 * Q *
      ((Lr / 120 + 1) * (Lr / 120) * ST + (Lr / 120 + 1) * 14400 * EL * ellr)) :
    1 / ellr * (SX / ((1 - η) * (N / (120 * φ * l2)))) ≤
      (1 + ε / C1) * (1 + 120 / Lr) / (1 - η) * (C1 * kap * (1 / ellr * ST)) +
      (C1 + ε) * C0 * Pl * 120 * l2 * (Lr / 120 + 1) * 14400 * EL / ((1 - η) * lN ^ 2) := by
  have hl2 : 0 < l2 := lt_of_lt_of_le hl2lo hlo
  have hlN0 : 0 < lN := lt_of_lt_of_le (by positivity) hlN
  have hA : 0 < (1 - η) * (N / (120 * φ * l2)) := by positivity
  have hdiv := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSX hA.le) (by positivity : (0 : ℝ) ≤ 1 / ellr)
  have hc := coef_le hLr hl2lo hlo hlN
  have hQ : Q = Pl / φ := by rw [← hφQ]; field_simp
  have e1 : 1 / ellr * ((C1 + ε) * C0 * N / lN ^ 2 * Q *
      ((Lr / 120 + 1) * (Lr / 120) * ST + (Lr / 120 + 1) * 14400 * EL * ellr) / ((1 - η) * (N / (120 * φ * l2)))) =
      (C1 + ε) * C0 * Pl * (1 / ellr * ST) / (1 - η) * (120 * l2 * ((Lr / 120 + 1) * (Lr / 120)) / lN ^ 2) +
      (C1 + ε) * C0 * Pl * 120 * l2 * (Lr / 120 + 1) * 14400 * EL / ((1 - η) * lN ^ 2) := by
    rw [hQ]; field_simp
  have e2 : (1 + ε / C1) * (1 + 120 / Lr) / (1 - η) * (C1 * kap * (1 / ellr * ST)) =
      (C1 + ε) * C0 * Pl * (1 / ellr * ST) / (1 - η) * ((1 + 120 / Lr) / (120 * l2lo)) := by
    rw [hkap]; field_simp
  rw [e1] at hdiv
  rw [e2]
  have := mul_le_mul_of_nonneg_left hc (show 0 ≤ (C1 + ε) * C0 * Pl * (1 / ellr * ST) / (1 - η) by positivity)
  linarith

theorem Yt_nonneg {η : ℝ} (hη1 : η < 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 0 ≤ Yt η N k :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) (AN_pos hN).le)

/-- The budget at one `N`: `(1/l) Σ_{k ∈ K} Ỹ_k ≤ λ'_N B + ν'_N` (JT Prop. 2 at `N`). -/
theorem budget_bound (hB2 : SumXUJTBound) (hD : DataFacts) {teff : List ℚ} (hT : TBound teff)
    {η ε : ℝ} (hη1 : η < 1) (hε : 0 < ε) {N : ℕ} (hN2 : 2 ≤ N)
    (hJT : ∀ h : ℤ, 0 < h → h < N →
      (pairCount N h : ℝ) ≤ (67814 / 10000 + ε) * C0up * N / Real.log N ^ 2 * sing h.natAbs) :
    1 / (ell : ℝ) * ∑ k ∈ Kset, Yt η N k ≤ lamB η ε (Nat.log 2 N) * Beval teff + nuB η ε N := by
  have hL1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN2)
  have hLr1 : (1 : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hell : (0 : ℝ) < ell := by exact_mod_cast ell_pos
  have hEL := EL_nonneg ell (Nat.log 2 N)
  -- `Σ_K Ỹ ≤ Σ_{k < l} Ỹ = (Σ XU)/((1-η) A_N)`
  have h1 : ∑ k ∈ Kset, Yt η N k ≤ (∑ k ∈ range ell, (XU ell N k : ℝ)) / ((1 - η) * AN N) := by
    rw [sum_div]
    exact sum_le_sum_of_subset_of_nonneg Kset_subset fun k _ _ => Yt_nonneg hη1 (by omega) k
  -- `Σ_k WU_k`
  have hW : ∑ k ∈ range ell, WU (Nat.log 2 N) k ≤
      ((Nat.log 2 N : ℝ) / 120 + 1) * ((Nat.log 2 N : ℝ) / 120) * ∑ k ∈ range ell, TK teff k +
        ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N) * ell := by
    have e : ∀ k ∈ range ell, WU (Nat.log 2 N) k ≤
        ((Nat.log 2 N : ℝ) / 120 + 1) * ((Nat.log 2 N : ℝ) / 120) * TK teff k +
          ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N) := by
      intro k _
      have hs2 : ((Uset 120 ellPrimes k).card : ℝ) ^ 2 ≤ 14400 := by
        have h0 : (0 : ℝ) ≤ (Uset 120 ellPrimes k).card := Nat.cast_nonneg _
        have := card_Uset_le k
        nlinarith
      refine (wuBound teff hT (Nat.log 2 N) k).trans ?_
      have : ((Nat.log 2 N : ℝ) / 120 + 1) * ((Uset 120 ellPrimes k).card : ℝ) ^ 2 * EL ell (Nat.log 2 N) ≤
          ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by positivity)) hEL
      linarith
    refine (sum_le_sum e).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    ring
  have hJ0 : 0 ≤ (67814 / 10000 + ε) * C0up * N / Real.log N ^ 2 * ∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2) := by
    refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by linarith) C0up_pos.le) hN0.le) (sq_nonneg _))
      (prod_nonneg fun p hp => ?_)
    have h2 : 2 < p := lt_of_le_of_ne (distinctPrimes_ell.2 p (List.mem_toFinset.mp hp)).two_le
      (fun e => (goodPrimes_ell p (List.mem_toFinset.mp hp)).2.1 e.symm)
    have : (2 : ℝ) < p := by exact_mod_cast h2
    exact one_div_nonneg.mpr (by linarith)
  have hSX : (∑ k ∈ range ell, (XU ell N k : ℝ)) ≤ (C1R + ε) * C0up * N / Real.log N ^ 2 *
      (∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) *
        (((Nat.log 2 N : ℝ) / 120 + 1) * ((Nat.log 2 N : ℝ) / 120) * ∑ k ∈ range ell, TK teff k +
          ((Nat.log 2 N : ℝ) / 120 + 1) * 14400 * EL ell (Nat.log 2 N) * ell) :=
    (hB2 N ε hε hJT).trans (mul_le_mul_of_nonneg_left hW hJ0)
  have hST : 0 ≤ ∑ k ∈ range ell, TK teff k := sum_nonneg fun k _ => TK_nonneg hT k
  have := budget_alg (SX := ∑ k ∈ range ell, (XU ell N k : ℝ)) (η := η) (ε := ε) (C1 := C1R)
    (l2lo := 693147180559945309 / 10 ^ 18) (by linarith) hε (by unfold C1R; norm_num) hST Pl_pos C0up_pos
    totient_ell_pos (by norm_num) log_two_bounds.1.le hN0 hLr1 (log_ge_L (by omega)) (kapR_eq hD) hell
    (phi_mul_prod hD) hSX
  have hmono := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (ell : ℝ))
  unfold lamB nuB Beval
  unfold AN at hmono
  linarith

end Romanoff
