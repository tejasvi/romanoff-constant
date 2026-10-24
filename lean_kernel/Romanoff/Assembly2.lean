import Romanoff.Assembly
import RCert.Cert45

/-!
# M4 assembly: the density at one `N` against the evaluator

With `P = parOf teff c1 mu` (the evaluator's parameters), `count_bound`, the per-class caps (`cap_bound`) and the
Lagrangian bound with perturbed caps (`lagrangian_perturbed`) give, for any budget bound `B` of `(1/l) Σ_K Ỹ_k`,
`dens N ≥ (1-η) (orbSum P - μ B - Y (λ_N - 1) - norm ν_N / 2)`, where `Y = (norm/l) Σ_K 8 κ T_k / 2`; the factor
`A_N l/(norm N) = log2hi/log 2 ≥ 1` is dropped.
-/

open Finset R45 R45.P45

namespace Romanoff

/-- `norm` of the evaluator, as a real number. -/
noncomputable def normR : ℝ := ((R45.P45.norm : ℚ) : ℝ)

/-- `Y = (norm/l) Σ_{k ∈ K} 8 κ T_k / 2` (the total of the caps, weighted as in the evaluator). -/
noncomputable def Ycon (teff : List ℚ) : ℝ := normR / ell * ∑ k ∈ Kset, 8 * kapR * TK teff k / 2

theorem parOf_ell (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).ell = ellN := rfl
theorem parOf_norm (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).norm = R45.P45.norm := rfl
theorem parOf_mu (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).mu = mu := rfl
theorem parOf_teff (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).teff = teff := rfl
theorem parOf_cap (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).cap = 8 := rfl
theorem parOf_kap (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).kap = kap := rfl
theorem parOf_c1 (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).c1 = c1 := rfl
theorem parOf_per (teff : List ℚ) (c1 mu : ℚ) : (parOf teff c1 mu).per = 120 := rfl

theorem normR_eq (hD : DataFacts) :
    normR = (ell : ℝ) / Nat.totient ell / (120 * (693147180559945310 / 10 ^ 18)) := by
  obtain ⟨hellN, hphil, _, _, _, hhi⟩ := hD
  unfold normR R45.P45.norm
  push_cast
  rw [hhi, hellN, hphil, show ((R45.P45.per : ℕ) : ℝ) = (120 : ℝ) by simp [R45.P45.per]]

theorem normR_pos (hD : DataFacts) : 0 < normR := by
  rw [normR_eq hD]
  have : (0 : ℝ) < ell := by exact_mod_cast ell_pos
  exact div_pos (div_pos this totient_ell_pos) (by norm_num)

theorem kapR_nonneg (hD : DataFacts) : 0 ≤ kapR := by
  rw [kapR_eq hD]; exact div_nonneg (mul_nonneg C0up_pos.le Pl_pos.le) (by norm_num)

theorem ymax_cast (teff : List ℚ) (c1 mu : ℚ) (k : ℕ) :
    (((parOf teff c1 mu).cap * (parOf teff c1 mu).kap *
      ∑ c ∈ range 120, (nC 120 ellPrimes k c : ℚ) * (parOf teff c1 mu).teff.getD c 0 : ℚ) : ℝ) =
      8 * kapR * TK teff k := by
  rw [parOf_cap, parOf_kap, parOf_teff]
  unfold kapR TK
  push_cast
  ring

theorem lamC_ge_one {η ε : ℝ} (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε) (L : ℕ) : 1 ≤ lamC η ε L := by
  unfold lamC
  rw [le_div_iff₀ (by linarith)]
  have h1 : 0 ≤ 120 / (L : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  nlinarith

theorem nuC_nonneg {η ε : ℝ} (hη1 : η < 1) (hε : 0 < ε) (N : ℕ) : 0 ≤ nuC η ε N := by
  unfold nuC
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLp : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) / 120 + 1 := by positivity
  refine div_nonneg (add_nonneg (div_nonneg ?_ (Nat.cast_nonneg _)) (div_nonneg ?_ (sq_nonneg _))) (by linarith)
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) totient_ell_pos.le) hl2)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith)
      C0up_pos.le) Pl_pos.le) (by norm_num)) hl2) hLp) (by norm_num)) (EL_nonneg _ _)

theorem card_Kset_le : (Kset.card : ℝ) ≤ ell := by
  have := card_le_card Kset_subset
  rw [card_range] at this
  exact_mod_cast this

theorem ratio_alg {N φ l2 h E : ℝ} (hN : 0 < N) (hφ : 0 < φ) (hl2 : 0 < l2) (hh : 0 < h) (hE : 0 < E) :
    N / (120 * φ * l2) * (E / (E / φ / (120 * h))) / N = h / l2 := by
  field_simp

theorem scale_alg {a A E n S : ℝ} (hE : E ≠ 0) (hn : n ≠ 0) : a * A * (E / n) * (n / E * S) = a * A * S := by
  field_simp

theorem dens_alg {a Q X N : ℝ} (hN : N ≠ 0) : a * (Q / N) * X * N = a * Q * X := by
  field_simp

/-- The density at one `N`. -/
theorem dens_lower_at (hB1 : XUESPBound) (hC1 : OrbSumLink) (hD : DataFacts)
    {teff : List ℚ} (hT : TBound teff) (c1 mu : ℚ) (hmu : (0 : ℝ) ≤ mu)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε) {N : ℕ} (hN2 : 2 ≤ N)
    (hFM : ∀ k < ell, (Uset 120 ellPrimes k).Nonempty →
      (1 - η) * (Uset 120 ellPrimes k).card * AN N ≤ S1 ell N k)
    (hESP : ∀ h : ℤ, 0 < h → h < N → ∀ k : ℕ, Nat.Coprime k ell →
      (pairCountMod N h k ell : ℝ) ≤
        (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * sing (ell * h.natAbs))
    (B : ℝ) (hbud : 1 / (ell : ℝ) * ∑ k ∈ Kset, Yt η N k ≤ B) :
    (1 - η) * (((orbSum (parOf teff c1 mu) (orbits 120 ellPrimes) : ℚ) : ℝ) - mu * B - Ycon teff * (lamC η ε (Nat.log 2 N) - 1) -
      normR * nuC η ε N / 2) ≤ dens N := by
  have hN1 : 1 ≤ N := by omega
  have hA := AN_pos hN1
  have hη0 : 0 < 1 - η := by linarith
  have hellR : (0 : ℝ) < ell := by exact_mod_cast ell_pos
  have hPell : (((parOf teff c1 mu).ell : ℕ) : ℝ) = ell := by rw [parOf_ell]; exact_mod_cast hD.1
  have hnormR := normR_pos hD
  have hPnorm : (((parOf teff c1 mu).norm : ℚ) : ℝ) = normR := by rw [parOf_norm]; rfl
  have hPmu : (((parOf teff c1 mu).mu : ℚ) : ℝ) = mu := by rw [parOf_mu]
  -- (1) Pintz per class
  have hcount := count_bound hη1 hN1 hFM
  -- (2) the Lagrangian bound with perturbed caps
  have hlag := lagrangian_perturbed Kset (parOf teff c1 mu) (fun k => (Uset 120 ellPrimes k).card) (Yt η N)
    (fun k => (parOf teff c1 mu).cap * (parOf teff c1 mu).kap * ∑ c ∈ range 120, (nC 120 ellPrimes k c : ℚ) * (parOf teff c1 mu).teff.getD c 0)
    (lamC η ε (Nat.log 2 N)) (nuC η ε N) B (lamC_ge_one hη hη1 hε _) (nuC_nonneg hη1 hε N)
    (fun k hk => (mem_filter.mp hk).2.card_pos) (fun k _ => Yt_nonneg hη1 hN1 k)
    (fun k _ => by
      have h := ymax_cast teff c1 mu k
      have h0 : (0 : ℝ) ≤ 8 * kapR * TK teff k := mul_nonneg (mul_nonneg (by norm_num) (kapR_nonneg hD)) (TK_nonneg hT k)
      rw [← h] at h0
      exact_mod_cast h0)
    (by rw [hPmu]; exact hmu) (by rw [hPnorm]; exact hnormR.le) (by rw [hPell]; exact hellR)
    (fun k hk => by
      have h := cap_bound hB1 hD hT hη1 hε hN2 hESP hk
      rw [ymax_cast teff c1 mu k]
      exact h)
    (by rw [hPell]; exact hbud)
  -- (3) the orbit sum is the sum of the minima over `K`
  have horb := hC1 (parOf teff c1 mu) (by rw [parOf_teff]; exact hT.1)
  rw [hPell, hPnorm, hPmu] at hlag
  simp only [ymax_cast teff c1 mu] at hlag
  have horb' : ((orbSum (parOf teff c1 mu) (orbits 120 ellPrimes) : ℚ) : ℝ) =
      ∑ k ∈ Kset, ((minQ (parOf teff c1 mu) (Uset 120 ellPrimes k).card
        ((parOf teff c1 mu).cap * (parOf teff c1 mu).kap *
          ∑ c ∈ range 120, (nC 120 ellPrimes k c : ℚ) * (parOf teff c1 mu).teff.getD c 0) : ℚ) : ℝ) := horb
  rw [← horb'] at hlag
  -- (4) assemble
  set X := ((orbSum (parOf teff c1 mu) (orbits 120 ellPrimes) : ℚ) : ℝ) - mu * B -
    normR / ell * ∑ k ∈ Kset, ((lamC η ε (Nat.log 2 N) - 1) * (8 * kapR * TK teff k) + nuC η ε N) / 2 with hX
  have hsumphi : ∑ k ∈ Kset, normR / ell * ((Uset 120 ellPrimes k).card : ℝ) *
      phi (1 + Yt η N k / (Uset 120 ellPrimes k).card) =
      normR / ell * ∑ k ∈ Kset, ((Uset 120 ellPrimes k).card : ℝ) * phi (1 + Yt η N k / (Uset 120 ellPrimes k).card) := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  rw [hsumphi] at hlag
  -- `count ≥ (1-η) A_N (l/norm) X`
  have hcX : (1 - η) * AN N * (ell / normR) * X ≤ count N := by
    have e : (1 - η) * AN N * (ell / normR) * (normR / ell * ∑ k ∈ Kset, ((Uset 120 ellPrimes k).card : ℝ) *
        phi (1 + Yt η N k / (Uset 120 ellPrimes k).card)) =
        (1 - η) * AN N * ∑ k ∈ Kset, ((Uset 120 ellPrimes k).card : ℝ) *
          phi (1 + Yt η N k / (Uset 120 ellPrimes k).card) :=
      scale_alg hellR.ne' hnormR.ne'
    have := mul_le_mul_of_nonneg_left hlag (show 0 ≤ (1 - η) * AN N * (ell / normR) by positivity)
    rw [e] at this
    exact this.trans hcount
  -- `A_N l/(norm N) = log2hi/log 2 ≥ 1`
  have hF : 1 ≤ AN N * (ell / normR) / N := by
    rw [normR_eq hD]
    unfold AN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hl2 := log_two_bounds
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have e : (N : ℝ) / (120 * Nat.totient ell * Real.log 2) *
        (ell / ((ell : ℝ) / Nat.totient ell / (120 * (693147180559945310 / 10 ^ 18)))) / N =
        (693147180559945310 / 10 ^ 18) / Real.log 2 :=
      ratio_alg hN0 totient_ell_pos hl20 (by norm_num) (by exact_mod_cast ell_pos)
    rw [e, le_div_iff₀ hl20]
    linarith [hl2.2]
  -- `X ≥ orbSum - μB - Y(λ - 1) - norm ν/2`
  have hXg : ((orbSum (parOf teff c1 mu) (orbits 120 ellPrimes) : ℚ) : ℝ) - mu * B - Ycon teff * (lamC η ε (Nat.log 2 N) - 1) -
      normR * nuC η ε N / 2 ≤ X := by
    rw [hX]
    have hnu := nuC_nonneg hη1 hε N
    have e : normR / ell * ∑ k ∈ Kset, ((lamC η ε (Nat.log 2 N) - 1) * (8 * kapR * TK teff k) + nuC η ε N) / 2 =
        Ycon teff * (lamC η ε (Nat.log 2 N) - 1) + normR / ell * (Kset.card : ℝ) * (nuC η ε N / 2) := by
      unfold Ycon
      rw [show ∑ k ∈ Kset, ((lamC η ε (Nat.log 2 N) - 1) * (8 * kapR * TK teff k) + nuC η ε N) / 2 =
          (lamC η ε (Nat.log 2 N) - 1) * ∑ k ∈ Kset, 8 * kapR * TK teff k / 2 + Kset.card * (nuC η ε N / 2) by
        rw [mul_sum, show ((Kset.card : ℕ) : ℝ) * (nuC η ε N / 2) = ∑ k ∈ Kset, nuC η ε N / 2 by
          rw [sum_const, nsmul_eq_mul], ← sum_add_distrib]
        refine sum_congr rfl fun k _ => by ring]
      ring
    rw [e]
    have hK : normR / ell * (Kset.card : ℝ) * (nuC η ε N / 2) ≤ normR * nuC η ε N / 2 := by
      have h1 : normR / ell * (Kset.card : ℝ) ≤ normR := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hellR]
        exact mul_le_mul_of_nonneg_left card_Kset_le hnormR.le
      have := mul_le_mul_of_nonneg_right h1 (div_nonneg hnu (by norm_num) : 0 ≤ nuC η ε N / 2)
      linarith
    linarith
  -- `dens N ≥ (1-η) F X ≥ (1-η) Xg`
  have hdens : (1 - η) * (AN N * (ell / normR) / N) * X ≤ dens N := by
    unfold dens
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [le_div_iff₀ hN0]
    have e : (1 - η) * (AN N * (ell / normR) / N) * X * N = (1 - η) * (AN N * (ell / normR)) * X :=
      dens_alg hN0.ne'
    rw [e, ← mul_assoc]; exact hcX
  rcases le_or_gt 0 X with hX0 | hX0
  · have h1 : (1 - η) * X ≤ (1 - η) * (AN N * (ell / normR) / N) * X := by
      have := mul_le_mul_of_nonneg_right hF (mul_nonneg hη0.le hX0)
      linarith
    have h2 := mul_le_mul_of_nonneg_left hXg hη0.le
    linarith
  · have h2 := mul_le_mul_of_nonneg_left hXg hη0.le
    have h3 : (1 - η) * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hη0.le hX0.le
    linarith [dens_nonneg N]

end Romanoff
