import Romanoff.Assembly2
import Romanoff.M4Spec2

/-!
# M4: the lower density from the per-`N` bound, and the theorems

For fixed `η, ε`, eventually `dens N ≥ (1-η) g(N)` with
`g(N) = orbSum - μ (λ'_N B + ν'_N) - Y (λ_N - 1) - norm ν_N/2`, and `g(N) → G(η, ε)`, so `(1-η) G(η, ε) ≤ liminf dens`.
With `η = ε = 1/(n+2) → 0`, `(1-η) G(η, ε) → orbSum - μ B = lagBound` (`LagBoundSplit`, `NcQLink`).
-/

open Finset Filter Topology R45 R45.P45

namespace Romanoff

/-- The evaluator's bound, as a real number. -/
noncomputable def lagR (teff : List ℚ) (c1 mu : ℚ) : ℝ := ((lagBound (parOf teff c1 mu) (orbits 120 ellPrimes) : ℚ) : ℝ)

/-- The orbit sum, as a real number. -/
noncomputable def orbR (teff : List ℚ) (c1 mu : ℚ) : ℝ := ((orbSum (parOf teff c1 mu) (orbits 120 ellPrimes) : ℚ) : ℝ)

/-- `g(N)`. -/
noncomputable def gN (teff : List ℚ) (c1 mu : ℚ) (η ε : ℝ) (N : ℕ) : ℝ :=
  orbR teff c1 mu - mu * (lamB η ε (Nat.log 2 N) * Beval teff + nuB η ε N) -
    Ycon teff * (lamC η ε (Nat.log 2 N) - 1) - normR * nuC η ε N / 2

/-- `G(η, ε) = lim g`. -/
noncomputable def Glim (teff : List ℚ) (c1 mu : ℚ) (η ε : ℝ) : ℝ :=
  orbR teff c1 mu - mu * ((1 + ε / C1R) / (1 - η) * Beval teff) - Ycon teff * ((1 + ε / 8) / (1 - η) - 1)

/-- The per-`N` bound holds eventually, for fixed `η, ε`. -/
theorem eventually_dens_ge (hB1 : XUESPBound) (hB2 : SumXUJTBound) (hC1 : OrbSumLink) (hD : DataFacts)
    {teff : List ℚ} (hT : TBound teff) (c1 mu : ℚ) (hmu : (0 : ℝ) ≤ mu)
    (hESP : ESP28 ell) (hPNT : PNTAP ell) (hJT : mu = 0 ∨ JTProp2)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1 - η) * gN teff c1 mu η ε N ≤ dens N := by
  obtain ⟨N0, hN0⟩ := hESP ε hε
  have hFMev := first_moment (per := 120) (by norm_num) goodPrimes_ell distinctPrimes_ell hPNT hη
  have hJTev : ∀ᶠ N : ℕ in atTop, mu = 0 ∨ ∀ h : ℤ, 0 < h → h < N →
      (pairCount N h : ℝ) ≤ (67814 / 10000 + ε) * C0up * N / Real.log N ^ 2 * sing h.natAbs := by
    rcases hJT with h0 | hJ
    · exact Eventually.of_forall fun _ => Or.inl h0
    · obtain ⟨N1, hN1⟩ := hJ ε hε
      exact eventually_atTop.mpr ⟨N1, fun N hN => Or.inr (hN1 N hN)⟩
  filter_upwards [hFMev, hJTev, eventually_ge_atTop (max N0 2)] with N hFM hJTN hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hESPN := hN0 N (le_trans (le_max_left _ _) hN)
  have hFM' : ∀ k < ell, (Uset 120 ellPrimes k).Nonempty →
      (1 - η) * (Uset 120 ellPrimes k).card * AN N ≤ S1 ell N k := by
    intro k hk hne
    have := hFM k hk hne
    unfold AN
    have e : ((120 : ℕ) : ℝ) = 120 := by norm_num
    rw [e] at this
    exact this
  rcases hJTN with h0 | hJN
  · -- `μ = 0`: any budget
    have := dens_lower_at hB1 hC1 hD hT c1 mu hmu hη hη1 hε hN2 hFM' hESPN _ le_rfl
    unfold gN
    rw [h0] at this ⊢
    simp only [Rat.cast_zero, zero_mul, sub_zero] at this ⊢
    exact this
  · have hbud := budget_bound hB2 hD hT hη1 hε hN2 hJN
    exact dens_lower_at hB1 hC1 hD hT c1 mu hmu hη hη1 hε hN2 hFM' hESPN _ hbud

/-- `g(N) → G(η, ε)`. -/
theorem tendsto_gN (hE : LimitFacts) (hR0 : R0Bound) (teff : List ℚ) (c1 mu : ℚ) {η ε : ℝ} (hη1 : η < 1) :
    Tendsto (gN teff c1 mu η ε) atTop (𝓝 (Glim teff c1 mu η ε)) := by
  obtain ⟨h120, hL2, hEL⟩ := hE
  have hEL' := hEL hR0
  have hη0 : (1 - η) ≠ 0 := by linarith
  -- `λ_N → (1 + ε/8)/(1 - η)`, `λ'_N → (1 + ε/C1)/(1 - η)`
  have hlamC : Tendsto (fun N : ℕ => lamC η ε (Nat.log 2 N)) atTop (𝓝 ((1 + ε / 8) / (1 - η))) := by
    have := ((tendsto_const_nhds (x := 1 + ε / 8)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h120)).div_const (1 - η)
    simpa [lamC] using this
  have hlamB : Tendsto (fun N : ℕ => lamB η ε (Nat.log 2 N)) atTop (𝓝 ((1 + ε / C1R) / (1 - η))) := by
    have := ((tendsto_const_nhds (x := 1 + ε / C1R)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h120)).div_const (1 - η)
    simpa [lamB] using this
  -- `ν_N → 0`, `ν'_N → 0`
  have hnuC : Tendsto (fun N : ℕ => nuC η ε N) atTop (𝓝 0) := by
    have h1 := (hL2.const_mul (9 * (120 * Nat.totient ell * Real.log 2))).add
      (hEL'.const_mul ((8 + ε) * C0up * Pl ellPrimes * 120 * Real.log 2 * 14400))
    have h2 := h1.div_const (1 - η)
    simp only [mul_zero, add_zero, zero_div] at h2
    refine h2.congr fun N => ?_
    unfold nuC
    ring
  have hnuB : Tendsto (fun N : ℕ => nuB η ε N) atTop (𝓝 0) := by
    have h2 := (hEL'.const_mul ((C1R + ε) * C0up * Pl ellPrimes * 120 * Real.log 2 * 14400)).div_const (1 - η)
    simp only [mul_zero, zero_div] at h2
    refine h2.congr fun N => ?_
    unfold nuB
    rw [mul_comm (1 - η) (Real.log N ^ 2), ← div_div]
    ring
  have := ((tendsto_const_nhds (x := orbR teff c1 mu)).sub
      ((hlamB.mul_const (Beval teff)).add hnuB |>.const_mul (mu : ℝ))).sub
      ((hlamC.sub_const 1).const_mul (Ycon teff)) |>.sub ((hnuC.const_mul normR).div_const 2)
  simp only [add_zero, mul_zero, zero_div, sub_zero] at this
  exact this

/-- `(1 - η) G(η, ε) ≤ liminf dens`. -/
theorem liminf_ge_G (hB1 : XUESPBound) (hB2 : SumXUJTBound) (hC1 : OrbSumLink) (hD : DataFacts) (hE : LimitFacts)
    {teff : List ℚ} (hT : TBound teff) (c1 mu : ℚ) (hmu : (0 : ℝ) ≤ mu)
    (hESP : ESP28 ell) (hPNT : PNTAP ell) (hR0 : R0Bound) (hJT : mu = 0 ∨ JTProp2)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε) :
    (1 - η) * Glim teff c1 mu η ε ≤ liminf dens atTop := by
  rw [← lowerDensityGe_iff]
  intro δ hδ
  have hT1 := tendsto_gN hE hR0 teff c1 mu (ε := ε) hη1
  have hT2 := hT1.const_mul (1 - η)
  have hev := (tendsto_order.mp hT2).1 ((1 - η) * Glim teff c1 mu η ε - δ) (by linarith)
  filter_upwards [hev, eventually_dens_ge hB1 hB2 hC1 hD hT c1 mu hmu hESP hPNT hJT hη hη1 hε] with N h1 h2
  linarith

/-- `lagBound ≤ liminf dens`. -/
theorem lagR_le_liminf (hB1 : XUESPBound) (hB2 : SumXUJTBound) (hC1 : OrbSumLink) (hC2 : NcQLink)
    (hC3 : LagBoundSplit) (hD : DataFacts) (hE : LimitFacts)
    {teff : List ℚ} (hT : TBound teff) (c1 mu : ℚ) (hmu : (0 : ℝ) ≤ mu)
    (hESP : ESP28 ell) (hPNT : PNTAP ell) (hR0 : R0Bound) (hJT : mu = 0 ∨ (JTProp2 ∧ (c1 : ℝ) = C1R)) :
    lagR teff c1 mu ≤ liminf dens atTop := by
  -- `orbSum - μ B = lagBound`
  have hsplit : orbR teff c1 mu - mu * Beval teff = lagR teff c1 mu := by
    unfold orbR lagR
    rw [hC3 (parOf teff c1 mu) (orbits 120 ellPrimes) (by rw [parOf_teff, parOf_per]; exact hT.1)]
    rcases hJT with h0 | ⟨_, hc1⟩
    · rw [parOf_mu, h0]; simp
    · rw [parOf_mu, parOf_c1, parOf_kap, parOf_per, parOf_teff]
      push_cast
      have hsum : ∑ c ∈ range 120, ((ncQ (parOf teff c1 mu) (orbits 120 ellPrimes) c : ℚ) : ℝ) *
          ((teff.getD c 0 : ℚ) : ℝ) = 1 / (ell : ℝ) * ∑ k ∈ range ell, TK teff k := by
        have e1 : ∀ c ∈ range 120, ((ncQ (parOf teff c1 mu) (orbits 120 ellPrimes) c : ℚ) : ℝ) =
            1 / (ell : ℝ) * ∑ k ∈ range ell, (nC 120 ellPrimes k c : ℝ) := by
          intro c hc
          rw [hC2 _ c (mem_range.mp hc), parOf_ell]
          push_cast
          rw [show ((ellN : ℕ) : ℝ) = (ell : ℝ) by exact_mod_cast hD.1]
        calc ∑ c ∈ range 120, ((ncQ (parOf teff c1 mu) (orbits 120 ellPrimes) c : ℚ) : ℝ) * ((teff.getD c 0 : ℚ) : ℝ)
            = ∑ c ∈ range 120, ∑ k ∈ range ell, 1 / (ell : ℝ) * ((nC 120 ellPrimes k c : ℝ) * ((teff.getD c 0 : ℚ) : ℝ)) := by
              refine sum_congr rfl fun c hc => ?_
              rw [e1 c hc, mul_sum, sum_mul]
              exact sum_congr rfl fun k _ => by ring
          _ = ∑ k ∈ range ell, ∑ c ∈ range 120, 1 / (ell : ℝ) * ((nC 120 ellPrimes k c : ℝ) * ((teff.getD c 0 : ℚ) : ℝ)) :=
              sum_comm
          _ = 1 / (ell : ℝ) * ∑ k ∈ range ell, TK teff k := by
              rw [mul_sum]
              refine sum_congr rfl fun k _ => ?_
              unfold TK
              rw [mul_sum]
      rw [hsum]
      unfold Beval kapR
      rw [← hc1]
      ring
  -- the sequence `η_n = ε_n = 1/(n+2)`
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with htdef
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n < 1 := fun n => by
    rw [htdef]; dsimp only; rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have htend : Tendsto t atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    exact h2
  have hlim : Tendsto (fun n => (1 - t n) * Glim teff c1 mu (t n) (t n)) atTop (𝓝 (lagR teff c1 mu)) := by
    have h1 : Tendsto (fun n => 1 - t n) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub htend
    have hden : Tendsto (fun n => 1 - t n) atTop (𝓝 (1 - 0)) := (tendsto_const_nhds (x := (1 : ℝ))).sub htend
    have hG : Tendsto (fun n => Glim teff c1 mu (t n) (t n)) atTop
        (𝓝 (orbR teff c1 mu - mu * ((1 + 0 / C1R) / (1 - 0) * Beval teff) - Ycon teff * ((1 + 0 / 8) / (1 - 0) - 1))) := by
      unfold Glim
      have hC1R : C1R ≠ 0 := by unfold C1R; norm_num
      refine ((tendsto_const_nhds (x := orbR teff c1 mu)).sub (((((tendsto_const_nhds (x := (1 : ℝ))).add (htend.div_const C1R)).div hden
        (by norm_num)).mul_const (Beval teff)).const_mul (mu : ℝ))).sub
        ((((tendsto_const_nhds (x := (1 : ℝ))).add (htend.div_const 8)).div hden (by norm_num)).sub_const 1 |>.const_mul (Ycon teff))
    have := h1.mul hG
    simp only [zero_div, add_zero, sub_zero, div_one, one_mul, sub_self, mul_zero] at this
    rw [← hsplit]
    exact this
  exact le_of_tendsto' hlim fun n =>
    liminf_ge_G hB1 hB2 hC1 hD hE hT c1 mu hmu hESP hPNT hR0 (hJT.imp id fun h => h.1) (ht0 n) (ht1 n) (ht0 n)

end Romanoff
