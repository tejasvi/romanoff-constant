import Romanoff.PairBounds

/-!
# The first moment in each class, from the prime number theorem in progressions

For `a ≤ L - 1` with `a mod per ∈ U_k`, `p ↦ p + 2^a` maps the primes `p ≤ N - 2^a`, `p ≡ k - 2^a (mod l)` into the
integers of class `k` represented with exponent `a`; the residue is a unit and `N - 2^a ≥ N/2`, so (I3), uniformly over
the finitely many residues, gives `S1(k) ≥ (1 - η) |U_k| N/(per φ(l) log 2)` for all large `N`.
-/

open Finset Filter Topology

namespace Romanoff

theorem card_mod_eq_ge (M per e : ℕ) (hper : 0 < per) (he : e < per) :
    M / per ≤ ((Icc 1 M).filter (· % per = e)).card := by
  have key : ∀ j < M / per, j * per + (if e = 0 then per else e) ∈ (Icc 1 M).filter (· % per = e) := by
    intro j hj
    have h1 : j * per + per ≤ M := by
      have h2 : (j + 1) * per ≤ M / per * per := Nat.mul_le_mul_right per (by omega)
      have h3 := Nat.div_mul_le_self M per
      rw [add_mul, one_mul] at h2
      omega
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · split_ifs with h0
      · omega
      · omega
    · split_ifs with h0
      · omega
      · omega
    · split_ifs with h0
      · rw [h0, add_comm, Nat.add_mul_mod_self_right, Nat.mod_self]
      · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]
  have := card_le_card_of_injOn (s := range (M / per)) (t := (Icc 1 M).filter (· % per = e))
    (fun j => j * per + if e = 0 then per else e) (fun j hj => key j (mem_range.mp hj)) ?_
  · rwa [card_range] at this
  · intro i _ j _ hij
    simp only at hij
    have : i * per = j * per := by omega
    exact Nat.eq_of_mul_eq_mul_right hper this

theorem card_mod_mem_ge (M per : ℕ) (hper : 0 < per) (U : Finset ℕ) (hU : ∀ e ∈ U, e < per) :
    U.card * (M / per) ≤ ((Icc 1 M).filter (fun a => a % per ∈ U)).card := by
  rw [card_eq_sum_card_fiberwise (s := (Icc 1 M).filter (fun a => a % per ∈ U)) (f := fun a => a % per) (t := U)
    (fun a ha => (mem_filter.mp ha).2)]
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun e he => ?_
  refine (card_mod_eq_ge M per e hper (hU e he)).trans (card_le_card fun a ha => ?_)
  obtain ⟨h1, h2⟩ := mem_filter.mp ha
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨h1, h2 ▸ he⟩, h2⟩

/-- `p ↦ p + 2^a` from the primes `≤ N - 2^a` in the residue `k - 2^a` to the class `k` with exponent `a`. -/
theorem primeCount_le_rep {l N k a : ℕ} (hl : 0 < l) (hk : k < l) (ha1 : 1 ≤ a) (haN : 2 ^ a ≤ N) :
    primeCountMod (N - 2 ^ a) l (resid l k a) ≤ ((cls l N k).filter fun n => a ∈ repSet n).card := by
  unfold primeCountMod
  refine card_le_card_of_injOn (fun p => p + 2 ^ a) (fun p hp => ?_) (fun p _ q _ h => by simpa using h)
  show p + 2 ^ a ∈ _
  obtain ⟨hpN, hpr, hpres⟩ := mem_filter.mp hp
  have hpN' : p ≤ N - 2 ^ a := Nat.lt_succ_iff.mp (mem_range.mp hpN)
  have hp2 := hpr.two_le
  have hlt : a < 2 ^ a := Nat.lt_two_pow_self
  have hpa : p + 2 ^ a ≤ N := Nat.add_le_of_le_sub haN hpN'
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hpa⟩, ?_⟩, ?_⟩
  · -- `p + 2^a ≡ k (mod l)`
    unfold resid at hpres
    rw [Nat.mod_mod] at hpres
    set r := 2 ^ a % l
    have hrl : r < l := Nat.mod_lt _ hl
    have e1 : p + 2 ^ a ≡ k + l - r + 2 ^ a [MOD l] := Nat.ModEq.add_right _ hpres
    have e2 : k + l - r + 2 ^ a ≡ k + l - r + r [MOD l] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
    have e3 : k + l - r + r ≡ k [MOD l] := by rw [Nat.sub_add_cancel (by omega)]; exact Nat.add_modEq_right
    have := e1.trans (e2.trans e3)
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hk]
  · refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1, by omega⟩, by omega, ?_⟩
    simpa using hpr

/-- (I3) uniformly over the residues coprime to `l`. -/
theorem pnt_uniform {l : ℕ} (hl : 0 < l) (hP : PNTAP l) {η : ℝ} (hη : 0 < η) :
    ∃ X0 : ℕ, 2 ≤ X0 ∧ ∀ x ≥ X0, ∀ b < l, Nat.Coprime b l →
      (1 - η) * x / ((Nat.totient l : ℝ) * Real.log x) ≤ primeCountMod x l b := by
  have hev : ∀ᶠ x : ℕ in atTop, ∀ b ∈ (range l).filter (fun b => Nat.Coprime b l),
      1 - η < (primeCountMod x l b : ℝ) * Nat.totient l * Real.log x / x := by
    rw [eventually_all_finset]
    intro b hb
    exact (tendsto_order.mp (hP b (mem_filter.mp hb).2)).1 (1 - η) (by linarith)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hev
  refine ⟨max X1 2, le_max_right _ _, fun x hx b hb hcop => ?_⟩
  have h := hX1 x (le_trans (le_max_left _ _) hx) b (mem_filter.mpr ⟨mem_range.mpr hb, hcop⟩)
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have htot : (0 : ℝ) < Nat.totient l := by exact_mod_cast Nat.totient_pos.mpr hl
  have hx0 : (0 : ℝ) < x := by linarith
  rw [lt_div_iff₀ hx0] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem sum_two_pow_lt (n : ℕ) : ∑ i ∈ range n, 2 ^ i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

/-- The final algebra of the first moment. -/
theorem fm_alg {s per ph lN N l2 η Acnt : ℝ} (hs : 1 ≤ s) (hper : 0 < per) (hph : 0 < ph) (hlN : 0 < lN) (hN : 0 ≤ N)
    (hl2 : 0 < l2) (hη1 : η ≤ 1) (hsmall : (2 + 2 * per) * l2 ≤ η * lN)
    (hA : s * ((lN / l2 - 2 - per) / per) ≤ Acnt) :
    (1 - η) * (1 - η) * s * (N / (per * ph * l2)) ≤ (1 - η) / (ph * lN) * (Acnt * N - N) := by
  have h1 : 0 ≤ 1 - η := by linarith
  have key : s * (1 - η) / (per * ph * l2) ≤ (s * ((lN / l2 - 2 - per) / per) - 1) / (ph * lN) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (s * ((lN / l2 - 2 - per) / per) - 1) * (per * ph * l2) = ph * (s * (lN - (2 + per) * l2) - per * l2) := by
      field_simp
      ring
    rw [e]
    have : s * (1 - η) * (ph * lN) ≤ ph * (s * (lN - (2 + per) * l2) - per * l2) := by
      have h2 : per * l2 ≤ s * (per * l2) := le_mul_of_one_le_left (by positivity) hs
      have h3 : s * ((2 + 2 * per) * l2) ≤ s * (η * lN) := mul_le_mul_of_nonneg_left hsmall (by linarith)
      nlinarith
    linarith
  calc (1 - η) * (1 - η) * s * (N / (per * ph * l2)) = (1 - η) * N * (s * (1 - η) / (per * ph * l2)) := by ring
    _ ≤ (1 - η) * N * ((s * ((lN / l2 - 2 - per) / per) - 1) / (ph * lN)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg h1 hN)
    _ ≤ (1 - η) * N * ((Acnt - 1) / (ph * lN)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg h1 hN)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = (1 - η) / (ph * lN) * (Acnt * N - N) := by ring

theorem log_le_log_two_mul (N : ℕ) (hN : 1 ≤ N) : Real.log N < (Nat.log 2 N + 1) * Real.log 2 := by
  have h1 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2 : (N : ℝ) < 2 ^ (Nat.log 2 N + 1) := by exact_mod_cast h1
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc Real.log N < Real.log (2 ^ (Nat.log 2 N + 1)) := Real.log_lt_log h0 h2
    _ = (Nat.log 2 N + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring

/-- The first moment: for every `η > 0`, eventually `S1(k) ≥ (1 - η) |U_k| N/(per φ(l) log 2)` for every class `k`
with `U_k ≠ ∅`. -/
theorem first_moment {per : ℕ} (hper : 0 < per) {ps : List ℕ} (hg : GoodPrimes per ps) (hd : DistinctPrimes ps)
    (hP : PNTAP ps.prod) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ k < ps.prod, (Uset per ps k).Nonempty →
      (1 - η) * (Uset per ps k).card * ((N : ℝ) / (per * Nat.totient ps.prod * Real.log 2)) ≤ S1 ps.prod N k := by
  set l := ps.prod with hldef
  have hl : 0 < l := prod_pos_of_primes ps hd.2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htot : (0 : ℝ) < Nat.totient l := by exact_mod_cast Nat.totient_pos.mpr hl
  have hper' : (0 : ℝ) < per := by exact_mod_cast hper
  by_cases hη1 : 1 ≤ η
  · refine Eventually.of_forall fun N k _ _ => ?_
    have : (1 - η) * (Uset per ps k).card * ((N : ℝ) / (per * Nat.totient l * Real.log 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
        (by positivity)
    exact this.trans (Nat.cast_nonneg _)
  rw [not_le] at hη1
  set η' := η / 2 with hη'
  have hη'0 : 0 < η' := by positivity
  obtain ⟨X0, hX0, hPNT⟩ := pnt_uniform hl hP hη'0
  have hlogev : ∀ᶠ N : ℕ in atTop, (2 + 2 * (per : ℝ)) * Real.log 2 / η' ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlogev, eventually_ge_atTop (2 * X0)] with N hlogN hN k hk hU
  have hN2 : 2 ≤ N := by omega
  set L := Nat.log 2 N with hL
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN2)
  have h2L : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  set U := Uset per ps k
  set A := (Icc 1 (L - 1)).filter (fun a => a % per ∈ U) with hA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  -- (1) restrict `S1` to the exponents in `A`
  have hS1 : ∑ a ∈ A, ((cls l N k).filter fun n => a ∈ repSet n).card ≤ S1 l N k := by
    rw [S1_eq]
    exact sum_le_sum_of_subset_of_nonneg (fun a ha => by
      have := mem_Icc.mp (mem_filter.mp ha).1; exact mem_Icc.mpr ⟨this.1, by omega⟩) fun _ _ _ => Nat.zero_le _
  -- (2) each exponent: PNT at `x = N - 2^a ≥ N/2 ≥ X0`
  have hterm : ∀ a ∈ A, (1 - η') * ((N : ℝ) - 2 ^ a) / (Nat.totient l * Real.log N) ≤
      (((cls l N k).filter fun n => a ∈ repSet n).card : ℝ) := by
    intro a ha
    obtain ⟨haI, haU⟩ := mem_filter.mp ha
    obtain ⟨ha1, haL⟩ := mem_Icc.mp haI
    have h2a : 2 * 2 ^ a ≤ N := by
      have : 2 ^ (a + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this; omega
    have hx : X0 ≤ N - 2 ^ a := by omega
    have hpc := hPNT (N - 2 ^ a) hx (resid l k a) (Nat.mod_lt _ hl) (resid_coprime hper hg hd haU)
    have hcount := primeCount_le_rep (l := l) (N := N) hl hk ha1 (by omega)
    have hcast : ((N - 2 ^ a : ℕ) : ℝ) = (N : ℝ) - 2 ^ a := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at hpc
    have hxpos : (0 : ℝ) < (N : ℝ) - 2 ^ a := by
      have : ((2 * 2 ^ a : ℕ) : ℝ) ≤ N := by exact_mod_cast h2a
      push_cast at this
      have : (0 : ℝ) < 2 ^ a := by positivity
      linarith
    have hlogx : Real.log ((N : ℝ) - 2 ^ a) ≤ Real.log N := Real.log_le_log hxpos (by
      have : (0 : ℝ) < 2 ^ a := by positivity
      linarith)
    have hlogx0 : 0 < Real.log ((N : ℝ) - 2 ^ a) := by
      have : (2 : ℝ) ≤ (N : ℝ) - 2 ^ a := by
        have : ((X0 : ℕ) : ℝ) ≤ ((N - 2 ^ a : ℕ) : ℝ) := by exact_mod_cast hx
        rw [hcast] at this
        have : (2 : ℝ) ≤ X0 := by exact_mod_cast hX0
        linarith
      exact Real.log_pos (by linarith)
    have hmono : (1 - η') * ((N : ℝ) - 2 ^ a) / (Nat.totient l * Real.log N) ≤
        (1 - η') * ((N : ℝ) - 2 ^ a) / (Nat.totient l * Real.log ((N : ℝ) - 2 ^ a)) := by
      apply div_le_div_of_nonneg_left _ (by positivity) (mul_le_mul_of_nonneg_left hlogx htot.le)
      exact mul_nonneg (by linarith) hxpos.le
    refine hmono.trans (hpc.trans ?_)
    exact_mod_cast hcount
  -- (3) sum over `A`
  have hsum2 : (∑ a ∈ A, (2 : ℝ) ^ a) ≤ N := by
    have h1 : ∑ a ∈ A, 2 ^ a ≤ ∑ a ∈ range L, 2 ^ a :=
      sum_le_sum_of_subset_of_nonneg (fun a ha => by
        have := mem_Icc.mp (mem_filter.mp ha).1; exact mem_range.mpr (by omega)) fun _ _ _ => Nat.zero_le _
    have h2 := sum_two_pow_lt L
    have : ∑ a ∈ A, 2 ^ a ≤ N := by omega
    exact_mod_cast this
  have hchain : (1 - η') / (Nat.totient l * Real.log N) * (A.card * (N : ℝ) - N) ≤ (S1 l N k : ℝ) := by
    calc (1 - η') / (Nat.totient l * Real.log N) * (A.card * (N : ℝ) - N)
        ≤ (1 - η') / (Nat.totient l * Real.log N) * (A.card * (N : ℝ) - ∑ a ∈ A, (2 : ℝ) ^ a) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) (by positivity))
      _ = ∑ a ∈ A, (1 - η') * ((N : ℝ) - 2 ^ a) / (Nat.totient l * Real.log N) := by
          rw [← sum_div, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ a ∈ A, (((cls l N k).filter fun n => a ∈ repSet n).card : ℝ) := sum_le_sum hterm
      _ ≤ (S1 l N k : ℝ) := by exact_mod_cast hS1
  -- (4) `|A| ≥ |U| ((log N/log 2 - 2 - per)/per)`
  have hUper : ∀ e ∈ U, e < per := fun e he => mem_range.mp (mem_filter.mp he).1
  have hAcard : (U.card : ℝ) * ((Real.log N / Real.log 2 - 2 - per) / per) ≤ A.card := by
    have h1 := card_mod_mem_ge (L - 1) per hper U hUper
    have h2 : ((L - 1 : ℕ) : ℝ) / per - 1 ≤ (((L - 1) / per : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := L - 1) hper
      have h3 : ((L - 1 : ℕ) : ℝ) < (((L - 1) / per : ℕ) : ℝ) * per + per := by exact_mod_cast this
      rw [div_sub_one hper'.ne', div_le_iff₀ hper']
      linarith
    have h4 : (Real.log N / Real.log 2 - 2 - per) / per ≤ ((L - 1 : ℕ) : ℝ) / per - 1 := by
      have hlt := log_le_log_two_mul N (by omega)
      have : Real.log N / Real.log 2 < L + 1 := by rw [div_lt_iff₀ hlog2]; linarith
      rw [Nat.cast_sub hL1, div_sub_one hper'.ne']
      apply div_le_div_of_nonneg_right _ hper'.le
      push_cast; linarith
    have h5 : (U.card : ℝ) * (((L - 1) / per : ℕ) : ℝ) ≤ A.card := by exact_mod_cast h1
    calc (U.card : ℝ) * ((Real.log N / Real.log 2 - 2 - per) / per)
        ≤ (U.card : ℝ) * (((L - 1) / per : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (h4.trans h2) (Nat.cast_nonneg _)
      _ ≤ A.card := h5
  -- (5) the algebra
  have hs1 : (1 : ℝ) ≤ U.card := by exact_mod_cast hU.card_pos
  have hsmall : (2 + 2 * (per : ℝ)) * Real.log 2 ≤ η' * Real.log N := by
    rw [div_le_iff₀ hη'0] at hlogN; linarith
  have halg := fm_alg (s := U.card) (per := per) (ph := Nat.totient l) (lN := Real.log N) (N := N)
    (l2 := Real.log 2) (η := η') (Acnt := A.card) hs1 hper' htot hlogNpos hN0.le hlog2 (by linarith) hsmall hAcard
  have hfin : (1 - η) * U.card * ((N : ℝ) / (per * Nat.totient l * Real.log 2)) ≤
      (1 - η') * (1 - η') * U.card * ((N : ℝ) / (per * Nat.totient l * Real.log 2)) := by
    have hq : (1 - η) ≤ (1 - η') * (1 - η') := by rw [hη']; nlinarith
    have hpos : 0 ≤ (U.card : ℝ) * ((N : ℝ) / (per * Nat.totient l * Real.log 2)) := by positivity
    nlinarith
  exact hfin.trans (halg.trans hchain)

end Romanoff
