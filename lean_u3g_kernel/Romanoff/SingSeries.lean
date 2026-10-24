import Romanoff.PairBounds
import Romanoff.TBoundSpec

/-!
# Mean value of the singular series over the pairs `a₁ ≠ a₂ ≤ L` in fixed residues mod 120

`S'(h) = Σ_{m | h, m odd squarefree, (m, l) = 1} f(m)`, and for odd `m` with `o = ord_m(2)`:
`m | 2^{max} - 2^{min}` iff `o | |a₂ - a₁|`.  For residues `r₁, r₂` (difference `c`), the pairs with `o | a₂ - a₁` number
at most `(L/per + 1)(L g/(per o) + 1)` (`g = gcd(o, per)`), and none unless `g | c` and `o ≤ L`.  Hence
`Σ S'(h) ≤ (L/120 + 1)(L/120) T(c) + (L/120 + 1) E(L)`, with `T(c)` bounded by `TBound` and
`E(L) = Σ_{m : o ≤ L} f(m)`.
-/

open Finset

namespace Romanoff

/-- `2^{max(a₁, a₂)} - 2^{min(a₁, a₂)}`. -/
def hsh (a1 a2 : ℕ) : ℕ := 2 ^ max a1 a2 - 2 ^ min a1 a2

/-- The odd squarefree `m < 2^L` coprime to `l`. -/
def SL (l L : ℕ) : Finset ℕ := (range (2 ^ L)).filter fun m => Odd m ∧ Squarefree m ∧ Nat.Coprime m l

/-- `E(L) = Σ_{m ∈ SL, ord_m(2) ≤ L} f(m)`. -/
noncomputable def EL (l L : ℕ) : ℝ := ∑ m ∈ (SL l L).filter (fun m => ordm m ≤ L), fm m

theorem fm_nonneg (m : ℕ) : 0 ≤ fm m := by
  unfold fm
  refine prod_nonneg fun p hp => one_div_nonneg.mpr ?_
  have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  linarith

/-! ## `S'(h)` as a sum over divisors -/

theorem singP_le_sum {ps : List ℕ} (hd : DistinctPrimes ps) {h L : ℕ} (hh : h ≠ 0) (hL : h < 2 ^ L) :
    singP ps h ≤ ∑ m ∈ SL ps.prod L, if m ∣ h then fm m else 0 := by
  set P' := h.primeFactors.filter (fun p => 2 < p ∧ p ∉ ps) with hP'
  have hprime : ∀ p ∈ P', p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have h1 : singP ps h = ∑ T ∈ P'.powerset, ∏ p ∈ T, 1 / ((p : ℝ) - 2) := by
    unfold singP
    rw [← prod_one_add]
    refine prod_congr rfl fun p hp => ?_
    have h2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  -- each subset `T` gives the divisor `m_T = ∏_{p ∈ T} p`
  have hfm : ∀ T ∈ P'.powerset, ∏ p ∈ T, 1 / ((p : ℝ) - 2) = fm (∏ p ∈ T, p) := by
    intro T hT
    unfold fm
    rw [Nat.primeFactors_prod fun p hp => hprime p (mem_powerset.mp hT hp)]
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (P'.powerset : Set (Finset ℕ)) := by
    intro T hT T' hT' he
    have e1 := Nat.primeFactors_prod fun p hp => hprime p (mem_powerset.mp hT hp)
    have e2 := Nat.primeFactors_prod fun p hp => hprime p (mem_powerset.mp hT' hp)
    simp only at he
    rw [← e1, ← e2, he]
  have hsub : P'.powerset.image (fun T => ∏ p ∈ T, p) ⊆ (SL ps.prod L).filter (fun m => m ∣ h) := by
    intro m hm
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hm
    have hTP := mem_powerset.mp hT
    have hTpr : ∀ p ∈ T, p.Prime := fun p hp => hprime p (hTP hp)
    have hpf : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hTpr
    have hdvd : (∏ p ∈ T, p) ∣ h := prod_primes_dvd h (fun p hp => (hTpr p hp).prime)
      fun p hp => Nat.dvd_of_mem_primeFactors (mem_filter.mp (hTP hp)).1
    have hpos : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hTpr p hp).pos
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hh) hdvd)
      hL), ?_, ?_, ?_⟩, hdvd⟩
    · -- odd: `2` is not a prime factor
      rw [Nat.odd_iff]
      by_contra h2
      have h2' : 2 ∣ ∏ p ∈ T, p := Nat.dvd_of_mod_eq_zero (by omega)
      have : 2 ∈ T := by rw [← hpf]; exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2', hpos.ne'⟩
      exact absurd (mem_filter.mp (hTP this)).2.1 (lt_irrefl 2)
    · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_) fun p hp => (hTpr p hp).prime.squarefree
      simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hTpr p hp) (hTpr q hq)).mpr hpq
    · refine (coprime_list_prod fun q hq => ⟨hd.2 q hq, fun hqd => ?_⟩)
      have : q ∈ T := by rw [← hpf]; exact Nat.mem_primeFactors.mpr ⟨hd.2 q hq, hqd, hpos.ne'⟩
      exact (mem_filter.mp (hTP this)).2.2 hq
  rw [h1, sum_congr rfl hfm, ← sum_image hinj, ← sum_filter]
  exact sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => fm_nonneg m

/-! ## Orders -/

theorem ordm_pos {m : ℕ} (hm : Odd m) : 0 < ordm m := by
  have : NeZero m := ⟨hm.pos.ne'⟩
  have hc : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  have : ordm m = orderOf (ZMod.unitOfCoprime 2 hc) := by
    unfold ordm
    rw [← orderOf_units, ZMod.coe_unitOfCoprime]
    norm_num
  rw [this]
  exact orderOf_pos _

theorem ordm_dvd_iff (m d : ℕ) : ordm m ∣ d ↔ m ∣ 2 ^ d - 1 := by
  unfold ordm
  rw [orderOf_dvd_iff_pow_eq_one]
  have : (2 : ZMod m) ^ d = ((2 ^ d : ℕ) : ZMod m) := by push_cast; rfl
  rw [this, show (1 : ZMod m) = ((1 : ℕ) : ZMod m) by simp, ZMod.natCast_eq_natCast_iff]
  exact ⟨fun h => (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm,
    fun h => ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr h).symm⟩

theorem hsh_eq (a1 a2 : ℕ) : hsh a1 a2 = 2 ^ min a1 a2 * (2 ^ (max a1 a2 - min a1 a2) - 1) := by
  unfold hsh
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' (min_le_max)]

theorem dvd_hsh_iff {m : ℕ} (hm : Odd m) (a1 a2 : ℕ) :
    m ∣ hsh a1 a2 ↔ ordm m ∣ max a1 a2 - min a1 a2 := by
  rw [hsh_eq, ordm_dvd_iff]
  exact Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_right _ (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hm)))

theorem hsh_pos {a1 a2 : ℕ} (h : a1 ≠ a2) : 0 < hsh a1 a2 := by
  unfold hsh
  have : 2 ^ min a1 a2 < 2 ^ max a1 a2 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem hsh_lt {a1 a2 L : ℕ} (h2 : max a1 a2 ≤ L) : hsh a1 a2 < 2 ^ L := by
  unfold hsh
  have : 2 ^ max a1 a2 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) h2
  have : 1 ≤ 2 ^ min a1 a2 := Nat.one_le_two_pow
  have : 0 < 2 ^ L := Nat.two_pow_pos L
  omega

/-! ## Counting pairs -/

/-- A subset of `[0, L]` whose elements are pairwise congruent mod `M` has at most `L/M + 1` elements. -/
theorem card_le_of_modEq {T : Finset ℕ} {L M : ℕ} (hT : ∀ x ∈ T, x ≤ L)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x % M = y % M) : T.card ≤ L / M + 1 := by
  have := card_le_card_of_injOn (t := range (L / M + 1)) (fun x => x / M)
    (fun x hx => mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hT x hx))))
    (fun x hx y hy hxy => by
      simp only at hxy
      rw [← Nat.div_add_mod x M, ← Nat.div_add_mod y M, hxy, hc x hx y hy])
  rwa [card_range] at this

theorem card_le_of_modEq_real {T : Finset ℕ} {L M : ℕ} (hT : ∀ x ∈ T, x ≤ L)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x % M = y % M) : (T.card : ℝ) ≤ (L : ℝ) / M + 1 := by
  have h1 := card_le_of_modEq hT hc
  have h2 : ((L / M : ℕ) : ℝ) ≤ (L : ℝ) / M := Nat.cast_div_le
  calc (T.card : ℝ) ≤ ((L / M + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((L / M : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (L : ℝ) / M + 1 := by linarith

theorem modEq_of_dvd_dist {o a b : ℕ} (h : o ∣ max a b - min a b) : a ≡ b [MOD o] := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, min_eq_left hab] at h
    exact (Nat.modEq_iff_dvd' hab).mpr h
  · rw [max_eq_left hab, min_eq_right hab] at h
    exact ((Nat.modEq_iff_dvd' hab).mpr h).symm

theorem modEq_lcm {a b m n : ℕ} (h1 : a ≡ b [MOD m]) (h2 : a ≡ b [MOD n]) : a ≡ b [MOD Nat.lcm m n] := by
  rw [Nat.modEq_iff_dvd, Int.natCast_dvd] at h1 h2 ⊢
  exact Nat.lcm_dvd h1 h2

/-- The second exponents of the pairs `(a₁, a₂)` with `a₂ ≡ r₂ (mod per)` and `o | |a₂ - a₁|`. -/
def A2 (per L r2 o a1 : ℕ) : Finset ℕ :=
  ((Icc 1 L).erase a1).filter fun a2 => a2 % per = r2 ∧ o ∣ max a1 a2 - min a1 a2

theorem card_A2 {per L r1 r2 o a1 : ℕ} (hper : 0 < per) (hr1 : r1 < per) (ho : 0 < o) (ha1 : a1 ∈ Icc 1 L)
    (har1 : a1 % per = r1) :
    ((A2 per L r2 o a1).card : ℝ) ≤
      if Nat.gcd o per ∣ (r2 + per - r1) % per ∧ o ≤ L then
        (L : ℝ) * Nat.gcd o per / (per * o) + 1 else 0 := by
  by_cases hne : (A2 per L r2 o a1).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨hxe, hxr, hxo⟩ := mem_filter.mp hx
    obtain ⟨hxa, hxL⟩ := mem_erase.mp hxe
    have hxL' := mem_Icc.mp hxL
    have ha1' := mem_Icc.mp ha1
    set g := Nat.gcd o per with hg
    -- `g | c`
    have hgc : g ∣ (r2 + per - r1) % per := by
      have e1 : a1 ≡ x [MOD g] := (modEq_of_dvd_dist hxo).of_dvd (Nat.gcd_dvd_left o per)
      have e2 : a1 ≡ r1 [MOD g] := by
        have : a1 ≡ r1 [MOD per] := by unfold Nat.ModEq; rw [har1, Nat.mod_eq_of_lt hr1]
        exact this.of_dvd (Nat.gcd_dvd_right o per)
      have e3 : x ≡ r2 [MOD g] := by
        have hr2 : r2 < per := by rw [← hxr]; exact Nat.mod_lt _ hper
        have : x ≡ r2 [MOD per] := by unfold Nat.ModEq; rw [hxr, Nat.mod_eq_of_lt hr2]
        exact this.of_dvd (Nat.gcd_dvd_right o per)
      have e4 : (r2 + per - r1) % per ≡ r2 + per - r1 [MOD g] := (Nat.mod_modEq _ _).of_dvd (Nat.gcd_dvd_right o per)
      have e5 : r2 + per - r1 + r1 ≡ 0 + r1 [MOD g] := by
        rw [Nat.sub_add_cancel (by omega), zero_add]
        have e6 : r2 + per ≡ r2 [MOD g] := by
          have := Nat.ModEq.add_left r2 ((Nat.modEq_zero_iff_dvd).mpr (Nat.gcd_dvd_right o per))
          rwa [add_zero] at this
        exact e6.trans (e3.symm.trans (e1.symm.trans e2))
      exact (Nat.modEq_zero_iff_dvd).mp (e4.trans (Nat.ModEq.add_right_cancel' r1 e5))
    -- `o ≤ L`
    have hoL : o ≤ L := by
      have hd0 : 0 < max a1 x - min a1 x := by omega
      have := Nat.le_of_dvd hd0 hxo
      omega
    rw [ite_eq_left ⟨hgc, hoL⟩]
    -- pairwise congruent modulo `lcm(per, o)`
    have hM : 0 < Nat.lcm per o := Nat.lcm_pos hper ho
    have hcard := card_le_of_modEq_real (T := A2 per L r2 o a1) (L := L) (M := Nat.lcm per o)
      (fun y hy => (mem_Icc.mp (mem_erase.mp (mem_filter.mp hy).1).2).2)
      (fun y hy z hz => by
        have hyr := (mem_filter.mp hy).2
        have hzr := (mem_filter.mp hz).2
        have h1 : y ≡ z [MOD per] := by unfold Nat.ModEq; rw [hyr.1, hzr.1]
        have h2 : y ≡ z [MOD o] := (modEq_of_dvd_dist hyr.2).symm.trans (modEq_of_dvd_dist hzr.2)
        exact modEq_lcm h1 h2)
    have hlcm : (Nat.lcm per o : ℝ) = per * o / g := by
      have := Nat.gcd_mul_lcm per o
      have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.gcd_pos_of_pos_left per ho
      rw [eq_div_iff hg0.ne', hg, Nat.gcd_comm]
      exact_mod_cast (by rw [mul_comm]; exact this)
    rw [hlcm] at hcard
    have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.gcd_pos_of_pos_left per ho
    have hpo : (0 : ℝ) < per * o := by positivity
    calc ((A2 per L r2 o a1).card : ℝ) ≤ (L : ℝ) / (per * o / g) + 1 := hcard
      _ = (L : ℝ) * g / (per * o) + 1 := by field_simp
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty, Nat.cast_zero]
    split_ifs
    · positivity
    · exact le_refl _

/-- The pair count for one modulus `m`. -/
theorem pairs_le {per L r1 r2 o : ℕ} (hper : 0 < per) (hr1 : r1 < per) (ho : 0 < o) :
    ∑ a1 ∈ (Icc 1 L).filter (· % per = r1), ((A2 per L r2 o a1).card : ℝ) ≤
      ((L : ℝ) / per + 1) * (if Nat.gcd o per ∣ (r2 + per - r1) % per ∧ o ≤ L then
        (L : ℝ) * Nat.gcd o per / (per * o) + 1 else 0) := by
  have hB : 0 ≤ (if Nat.gcd o per ∣ (r2 + per - r1) % per ∧ o ≤ L then
      (L : ℝ) * Nat.gcd o per / (per * o) + 1 else 0) := by split_ifs <;> positivity
  have hT1 : (((Icc 1 L).filter (· % per = r1)).card : ℝ) ≤ (L : ℝ) / per + 1 :=
    card_le_of_modEq_real (M := per) (fun x hx => (mem_Icc.mp (mem_filter.mp hx).1).2)
      (fun x hx y hy => by rw [(mem_filter.mp hx).2, (mem_filter.mp hy).2])
  calc ∑ a1 ∈ (Icc 1 L).filter (· % per = r1), ((A2 per L r2 o a1).card : ℝ)
      ≤ ∑ a1 ∈ (Icc 1 L).filter (· % per = r1), (if Nat.gcd o per ∣ (r2 + per - r1) % per ∧ o ≤ L then
        (L : ℝ) * Nat.gcd o per / (per * o) + 1 else 0) :=
        sum_le_sum fun a1 ha1 => card_A2 hper hr1 ho (mem_filter.mp ha1).1 (mem_filter.mp ha1).2
    _ = (((Icc 1 L).filter (· % per = r1)).card : ℝ) * (if Nat.gcd o per ∣ (r2 + per - r1) % per ∧ o ≤ L then
        (L : ℝ) * Nat.gcd o per / (per * o) + 1 else 0) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((L : ℝ) / per + 1) * _ := mul_le_mul_of_nonneg_right hT1 hB

/-! ## The mean value over one residue pair -/

/-- `Σ_{a₁ ≡ r₁, a₂ ≡ r₂, a₁ ≠ a₂ ≤ L} S'(h) ≤ (L/120 + 1)(L/120) t(c) + (L/120 + 1) E(L)` given a `TBound`-type bound
`t(c)` for the class `c = r₂ - r₁ mod 120`. -/
theorem sing_series_pair {ps : List ℕ} (hd : DistinctPrimes ps) {L r1 r2 : ℕ} (hr1 : r1 < 120) (t : ℝ)
    (hT : ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m ∧ Nat.Coprime m ps.prod) →
      ∑ m ∈ S, tw ((r2 + 120 - r1) % 120) m ≤ t) :
    ∑ a1 ∈ (Icc 1 L).filter (· % 120 = r1), ∑ a2 ∈ ((Icc 1 L).erase a1).filter (· % 120 = r2),
        singP ps (hsh a1 a2) ≤
      ((L : ℝ) / 120 + 1) * ((L : ℝ) / 120) * t + ((L : ℝ) / 120 + 1) * EL ps.prod L := by
  set c := (r2 + 120 - r1) % 120 with hc
  -- expand `S'` and exchange the sums
  have h1 : ∀ a1 ∈ (Icc 1 L).filter (· % 120 = r1), ∀ a2 ∈ ((Icc 1 L).erase a1).filter (· % 120 = r2),
      singP ps (hsh a1 a2) ≤ ∑ m ∈ SL ps.prod L, if m ∣ hsh a1 a2 then fm m else 0 := by
    intro a1 ha1 a2 ha2
    have ha1' := mem_Icc.mp (mem_filter.mp ha1).1
    obtain ⟨hne, ha2L⟩ := mem_erase.mp (mem_filter.mp ha2).1
    have ha2' := mem_Icc.mp ha2L
    exact singP_le_sum hd (hsh_pos (Ne.symm hne)).ne' (hsh_lt (by omega))
  refine (sum_le_sum fun a1 ha1 => sum_le_sum fun a2 ha2 => h1 a1 ha1 a2 ha2).trans ?_
  rw [sum_congr rfl fun a1 _ => sum_comm, sum_comm]
  -- one modulus at a time
  have h2 : ∀ m ∈ SL ps.prod L,
      ∑ a1 ∈ (Icc 1 L).filter (· % 120 = r1), ∑ a2 ∈ ((Icc 1 L).erase a1).filter (· % 120 = r2),
        (if m ∣ hsh a1 a2 then fm m else 0) ≤
      ((L : ℝ) / 120 + 1) * ((L : ℝ) / 120) * (if ordm m ≤ L then tw c m else 0) +
        ((L : ℝ) / 120 + 1) * (if ordm m ≤ L then fm m else 0) := by
    intro m hm
    have hmo : Odd m := (mem_filter.mp hm).2.1
    have ho := ordm_pos hmo
    have e1 : ∀ a1 ∈ (Icc 1 L).filter (· % 120 = r1),
        ∑ a2 ∈ ((Icc 1 L).erase a1).filter (· % 120 = r2), (if m ∣ hsh a1 a2 then fm m else 0) =
          ((A2 120 L r2 (ordm m) a1).card : ℝ) * fm m := by
      intro a1 _
      rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter]
      congr 3
      exact filter_congr fun a2 _ => by rw [dvd_hsh_iff hmo]
    rw [sum_congr rfl e1, ← sum_mul]
    have hp := pairs_le (per := 120) (L := L) (r1 := r1) (r2 := r2) (by norm_num) hr1 ho
    have hfm := fm_nonneg m
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    refine (mul_le_mul_of_nonneg_right hp hfm).trans ?_
    have hc' : (r2 + 120 - r1) % 120 = c := rfl
    rw [hc']
    unfold tw
    have ho' : (0 : ℝ) < ordm m := by exact_mod_cast ho
    by_cases hgc : Nat.gcd (ordm m) 120 ∣ c <;> by_cases hoL : ordm m ≤ L
    · rw [ite_eq_left ⟨hgc, hoL⟩, ite_eq_left hoL, ite_eq_left hgc, ite_eq_left hoL]
      apply le_of_eq
      field_simp
      ring
    · rw [ite_eq_right (fun h => hoL h.2), ite_eq_right hoL, ite_eq_right hoL]; simp
    · rw [ite_eq_right (fun h => hgc h.1), ite_eq_left hoL, ite_eq_right hgc, ite_eq_left hoL]
      simp only [mul_zero, zero_mul, zero_add]
      positivity
    · rw [ite_eq_right (fun h => hgc h.1), ite_eq_right hoL, ite_eq_right hoL]; simp
  refine (sum_le_sum h2).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, ← sum_filter]
  have hS : ∀ m ∈ (SL ps.prod L).filter (fun m => ordm m ≤ L), Odd m ∧ Squarefree m ∧ Nat.Coprime m ps.prod :=
    fun m hm => (mem_filter.mp (mem_filter.mp hm).1).2
  have hcoef : (0 : ℝ) ≤ ((L : ℝ) / 120 + 1) * ((L : ℝ) / 120) := by positivity
  unfold EL
  have := mul_le_mul_of_nonneg_left (hT _ hS) hcoef
  linarith

end Romanoff
