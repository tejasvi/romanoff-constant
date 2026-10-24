import Romanoff.Classes

/-!
# The singular series at the shifts `h = 2^{a₂} - 2^{a₁}`

`S'(h) = ∏_{p | h, p > 2, p ∉ ps} (p-1)/(p-2)` (the part of `sing h` coprime to `2 l`), `P_l = ∏_{p ∈ ps} (p-1)/(p-2)`.
* `sing (l h) = P_l S'(h)` (the per-class factor in ESP (28));
* `sing h = (∏_{p ∈ ps} 1/(p-2)) #{k < l : a₁, a₂ mod per ∈ U_k} S'(h)`, because `p | h` iff `2^{a₁} ≡ 2^{a₂} (mod p)`
  and `#{k} = ∏_p (p - 1 - [p ∤ h])` (CRT).  Summed over `k` this turns JT's total bound into the evaluator's budget.
-/

open Finset

namespace Romanoff

/-- `S'(h) = ∏_{p | h, p > 2, p ∉ ps} (p-1)/(p-2)`. -/
noncomputable def singP (ps : List ℕ) (h : ℕ) : ℝ :=
  ∏ p ∈ h.primeFactors.filter (fun p => 2 < p ∧ p ∉ ps), ((p : ℝ) - 1) / (p - 2)

/-- `P_l = ∏_{p ∈ ps} (p-1)/(p-2)`. -/
noncomputable def Pl (ps : List ℕ) : ℝ := ∏ p ∈ ps.toFinset, ((p : ℝ) - 1) / (p - 2)

theorem singP_nonneg (ps : List ℕ) (h : ℕ) : 0 ≤ singP ps h := by
  unfold singP
  refine prod_nonneg fun p hp => ?_
  have h2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1
  exact div_nonneg (by linarith) (by linarith)

theorem prod_eq_toFinset_prod {ps : List ℕ} (hd : DistinctPrimes ps) : ps.prod = ∏ p ∈ ps.toFinset, p := by
  rw [List.prod_toFinset _ hd.1, List.map_id']

theorem primeFactors_prod_list {ps : List ℕ} (hd : DistinctPrimes ps) : ps.prod.primeFactors = ps.toFinset := by
  rw [prod_eq_toFinset_prod hd]
  exact Nat.primeFactors_prod fun p hp => hd.2 p (List.mem_toFinset.mp hp)

/-- `sing (l h) = P_l S'(h)`. -/
theorem sing_mul {per : ℕ} {ps : List ℕ} (hg : GoodPrimes per ps) (hd : DistinctPrimes ps) {h : ℕ} (hh : h ≠ 0) :
    sing (ps.prod * h) = Pl ps * singP ps h := by
  have hl0 : ps.prod ≠ 0 := (prod_pos_of_primes ps hd.2).ne'
  have hps2 : ∀ p ∈ ps, 2 < p := fun p hp => lt_of_le_of_ne (hd.2 p hp).two_le (fun e => (hg p hp).2.1 e.symm)
  unfold sing Pl singP
  rw [Nat.primeFactors_mul hl0 hh, primeFactors_prod_list hd]
  have hset : (ps.toFinset ∪ h.primeFactors).filter (2 < ·) =
      ps.toFinset ∪ h.primeFactors.filter (fun p => 2 < p ∧ p ∉ ps) := by
    ext p
    simp only [mem_filter, mem_union, List.mem_toFinset]
    constructor
    · rintro ⟨hp | hp, h2⟩
      · exact Or.inl hp
      · by_cases hq : p ∈ ps
        · exact Or.inl hq
        · exact Or.inr ⟨hp, h2, hq⟩
    · rintro (hp | ⟨hp, h2, _⟩)
      · exact ⟨Or.inl hp, hps2 p hp⟩
      · exact ⟨Or.inr hp, h2⟩
  rw [hset, prod_union]
  rw [disjoint_left]
  intro p hp hp'
  exact (mem_filter.mp hp').2.2 (List.mem_toFinset.mp hp)

/-- For `p ∈ ps` and `a₁ ≤ a₂`: `p | 2^{a₂} - 2^{a₁}` iff `2^{a₁} ≡ 2^{a₂} (mod p)`. -/
theorem dvd_shift_iff (p a1 a2 : ℕ) (h12 : a1 ≤ a2) : p ∣ 2 ^ a2 - 2 ^ a1 ↔ 2 ^ a1 % p = 2 ^ a2 % p :=
  (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) h12)).symm

/-- `sing h = (∏_p 1/(p-2)) #{k < l : a₁, a₂ mod per ∈ U_k} S'(h)` for `h = 2^{a₂} - 2^{a₁}`, `a₁ < a₂`. -/
theorem sing_shift {per : ℕ} (hper : 0 < per) {ps : List ℕ} (hg : GoodPrimes per ps) (hd : DistinctPrimes ps)
    {a1 a2 : ℕ} (h12 : a1 < a2) :
    sing (2 ^ a2 - 2 ^ a1) = (∏ p ∈ ps.toFinset, 1 / ((p : ℝ) - 2)) *
      (((range ps.prod).filter fun k => a1 % per ∈ Uset per ps k ∧ a2 % per ∈ Uset per ps k).card : ℝ) *
      singP ps (2 ^ a2 - 2 ^ a1) := by
  set h := 2 ^ a2 - 2 ^ a1 with hhdef
  have hpow : 2 ^ a1 < 2 ^ a2 := Nat.pow_lt_pow_right (by norm_num) h12
  have hh : h ≠ 0 := by omega
  have hps2 : ∀ p ∈ ps, 2 < p := fun p hp => lt_of_le_of_ne (hd.2 p hp).two_le (fun e => (hg p hp).2.1 e.symm)
  -- the CRT count, in `ℝ`
  have hA : (((range ps.prod).filter fun k => a1 % per ∈ Uset per ps k ∧ a2 % per ∈ Uset per ps k).card : ℝ) =
      ∏ p ∈ ps.toFinset, ((p : ℝ) - if 2 ^ a1 % p = 2 ^ a2 % p then 1 else 2) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (card_pair_classes hper hg hd a1 a2)
    simp only [Rat.cast_natCast, Rat.cast_list_prod, List.map_map] at this
    rw [this, List.prod_toFinset _ hd.1]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply]
    push_cast
    split_ifs <;> norm_num
  rw [hA, ← prod_mul_distrib]
  unfold sing singP
  -- split `sing h` into the primes of `ps` and the rest
  rw [← prod_filter_mul_prod_filter_not (h.primeFactors.filter (2 < ·)) (fun p => p ∈ ps)]
  rw [filter_filter, filter_filter]
  congr 1
  · -- the primes of `ps`
    have hset : h.primeFactors.filter (fun p => 2 < p ∧ p ∈ ps) = ps.toFinset.filter (fun p => p ∣ h) := by
      ext p
      simp only [mem_filter, Nat.mem_primeFactors, List.mem_toFinset]
      constructor
      · rintro ⟨⟨_, hdvd, _⟩, _, hp⟩; exact ⟨hp, hdvd⟩
      · rintro ⟨hp, hdvd⟩; exact ⟨⟨hd.2 p hp, hdvd, hh⟩, hps2 p hp, hp⟩
    rw [hset, prod_filter]
    refine prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hps2 p (List.mem_toFinset.mp hp)
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    rw [hhdef]
    by_cases hdv : p ∣ 2 ^ a2 - 2 ^ a1
    · rw [ite_eq_left hdv, ite_eq_left ((dvd_shift_iff p a1 a2 h12.le).mp hdv)]
      field_simp
    · rw [ite_eq_right hdv, ite_eq_right (fun e => hdv ((dvd_shift_iff p a1 a2 h12.le).mpr e))]
      field_simp

end Romanoff
