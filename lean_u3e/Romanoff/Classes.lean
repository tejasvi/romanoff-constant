import Romanoff.OrbSound
import Romanoff.Moments

/-!
# Residue classes modulo `l = ∏ ps`: the sets `U_k`, the evaluator's per-class data, and the CRT count

`U_k = {e < per : 2^e ≢ k (mod p) for every p ∈ ps}` (the exponents `e` with `k - 2^e` a unit mod `l`).
* The evaluator's class data are those of `U_k`: `phiCls P per (exmaskL per ps 0 k)` is `0` if `U_k = ∅`, and otherwise
  the per-class minimum with `s = |U_k|`, `n(c) = #{e ∈ U_k : e + c mod per ∈ U_k}`.
* CRT count: `#{k < l : r₁, r₂ ∈ U_k} = ∏_{p ∈ ps} (p - 1 - [2^{r₁} ≢ 2^{r₂} (mod p)])`.
* For `h = 2^{a₂} - 2^{a₁}` (`a₁ < a₂`): `sing h = (∏_p 1/(p-2)) #{k : a₁, a₂ mod per ∈ U_k} S'(h)` and
  `sing (l h) = P_l S'(h)`, where `S'(h) = ∏_{p | h, p > 2, p ∉ ps} (p-1)/(p-2)`.
-/

open Finset R45

namespace Romanoff

/-- `U_k`: the exponents `e < per` with `2^e ≢ k` modulo every `p ∈ ps`. -/
def Uset (per : ℕ) (ps : List ℕ) (k : ℕ) : Finset ℕ := (range per).filter fun e => ∀ p ∈ ps, 2 ^ e % p ≠ k % p

/-- `n_k(c) = #{e ∈ U_k : (e + c) mod per ∈ U_k}`. -/
def nC (per : ℕ) (ps : List ℕ) (k c : ℕ) : ℕ := ((Uset per ps k).filter fun e => (e + c) % per ∈ Uset per ps k).card

theorem testBit_exmaskL (per : ℕ) : ∀ (ps : List ℕ) (acc k e : ℕ),
    (exmaskL per ps acc k).testBit e = true ↔ (acc.testBit e = true ∨ (e < per ∧ ∃ p ∈ ps, 2 ^ e % p = k % p))
  | [], acc, k, e => by simp [exmaskL]
  | p :: ps, acc, k, e => by
    rw [exmaskL, testBit_exmaskL per ps, Nat.testBit_or, maskP_testBit]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem exmaskL_lt (per : ℕ) (ps : List ℕ) (k : ℕ) : exmaskL per ps 0 k < 2 ^ per := by
  apply lt_two_pow_of_testBit
  intro i hi
  rw [testBit_exmaskL] at hi
  rcases hi with h | h
  · simp at h
  · exact h.1

/-- The complement mask of class `k`. -/
def umask (per : ℕ) (ps : List ℕ) (k : ℕ) : ℕ := full per ^^^ exmaskL per ps 0 k

theorem testBit_umask (per : ℕ) (ps : List ℕ) (k e : ℕ) :
    (umask per ps k).testBit e = true ↔ e ∈ Uset per ps k := by
  have h1 := testBit_exmaskL per ps 0 k e
  rw [Nat.zero_testBit] at h1
  unfold umask Uset
  rw [Nat.testBit_xor, testBit_full, mem_filter, mem_range]
  cases hb : (exmaskL per ps 0 k).testBit e
  · rw [hb] at h1
    by_cases he : e < per
    · have : ∀ p ∈ ps, 2 ^ e % p ≠ k % p := fun p hp h =>
        absurd (h1.mpr (Or.inr ⟨he, p, hp, h⟩)) (by simp)
      simpa [he] using this
    · simp [he]
  · rw [hb] at h1
    rcases h1.mp rfl with h | ⟨he, p, hp, hpe⟩
    · simp at h
    · simp only [he, decide_true, Bool.true_xor, Bool.not_true, Bool.false_eq_true, true_and, false_iff]
      exact fun h => h p hp hpe

theorem umask_lt (per : ℕ) (ps : List ℕ) (k : ℕ) : umask per ps k < 2 ^ per :=
  full_xor_lt per _ (exmaskL_lt per ps k)

theorem popcount_umask (per : ℕ) (ps : List ℕ) (k : ℕ) : popcount per (umask per ps k) = (Uset per ps k).card := by
  rw [popcount_eq]
  congr 1
  ext e
  rw [mem_filter, testBit_umask]
  exact ⟨fun h => h.2, fun h => ⟨(mem_filter.mp h).1, h⟩⟩

theorem nShift_umask (per : ℕ) (ps : List ℕ) (k c : ℕ) (hc : c < per) :
    (nShift per (umask per ps k)).getD c 0 = nC per ps k c := by
  rw [nShift_getD per _ c hc, nC]
  congr 1
  ext e
  simp only [mem_filter, Bool.and_eq_true, testBit_umask]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨(mem_filter.mp h.1).1, h.1, h.2⟩⟩

theorem umask_eq_zero_iff (per : ℕ) (ps : List ℕ) (k : ℕ) : umask per ps k = 0 ↔ Uset per ps k = ∅ := by
  rw [eq_zero_iff_popcount (umask_lt per ps k), popcount_umask, card_eq_zero]

/-- `Σ_c n(c) t(c)` as a finite sum (lists of length `per`). -/
theorem dotNQ_eq : ∀ (n : List ℕ) (t : List ℚ) (a : ℚ), n.length = t.length →
    (n.zip t).foldl (fun acc nt => acc + (nt.1 : ℚ) * nt.2) a =
      a + ∑ c ∈ range n.length, ((n.getD c 0 : ℕ) : ℚ) * t.getD c 0
  | [], _, a, _ => by simp
  | x :: n, [], a, h => by simp at h
  | x :: n, y :: t, a, h => by
    rw [List.zip_cons_cons, List.foldl_cons, dotNQ_eq n t _ (by simpa using h), List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The evaluator's value on class `k`. -/
theorem phiCls_exmaskL (P : Par) (per : ℕ) (ps : List ℕ) (k : ℕ) (ht : P.teff.length = per) :
    phiCls P per (exmaskL per ps 0 k) =
      if Uset per ps k = ∅ then 0
      else minQ P (Uset per ps k).card (P.cap * P.kap * ∑ c ∈ range per, (nC per ps k c : ℚ) * P.teff.getD c 0) := by
  unfold phiCls
  rw [← umask]
  by_cases h : Uset per ps k = ∅
  · rw [ite_eq_left ((umask_eq_zero_iff per ps k).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((umask_eq_zero_iff per ps k).mp h')), ite_eq_right h, popcount_umask]
    congr 1
    have hsum : ∑ c ∈ range per, (((nShift per (umask per ps k)).getD c 0 : ℕ) : ℚ) * P.teff.getD c 0 =
        ∑ c ∈ range per, (nC per ps k c : ℚ) * P.teff.getD c 0 :=
      sum_congr rfl fun c hc => by rw [nShift_umask per ps k c (mem_range.mp hc)]
    unfold ymaxQ dotNQ
    rw [dotNQ_eq _ _ 0 (by rw [nShift_length, ht]), zero_add, nShift_length, hsum]

/-- Ordered pairs in `U × U` grouped by the difference `c = r₂ - r₁ mod per`. -/
theorem sum_pairs_eq_sum_nC {per : ℕ} (hper : 0 < per) (ps : List ℕ) (k : ℕ) (F : ℕ → ℝ) :
    ∑ r1 ∈ Uset per ps k, ∑ r2 ∈ Uset per ps k, F ((r2 + per - r1) % per) =
      ∑ c ∈ range per, (nC per ps k c : ℝ) * F c := by
  have hU : ∀ e ∈ Uset per ps k, e < per := fun e he => mem_range.mp (mem_filter.mp he).1
  have h1 : ∀ c ∈ range per, (nC per ps k c : ℝ) * F c =
      ∑ r1 ∈ Uset per ps k, if (r1 + c) % per ∈ Uset per ps k then F c else 0 := by
    intro c _
    rw [nC, ← sum_filter, sum_const, nsmul_eq_mul]
  rw [sum_congr rfl h1]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun r1 hr1 => ?_
  rw [← sum_filter]
  symm
  refine sum_nbij' (fun c => (r1 + c) % per) (fun r2 => (r2 + per - r1) % per) ?_ ?_ ?_ ?_ ?_
  · intro c hc; exact (mem_filter.mp hc).2
  · intro r2 hr2
    have h2 := hU r2 hr2
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hper), ?_⟩
    have h1 := hU r1 hr1
    have : (r1 + (r2 + per - r1) % per) % per = r2 := by
      rw [Nat.add_mod_mod, show r1 + (r2 + per - r1) = r2 + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
    rw [this]; exact hr2
  · intro c hc
    have hc' := mem_range.mp (mem_filter.mp hc).1
    have h1 := hU r1 hr1
    show ((r1 + c) % per + per - r1) % per = c
    rcases lt_or_ge (r1 + c) per with h | h
    · rw [Nat.mod_eq_of_lt h, show r1 + c + per - r1 = c + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hc']
    · have : (r1 + c) % per = r1 + c - per := by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      rw [this, show r1 + c - per + per - r1 = c by omega, Nat.mod_eq_of_lt hc']
  · intro r2 hr2
    have h2 := hU r2 hr2
    have h1 := hU r1 hr1
    show (r1 + (r2 + per - r1) % per) % per = r2
    rw [Nat.add_mod_mod, show r1 + (r2 + per - r1) = r2 + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
  · intro c hc
    have hc' := mem_range.mp (mem_filter.mp hc).1
    have h1 := hU r1 hr1
    congr 1
    rcases lt_or_ge (r1 + c) per with h | h
    · rw [Nat.mod_eq_of_lt h, show r1 + c + per - r1 = c + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hc']
    · have : (r1 + c) % per = r1 + c - per := by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      rw [this, show r1 + c - per + per - r1 = c by omega, Nat.mod_eq_of_lt hc']

/-! ## Exponents in a class -/

theorem two_pow_mod_per {per p : ℕ} (h2 : 2 ^ per % p = 1) (a : ℕ) : 2 ^ a % p = 2 ^ (a % per) % p := by
  have hp1 : p ≠ 1 := by rintro rfl; rw [Nat.mod_one] at h2; exact absurd h2 (by norm_num)
  have h : 2 ^ per ≡ 1 [MOD p] := by unfold Nat.ModEq; rw [h2, Nat.one_mod_eq_one.mpr hp1]
  have := (h.pow (a / per)).mul_right (2 ^ (a % per))
  rw [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at this
  exact this

/-- `a mod per ∈ U_k` iff `2^a ≢ k` modulo every `p ∈ ps`. -/
theorem mem_Uset_mod {per : ℕ} (hper : 0 < per) {ps : List ℕ} (hg : GoodPrimes per ps) (k a : ℕ) :
    a % per ∈ Uset per ps k ↔ ∀ p ∈ ps, 2 ^ a % p ≠ k % p := by
  unfold Uset
  rw [mem_filter, mem_range]
  constructor
  · rintro ⟨_, h⟩ p hp; rw [two_pow_mod_per (hg p hp).2.2 a]; exact h p hp
  · intro h; exact ⟨Nat.mod_lt _ hper, fun p hp => by rw [← two_pow_mod_per (hg p hp).2.2 a]; exact h p hp⟩

/-! ## The CRT count -/

theorem prod_pos_of_primes : ∀ (ps : List ℕ), (∀ p ∈ ps, p.Prime) → 0 < ps.prod
  | [], _ => by simp
  | p :: ps, h => by
    rw [List.prod_cons]
    exact Nat.mul_pos (h p (by simp)).pos (prod_pos_of_primes ps fun q hq => h q (by simp [hq]))

theorem dvd_prod_of_mem : ∀ {ps : List ℕ} {q : ℕ}, q ∈ ps → q ∣ ps.prod
  | p :: ps, q, h => by
    rw [List.prod_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact dvd_mul_right _ _
    · exact Dvd.dvd.mul_left (dvd_prod_of_mem h) _

/-- `#{k < ∏ ps : ∀ p, B p (k mod p)} = ∏_p #{r < p : B p r}` (as rationals). -/
theorem crt_count (B : ℕ → ℕ → Prop) [∀ p, DecidablePred (B p)] :
    ∀ (ps : List ℕ), DistinctPrimes ps →
      ∑ k ∈ range ps.prod, (if ∀ p ∈ ps, B p (k % p) then (1 : ℚ) else 0) =
        (ps.map fun p => ∑ r ∈ range p, if B p r then (1 : ℚ) else 0).prod
  | [], _ => by simp
  | p :: ps, ⟨hnd, hpr⟩ => by
    have hp := hpr p (by simp)
    have hnd' := List.nodup_cons.mp hnd
    have hps : DistinctPrimes ps := ⟨hnd'.2, fun q hq => hpr q (by simp [hq])⟩
    have hcop : Nat.Coprime p ps.prod :=
      coprime_prod hp ps fun q hq => ⟨hpr q (by simp [hq]), fun h => hnd'.1 (h ▸ hq)⟩
    have hm : 0 < ps.prod := prod_pos_of_primes ps hps.2
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← crt_count B ps hps]
    have h1 : ∀ k, (if ∀ q ∈ p :: ps, B q (k % q) then (1 : ℚ) else 0) =
        (if B p (k % p) then (1 : ℚ) else 0) * (if ∀ q ∈ ps, B q ((k % ps.prod) % q) then (1 : ℚ) else 0) := by
      intro k
      have : ∀ q ∈ ps, (k % ps.prod) % q = k % q := fun q hq => Nat.mod_mod_of_dvd k (dvd_prod_of_mem hq)
      by_cases hb : B p (k % p) <;> by_cases ha : ∀ q ∈ ps, B q (k % q)
      · have hall : ∀ q ∈ p :: ps, B q (k % q) := fun q hq => by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hb
          · exact ha q hq
        rw [ite_eq_left hall, ite_eq_left hb, ite_eq_left (fun q hq => by rw [this q hq]; exact ha q hq), mul_one]
      · have hall : ¬ ∀ q ∈ p :: ps, B q (k % q) := fun h => ha fun q hq => h q (List.mem_cons_of_mem _ hq)
        rw [ite_eq_right hall, ite_eq_left hb, ite_eq_right (fun h => ha fun q hq => by rw [← this q hq]; exact h q hq), mul_zero]
      · have hall : ¬ ∀ q ∈ p :: ps, B q (k % q) := fun h => hb (h p List.mem_cons_self)
        rw [ite_eq_right hall, ite_eq_right hb, zero_mul]
      · have hall : ¬ ∀ q ∈ p :: ps, B q (k % q) := fun h => hb (h p List.mem_cons_self)
        rw [ite_eq_right hall, ite_eq_right hb, zero_mul]
    rw [sum_congr rfl fun k _ => h1 k]
    rw [sum_range_mul_crt hcop hp.pos hm (fun a b => (if B p a then (1 : ℚ) else 0) *
      (if ∀ q ∈ ps, B q (b % q) then (1 : ℚ) else 0)), sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]

/-- `#{r < p : r ≠ x, r ≠ y}` for `x, y < p`. -/
theorem count_ne_two {p x y : ℕ} (hx : x < p) (hy : y < p) :
    ∑ r ∈ range p, (if r ≠ x ∧ r ≠ y then (1 : ℚ) else 0) = (p : ℚ) - if x = y then 1 else 2 := by
  rw [sum_boole]
  have : (range p).filter (fun r => r ≠ x ∧ r ≠ y) = ((range p).erase x).erase y := by
    ext r; simp only [mem_filter, mem_erase, mem_range]; tauto
  rw [this]
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl, erase_eq_of_notMem (by simp), card_erase_of_mem (mem_range.mpr hx), card_range]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
  · rw [ite_eq_right hxy, card_erase_of_mem (mem_erase.mpr ⟨fun h => hxy h.symm, mem_range.mpr hy⟩),
      card_erase_of_mem (mem_range.mpr hx), card_range]
    have : 2 ≤ p := by omega
    push_cast [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 1 ≤ p - 1)]; ring

/-- `A(a₁, a₂) = #{k < l : a₁ mod per, a₂ mod per ∈ U_k}` as a product over `ps`. -/
theorem card_pair_classes {per : ℕ} (hper : 0 < per) {ps : List ℕ} (hg : GoodPrimes per ps) (hd : DistinctPrimes ps)
    (a1 a2 : ℕ) :
    (((range ps.prod).filter fun k => a1 % per ∈ Uset per ps k ∧ a2 % per ∈ Uset per ps k).card : ℚ) =
      (ps.map fun (p : ℕ) => (p : ℚ) - if 2 ^ a1 % p = 2 ^ a2 % p then 1 else 2).prod := by
  have h1 : ∀ k, (a1 % per ∈ Uset per ps k ∧ a2 % per ∈ Uset per ps k) ↔
      ∀ p ∈ ps, (k % p ≠ 2 ^ a1 % p ∧ k % p ≠ 2 ^ a2 % p) := by
    intro k
    rw [mem_Uset_mod hper hg, mem_Uset_mod hper hg]
    constructor
    · rintro ⟨h1, h2⟩ p hp; exact ⟨fun h => h1 p hp h.symm, fun h => h2 p hp h.symm⟩
    · intro h; exact ⟨fun p hp e => (h p hp).1 e.symm, fun p hp e => (h p hp).2 e.symm⟩
  rw [← sum_boole]
  rw [sum_congr rfl fun k _ => if_congr (h1 k) rfl rfl]
  rw [crt_count (fun p r => r ≠ 2 ^ a1 % p ∧ r ≠ 2 ^ a2 % p) ps hd]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp0 := (hd.2 p hp).pos
  exact count_ne_two (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0)

end Romanoff
