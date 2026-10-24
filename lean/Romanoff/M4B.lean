import Romanoff.M4Spec

/-!
# M4 layer (B): the pair sums at one `N` from ESP (28) and JT Prop. 2

`xuESP : XUESPBound` and `sumXUJT : SumXUJTBound` (statements frozen in `Romanoff.M4Spec`).
* Per class (ESP): a pair `a₁ ≠ a₂ ≤ L` with both exponents in `U_k` has `X_k(a₁, a₂) ≤ pairCountMod N h r l` for
  `h = 2^{max} - 2^{min}` (`X_comm` when `a₁ > a₂`) and the residue `r = k - 2^{max} mod l`, a unit (`resid_coprime`);
  (28) and `sing (l h) = P_l S'(h)` (`sing_mul`) bound it by the ESP factor times `P_l S'(h)`.  Any other pair has
  `X ≤ |ps| = 9`, and there are at most `L²` pairs.
* Summed over the classes (JT): `Σ_k X_k(a₁, a₂) ≤ pairCount N h ≤ (JT factor) sing h`, and
  `sing h = (∏_p 1/(p-2)) #{k : a₁, a₂ mod 120 ∈ U_k} S'(h)` (`sing_shift`); the count is a sum over `k`, and the sums
  over the classes and the pairs are exchanged.
Nothing is evaluated over `range ell`: `ell` enters only through `ell = ellPrimes.prod` (definitional).
-/

open Finset

namespace Romanoff

namespace M4B

theorem ell_eq : ellPrimes.prod = ell := rfl

theorem ell_pos : 0 < ell := prod_pos_of_primes ellPrimes distinctPrimes_ell.2

/-- For `a₁ < a₂ ≤ ⌊log₂ N⌋` the shift `2^{a₂} - 2^{a₁}` lies in `(0, N)`. -/
theorem shift_lt {N a1 a2 : ℕ} (h12 : a1 < a2) (hL : a2 ≤ Nat.log 2 N) :
    0 < 2 ^ a2 - 2 ^ a1 ∧ 2 ^ a2 - 2 ^ a1 < N := by
  have hpow : 2 ^ a1 < 2 ^ a2 := Nat.pow_lt_pow_right (by norm_num) h12
  have hN : N ≠ 0 := by
    rintro rfl
    rw [Nat.log_zero_right] at hL
    omega
  have h1 : 2 ^ a2 ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by norm_num) hL
  have h2 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN
  have h3 : 0 < 2 ^ a1 := Nat.two_pow_pos a1
  omega

theorem hsh_of_lt {a1 a2 : ℕ} (h : a1 < a2) : hsh a1 a2 = 2 ^ a2 - 2 ^ a1 := by
  unfold hsh
  rw [max_eq_right h.le, min_eq_left h.le]

theorem hsh_of_gt {a1 a2 : ℕ} (h : a2 < a1) : hsh a1 a2 = 2 ^ a1 - 2 ^ a2 := by
  unfold hsh
  rw [max_eq_left h.le, min_eq_right h.le]

theorem hsh_comm (a1 a2 : ℕ) : hsh a1 a2 = hsh a2 a1 := by
  unfold hsh
  rw [max_comm, min_comm]

/-- The summand of `WU`. -/
noncomputable def wq (k a1 a2 : ℕ) : ℝ :=
  if a1 % 120 ∈ Uset 120 ellPrimes k ∧ a2 % 120 ∈ Uset 120 ellPrimes k then singP ellPrimes (hsh a1 a2) else 0

theorem wq_comm (k a1 a2 : ℕ) : wq k a1 a2 = wq k a2 a1 := by
  unfold wq
  rw [hsh_comm a1 a2]
  exact if_congr and_comm rfl rfl

theorem WU_eq (L k : ℕ) : WU L k = ∑ a1 ∈ Icc 1 L, ∑ a2 ∈ (Icc 1 L).erase a1, wq k a1 a2 := rfl

theorem XU_eq (N k : ℕ) :
    (XU ell N k : ℝ) = ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1, (X ell N k a1 a2 : ℝ) := by
  unfold XU
  simp only [Nat.cast_sum]

/-- ESP (28) for one pair `a₁ < a₂` with `a₂ mod 120 ∈ U_k`. -/
theorem X_esp {N k : ℕ} (hk : k < ell) {F : ℝ}
    (hESP : ∀ h : ℤ, 0 < h → h < N → ∀ k : ℕ, Nat.Coprime k ell →
      (pairCountMod N h k ell : ℝ) ≤ F * sing (ell * h.natAbs))
    {a1 a2 : ℕ} (h12 : a1 < a2) (hL : a2 ≤ Nat.log 2 N) (hU : a2 % 120 ∈ Uset 120 ellPrimes k) :
    (X ell N k a1 a2 : ℝ) ≤ F * Pl ellPrimes * singP ellPrimes (2 ^ a2 - 2 ^ a1) := by
  obtain ⟨h0, hlt⟩ := shift_lt h12 hL
  have hcop : Nat.Coprime (resid ell k a2) ell := resid_coprime (by norm_num) goodPrimes_ell distinctPrimes_ell hU
  have h1 : (X ell N k a1 a2 : ℝ) ≤ (pairCountMod N ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) (resid ell k a2) ell : ℝ) := by
    exact_mod_cast X_le_pairCountMod ell_pos hk h12
  have h2 := hESP ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) (by exact_mod_cast h0) (by exact_mod_cast hlt) (resid ell k a2) hcop
  have h3 : sing (ell * (2 ^ a2 - 2 ^ a1)) = Pl ellPrimes * singP ellPrimes (2 ^ a2 - 2 ^ a1) :=
    sing_mul goodPrimes_ell distinctPrimes_ell h0.ne'
  rw [Int.natAbs_natCast, h3, ← mul_assoc] at h2
  exact h1.trans h2

/-- Per class, from ESP (28) at `N` with any factor `F`. -/
theorem xu_le {N k : ℕ} (hk : k < ell) {F : ℝ}
    (hESP : ∀ h : ℤ, 0 < h → h < N → ∀ k : ℕ, Nat.Coprime k ell →
      (pairCountMod N h k ell : ℝ) ≤ F * sing (ell * h.natAbs)) :
    (XU ell N k : ℝ) ≤ 9 * (Nat.log 2 N : ℝ) ^ 2 + F * Pl ellPrimes * WU (Nat.log 2 N) k := by
  have hterm : ∀ a1 ∈ Icc 1 (Nat.log 2 N), ∀ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
      (X ell N k a1 a2 : ℝ) ≤
        (if a1 % 120 ∈ Uset 120 ellPrimes k ∧ a2 % 120 ∈ Uset 120 ellPrimes k then (0 : ℝ) else 9) +
          F * Pl ellPrimes * wq k a1 a2 := by
    intro a1 ha1 a2 ha2
    obtain ⟨hne, ha2⟩ := mem_erase.mp ha2
    unfold wq
    split_ifs with hP
    · rw [zero_add]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [X_comm, hsh_of_gt h]
        exact X_esp hk hESP h (mem_Icc.mp ha1).2 hP.1
      · rw [hsh_of_lt h]
        exact X_esp hk hESP h (mem_Icc.mp ha2).2 hP.2
    · rw [mul_zero, add_zero]
      have h9 := X_le_length_of_not_mem (N := N) (by norm_num : 0 < 120) goodPrimes_ell distinctPrimes_ell
        (not_and_or.mp hP)
      rw [ell_eq, show ellPrimes.length = 9 from rfl] at h9
      exact_mod_cast h9
  have hcount : ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
      (if a1 % 120 ∈ Uset 120 ellPrimes k ∧ a2 % 120 ∈ Uset 120 ellPrimes k then (0 : ℝ) else 9) ≤
        9 * (Nat.log 2 N : ℝ) ^ 2 := by
    calc _ ≤ ∑ _a1 ∈ Icc 1 (Nat.log 2 N), ∑ _a2 ∈ Icc 1 (Nat.log 2 N), (9 : ℝ) := by
          refine sum_le_sum fun a1 _ => ?_
          refine (sum_le_sum fun a2 _ => ?_).trans
            (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by norm_num)
          split_ifs <;> norm_num
      _ = 9 * (Nat.log 2 N : ℝ) ^ 2 := by
          simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          ring
  rw [XU_eq, WU_eq, Finset.mul_sum]
  calc ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1, (X ell N k a1 a2 : ℝ)
      ≤ ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
          ((if a1 % 120 ∈ Uset 120 ellPrimes k ∧ a2 % 120 ∈ Uset 120 ellPrimes k then (0 : ℝ) else 9) +
            F * Pl ellPrimes * wq k a1 a2) :=
        sum_le_sum fun a1 ha1 => sum_le_sum fun a2 ha2 => hterm a1 ha1 a2 ha2
    _ = ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
          (if a1 % 120 ∈ Uset 120 ellPrimes k ∧ a2 % 120 ∈ Uset 120 ellPrimes k then (0 : ℝ) else 9) +
        ∑ a1 ∈ Icc 1 (Nat.log 2 N), F * Pl ellPrimes * ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1, wq k a1 a2 := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun a1 _ => ?_
        rw [Finset.mul_sum, ← sum_add_distrib]
    _ ≤ _ := add_le_add hcount le_rfl

/-- JT Prop. 2 for one pair `a₁ < a₂`, summed over the classes. -/
theorem jt_pair {N : ℕ} {G : ℝ}
    (hJT : ∀ h : ℤ, 0 < h → h < N → (pairCount N h : ℝ) ≤ G * sing h.natAbs)
    {a1 a2 : ℕ} (h12 : a1 < a2) (hL : a2 ≤ Nat.log 2 N) :
    ∑ k ∈ range ell, (X ell N k a1 a2 : ℝ) ≤
      G * ((∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) * ∑ k ∈ range ell, wq k a1 a2) := by
  obtain ⟨h0, hlt⟩ := shift_lt h12 hL
  have h1 : ∑ k ∈ range ell, (X ell N k a1 a2 : ℝ) ≤ (pairCount N ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) : ℝ) := by
    exact_mod_cast sum_X_le_pairCount ell_pos h12
  have h2 := hJT ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) (by exact_mod_cast h0) (by exact_mod_cast hlt)
  have h3 := sing_shift (by norm_num : 0 < 120) goodPrimes_ell distinctPrimes_ell h12
  rw [ell_eq] at h3
  rw [Int.natAbs_natCast, h3] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  unfold wq
  rw [hsh_of_lt h12, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  ring

theorem sum_swap (L : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ k ∈ range ell, ∑ a1 ∈ Icc 1 L, ∑ a2 ∈ (Icc 1 L).erase a1, f k a1 a2 =
      ∑ a1 ∈ Icc 1 L, ∑ a2 ∈ (Icc 1 L).erase a1, ∑ k ∈ range ell, f k a1 a2 := by
  rw [sum_comm]
  exact sum_congr rfl fun a1 _ => sum_comm

/-- Summed over the classes, from JT Prop. 2 at `N` with any factor `G`. -/
theorem sum_xu_le {N : ℕ} {G : ℝ}
    (hJT : ∀ h : ℤ, 0 < h → h < N → (pairCount N h : ℝ) ≤ G * sing h.natAbs) :
    ∑ k ∈ range ell, (XU ell N k : ℝ) ≤
      G * (∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) * ∑ k ∈ range ell, WU (Nat.log 2 N) k := by
  have hpair : ∀ a1 ∈ Icc 1 (Nat.log 2 N), ∀ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
      ∑ k ∈ range ell, (X ell N k a1 a2 : ℝ) ≤
        G * ((∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) * ∑ k ∈ range ell, wq k a1 a2) := by
    intro a1 ha1 a2 ha2
    obtain ⟨hne, ha2⟩ := mem_erase.mp ha2
    rcases lt_or_gt_of_ne hne with h | h
    · have e1 : ∑ k ∈ range ell, (X ell N k a1 a2 : ℝ) = ∑ k ∈ range ell, (X ell N k a2 a1 : ℝ) :=
        sum_congr rfl fun k _ => by rw [X_comm]
      have e2 : ∑ k ∈ range ell, wq k a1 a2 = ∑ k ∈ range ell, wq k a2 a1 :=
        sum_congr rfl fun k _ => wq_comm k a1 a2
      rw [e1, e2]
      exact jt_pair hJT h (mem_Icc.mp ha1).2
    · exact jt_pair hJT h (mem_Icc.mp ha2).2
  calc ∑ k ∈ range ell, (XU ell N k : ℝ)
      = ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
          ∑ k ∈ range ell, (X ell N k a1 a2 : ℝ) := by
        simp only [XU_eq]
        exact sum_swap _ _
    _ ≤ ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1,
          G * ((∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) * ∑ k ∈ range ell, wq k a1 a2) :=
        sum_le_sum fun a1 ha1 => sum_le_sum fun a2 ha2 => hpair a1 ha1 a2 ha2
    _ = G * (∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) * ∑ k ∈ range ell, WU (Nat.log 2 N) k := by
        simp only [WU_eq, ← Finset.mul_sum]
        rw [sum_swap, mul_assoc]

end M4B

open M4B in
theorem xuESP : XUESPBound := fun _ _ _ hESP _ hk => xu_le hk hESP

open M4B in
theorem sumXUJT : SumXUJTBound := fun _ _ _ hJT => sum_xu_le hJT

end Romanoff
