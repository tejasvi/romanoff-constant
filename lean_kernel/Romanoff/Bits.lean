import Mathlib
import RCert.Patt

/-!
# Bit masks of exponents: `maskP`, `rot1`, `canon`

`maskP per p r` has bit `e` iff `e < per ∧ 2^e % p = r`; `rot1` moves bit `e` to `e + 1 mod per` (on `per`-bit masks);
`maskP (2r mod p) = rot1 (maskP r)` when `2^per ≡ 1 (mod p)`, `p` odd; `canon x` is a rotation of `x`.
-/

namespace Romanoff

open R45

theorem testBit_foldl_or (per : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∀ (n a i : ℕ), ((List.range n).foldl (fun acc e => if P e then acc ||| (1 <<< e) else acc) a).testBit i =
      (a.testBit i || (decide (i < n) && decide (P i)))
  | 0, a, i => by simp
  | n + 1, a, i => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := testBit_foldl_or per P n a i
    by_cases hP : P n
    · rw [ite_eq_left hP, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      rcases Nat.lt_trichotomy i n with h | h | h
      · simp [h, show i < n + 1 by omega, show n ≠ i by omega]
      · subst h; simp [hP]
      · simp [show ¬ i < n by omega, show ¬ i < n + 1 by omega, show n ≠ i by omega]
    · rw [ite_eq_right hP, ih]
      rcases Nat.lt_trichotomy i n with h | h | h
      · simp [h, show i < n + 1 by omega]
      · subst h; simp [hP]
      · simp [show ¬ i < n by omega, show ¬ i < n + 1 by omega]

theorem maskP_testBit (per p r e : ℕ) :
    (maskP per p r).testBit e = (decide (e < per) && decide (2 ^ e % p = r)) := by
  unfold maskP
  rw [testBit_foldl_or per (fun e => 2 ^ e % p = r) per 0 e]
  simp

theorem lt_two_pow_of_testBit {x per : ℕ} (h : ∀ i, x.testBit i = true → i < per) : x < 2 ^ per :=
  Nat.lt_pow_two_of_testBit x fun i hi => by
    by_contra hc
    have := h i (by simpa using hc)
    omega

theorem testBit_eq_false_of_lt_pow {x per i : ℕ} (hx : x < 2 ^ per) (hi : per ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem maskP_lt (per p r : ℕ) : maskP per p r < 2 ^ per :=
  lt_two_pow_of_testBit fun i hi => by
    rw [maskP_testBit] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.1

theorem full_eq (per : ℕ) : full per = 2 ^ per - 1 := rfl

theorem rot1_testBit {per : ℕ} (hper : 0 < per) {x : ℕ} (hx : x < 2 ^ per) (e : ℕ) :
    (rot1 per x).testBit e = (decide (e < per) && x.testBit ((e + per - 1) % per)) := by
  unfold rot1
  rw [Nat.testBit_and, full_eq, Nat.testBit_two_pow_sub_one, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases he : e < per
  · simp only [he, decide_true, Bool.and_true, Bool.true_and]
    rcases Nat.eq_zero_or_pos e with rfl | he0
    · simp only [ge_iff_le, Nat.le_zero, one_ne_zero, decide_false, Bool.false_and, Bool.false_or, Nat.add_zero,
        zero_add]
      rw [Nat.mod_eq_of_lt (by omega)]
    · have h1 : (e + per - 1) % per = e - 1 := by
        rw [show e + per - 1 = (e - 1) + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1, testBit_eq_false_of_lt_pow (i := per - 1 + e) hx (by omega)]
      simp [show 1 ≤ e by omega]
  · simp [he]

theorem rot1_lt (per x : ℕ) : rot1 per x < 2 ^ per := by
  unfold rot1
  exact Nat.and_lt_two_pow _ (by rw [full_eq]; exact Nat.sub_lt (Nat.two_pow_pos per) one_pos)

theorem rot1_or {per : ℕ} (hper : 0 < per) {a b : ℕ} (ha : a < 2 ^ per) (hb : b < 2 ^ per) :
    rot1 per (a ||| b) = rot1 per a ||| rot1 per b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [rot1_testBit hper (Nat.or_lt_two_pow ha hb), rot1_testBit hper ha, rot1_testBit hper hb,
    Nat.testBit_or]
  cases decide (i < per) <;> simp

/-- `maskP (2r mod p) = rot1 (maskP r)` when `2^per ≡ 1 (mod p)` and `p` is odd. -/
theorem maskP_two_mul {per p : ℕ} (hper : 0 < per) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ^ per % p = 1)
    {r : ℕ} (hr : r < p) : maskP per p (2 * r % p) = rot1 per (maskP per p r) := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [maskP_testBit, rot1_testBit hper (maskP_lt per p r), maskP_testBit]
  by_cases he : e < per
  · simp only [he, decide_true, Bool.true_and]
    have hm : (e + per - 1) % per < per := Nat.mod_lt _ hper
    simp only [hm, decide_true, Bool.true_and, decide_eq_decide]
    -- 2^e ≡ 2 r  ⟺  2^((e - 1) mod per) ≡ r  (mod p)
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have key : 2 ^ e % p = 2 * 2 ^ ((e + per - 1) % per) % p := by
      have h3 : 2 * 2 ^ ((e + per - 1) % per) = 2 ^ ((e + per - 1) % per + 1) := by ring
      rw [h3]
      rcases Nat.eq_zero_or_pos e with rfl | he0
      · rw [show (0 + per - 1) % per + 1 = per by rw [Nat.mod_eq_of_lt (by omega)]; omega, h2, pow_zero]
        exact Nat.mod_eq_of_lt hp.one_lt
      · rw [show (e + per - 1) % per + 1 = e by
          rw [show e + per - 1 = (e - 1) + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega]
    rw [key]
    constructor
    · intro h
      -- 2 * x ≡ 2 * r  ⇒  x ≡ r
      have h' : 2 * 2 ^ ((e + per - 1) % per) ≡ 2 * r [MOD p] := by
        unfold Nat.ModEq; rw [h]
      have := Nat.ModEq.cancel_left_of_coprime (by rwa [Nat.coprime_comm] at hcop) h'
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hr]
    · intro h
      rw [Nat.mul_mod, h]
      conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt hr]
  · simp [he]

theorem iterate_rot1_lt (per : ℕ) : ∀ (t x : ℕ), x < 2 ^ per → (rot1 per)^[t] x < 2 ^ per
  | 0, x, hx => hx
  | t + 1, x, _ => by rw [Function.iterate_succ_apply']; exact rot1_lt per _

/-- `canon x` is one of the rotations of `x`. -/
theorem canon_rot (per x : ℕ) : ∃ t, canon per x = (rot1 per)^[t] x := by
  have key : ∀ n : ℕ, ∃ t, ((List.range n).foldl (fun (bc : ℕ × ℕ) _ => let y := rot1 per bc.2; (min bc.1 y, y))
      (x, x)).1 = (rot1 per)^[t] x ∧
      ((List.range n).foldl (fun (bc : ℕ × ℕ) _ => let y := rot1 per bc.2; (min bc.1 y, y)) (x, x)).2 =
        (rot1 per)^[n] x := by
    intro n
    induction n with
    | zero => exact ⟨0, rfl, rfl⟩
    | succ n ih =>
      obtain ⟨t, h1, h2⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only
      rw [h1, h2]
      rcases min_choice ((rot1 per)^[t] x) (rot1 per ((rot1 per)^[n] x)) with h | h
      · exact ⟨t, h, by rw [Function.iterate_succ_apply']⟩
      · exact ⟨n + 1, by rw [h, Function.iterate_succ_apply'], by rw [Function.iterate_succ_apply']⟩
  obtain ⟨t, h, _⟩ := key per
  exact ⟨t, h⟩

theorem canon_lt {per x : ℕ} (hx : x < 2 ^ per) : canon per x < 2 ^ per := by
  obtain ⟨t, h⟩ := canon_rot per x
  rw [h]; exact iterate_rot1_lt per t x hx

/-- A function invariant under `rot1` on `per`-bit masks is invariant under `canon`. -/
theorem canon_inv {per : ℕ} {G : ℕ → ℚ} (hG : ∀ x, x < 2 ^ per → G (rot1 per x) = G x) {x : ℕ}
    (hx : x < 2 ^ per) : G (canon per x) = G x := by
  obtain ⟨t, h⟩ := canon_rot per x
  rw [h]
  clear h
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', hG _ (iterate_rot1_lt per t x hx), ih]

end Romanoff
