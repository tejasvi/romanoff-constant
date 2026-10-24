import Romanoff.OrbSound
import Romanoff.G.Tables
import RCert.G.Ev

/-!
# U3g/V4g stage 2: the row quantities at a period `P` (27720 for the rows, 360 for the core rows)

For an exclusion mask `X` and a period `P` (the row `U = {e < P : e ∉ X}`):
* `cntP P X h a = N^h_a = #{e ∈ U : e ≡ a (h)}` (as a sum of indicators), `SP P X g = Σ_{a < g} N^g_a ^ 2`;
* `cntP_split`: `N^h_a = Σ_{t < q} N^{hq}_{a + h t}`; `SP_le`: `g S_g ≤ P |U|` (`g ∣ P`);
* `dotP_double`: `Σ_a N^g_a(X1) N^g_a(X2) = Σ_{e, e' < P, e ≡ e' (g)} [e ∉ X1] [e' ∉ X2]` (and `SP_double`);
* at `P = 27720`: `popcount_fx`: `|U| = N^1_0`, `ngOf_nShift`: `N_g(n_U) = S_g` (`g ∣ 27720`).
-/

open Finset R45 R45.U3G

namespace Romanoff.G.S2

/-- `[e ∉ X]`. -/
def ind (X e : ℕ) : ℕ := if X.testBit e then 0 else 1

/-- `N^h_a(X) = Σ_{e < P, e ≡ a (h)} [e ∉ X]`. -/
def cntP (P X h a : ℕ) : ℕ := ∑ e ∈ range P, if e % h = a then ind X e else 0

/-- `S_g(X) = Σ_{a < g} N^g_a(X)^2`. -/
def SP (P X g : ℕ) : ℕ := ∑ a ∈ range g, cntP P X g a ^ 2

theorem ind_le (X e : ℕ) : ind X e ≤ 1 := by unfold ind; split_ifs <;> omega

/-- `Σ_{t < q} [e mod hq = a + h t] = [e mod h = a]`. -/
theorem sum_mod_mul {h q a : ℕ} (hh : 0 < h) (hq : 0 < q) (ha : a < h) (e : ℕ) (f : ℕ) :
    (∑ t ∈ range q, if e % (h * q) = a + h * t then f else 0) = if e % h = a then f else 0 := by
  have key : ∀ t, (e % (h * q) = a + h * t ↔ e % h = a ∧ e / h % q = t) := by
    intro t
    rw [Nat.mod_mul]
    constructor
    · intro hx
      have h1 : (e % h + h * (e / h % q)) % h = (a + h * t) % h := by rw [hx]
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ hh),
        Nat.mod_eq_of_lt ha] at h1
      refine ⟨h1, ?_⟩
      rw [h1] at hx
      have := Nat.eq_of_mul_eq_mul_left hh (Nat.add_left_cancel hx)
      exact this
    · rintro ⟨h1, h2⟩; rw [h1, h2]
  simp_rw [key]
  by_cases h1 : e % h = a
  · have : ∀ t ∈ range q, (if e % h = a ∧ e / h % q = t then f else 0) = if e / h % q = t then f else 0 := by
      intro t _; simp [h1]
    rw [sum_congr rfl this, Finset.sum_ite_eq, if_pos (mem_range.mpr (Nat.mod_lt _ hq)), if_pos h1]
  · have : ∀ t ∈ range q, (if e % h = a ∧ e / h % q = t then f else 0) = 0 := by
      intro t _; simp [h1]
    rw [sum_congr rfl this, sum_const_zero, if_neg h1]

/-- `N^h_a = Σ_{t < q} N^{hq}_{a + h t}`. -/
theorem cntP_split (P X : ℕ) {h q a : ℕ} (hh : 0 < h) (hq : 0 < q) (ha : a < h) :
    cntP P X h a = ∑ t ∈ range q, cntP P X (h * q) (a + h * t) := by
  unfold cntP
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e _
  rw [sum_mod_mul hh hq ha e (ind X e)]

theorem cntP_le_cntP0 (P X h a : ℕ) : cntP P X h a ≤ cntP P 0 h a := by
  unfold cntP
  apply sum_le_sum
  intro e _
  split_ifs
  · exact (ind_le X e).trans (by simp [ind])
  · exact le_refl _

theorem cntP_top (P X : ℕ) {a : ℕ} (ha : a < P) : cntP P X P a = ind X a := by
  unfold cntP
  rw [Finset.sum_eq_single a]
  · rw [Nat.mod_eq_of_lt ha, if_pos rfl]
  · intro e he hne
    rw [Nat.mod_eq_of_lt (mem_range.mp he), if_neg hne]
  · intro h; exact absurd (mem_range.mpr ha) h

/-- `N^g_a(∅) = P / g` for `g ∣ P`, `a < g`. -/
theorem cntP0 {P g a : ℕ} (hg : g ∣ P) (hg0 : 0 < g) (hP : 0 < P) (ha : a < g) : cntP P 0 g a = P / g := by
  obtain ⟨k, rfl⟩ := hg
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hP)
  rw [Nat.mul_div_cancel_left _ hg0, cntP_split (g * k) 0 hg0 hk0 ha]
  have : ∀ t ∈ range k, cntP (g * k) 0 (g * k) (a + g * t) = 1 := by
    intro t ht
    have : a + g * t < g * k := by
      have := mem_range.mp ht
      calc a + g * t < g + g * t := by omega
        _ = g * (t + 1) := by ring
        _ ≤ g * k := Nat.mul_le_mul_left _ this
    rw [cntP_top _ 0 this]; simp [ind]
  rw [sum_congr rfl this]; simp

theorem sum_cntP (P X : ℕ) {g : ℕ} (hg0 : 0 < g) : ∑ a ∈ range g, cntP P X g a = cntP P X 1 0 := by
  rw [cntP_split P X (h := 1) (q := g) Nat.one_pos hg0 Nat.one_pos]
  simp

/-- `g S_g ≤ P |U|` for `g ∣ P`. -/
theorem SP_le (P X : ℕ) {g : ℕ} (hg : g ∣ P) (hg0 : 0 < g) (hP : 0 < P) : g * SP P X g ≤ P * cntP P X 1 0 := by
  have h1 : SP P X g ≤ P / g * cntP P X 1 0 := by
    unfold SP
    rw [← sum_cntP P X hg0, mul_sum]
    apply sum_le_sum
    intro a ha
    rw [pow_two]
    apply Nat.mul_le_mul_right
    exact (cntP_le_cntP0 P X g a).trans (cntP0 hg hg0 hP (mem_range.mp ha)).le
  calc g * SP P X g ≤ g * (P / g * cntP P X 1 0) := Nat.mul_le_mul_left _ h1
    _ = g * (P / g) * cntP P X 1 0 := by ring
    _ = P * cntP P X 1 0 := by rw [Nat.mul_div_cancel' hg]

/-- `Σ_{a < g} N^g_a(X1) N^g_a(X2) = Σ_{e, e' < P, e ≡ e' (g)} [e ∉ X1] [e' ∉ X2]`. -/
theorem dotP_double (P X1 X2 : ℕ) {g : ℕ} (hg0 : 0 < g) :
    ∑ a ∈ range g, cntP P X1 g a * cntP P X2 g a =
      ∑ e ∈ range P, ∑ e' ∈ range P, if e % g = e' % g then ind X1 e * ind X2 e' else 0 := by
  unfold cntP
  have h3 : ∀ a ∈ range g, (∑ e ∈ range P, if e % g = a then ind X1 e else 0) *
      (∑ e ∈ range P, if e % g = a then ind X2 e else 0) =
      ∑ e ∈ range P, ∑ e' ∈ range P,
        (if e % g = a then ind X1 e else 0) * (if e' % g = a then ind X2 e' else 0) := by
    intro a _
    rw [sum_mul_sum]
  rw [sum_congr rfl h3, Finset.sum_comm]
  apply sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e' _
  have h4 : ∀ a ∈ range g, (if e % g = a then ind X1 e else 0) * (if e' % g = a then ind X2 e' else 0) =
      if e % g = a then (if e % g = e' % g then ind X1 e * ind X2 e' else 0) else 0 := by
    intro a _
    by_cases ha : e % g = a
    · subst ha
      by_cases hb : e' % g = e % g
      · simp [hb]
      · simp [hb, Ne.symm hb]
    · simp [ha]
  rw [sum_congr rfl h4, Finset.sum_ite_eq (range g) (e % g)]
  simp [Nat.mod_lt _ hg0]

/-- `S_g = Σ_{e, e' < P, e ≡ e' (g)} [e ∉ X] [e' ∉ X]`. -/
theorem SP_double (P X : ℕ) {g : ℕ} (hg0 : 0 < g) :
    SP P X g = ∑ e ∈ range P, ∑ e' ∈ range P, if e % g = e' % g then ind X e * ind X e' else 0 := by
  rw [← dotP_double P X X hg0]
  unfold SP
  exact sum_congr rfl fun a _ => pow_two _

/-! ## The bridge to `popcount` and `nShift` at period 27720 -/

theorem testBit_fx (X : ℕ) {e : ℕ} (he : e < 27720) : (full 27720 ^^^ X).testBit e = !X.testBit e := by
  rw [Nat.testBit_xor, testBit_full]
  simp [he]

theorem card_filter_eq_sum (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (s.filter P).card = ∑ e ∈ s, if P e then 1 else 0 := by
  rw [Finset.card_filter]

theorem popcount_fx (X : ℕ) : popcount 27720 (full 27720 ^^^ X) = cntP 27720 X 1 0 := by
  rw [popcount_eq, card_filter_eq_sum]
  unfold cntP
  apply sum_congr rfl
  intro e he
  rw [testBit_fx X (mem_range.mp he), Nat.mod_one, if_pos rfl]
  unfold ind
  cases X.testBit e <;> simp

/-- For `g ∣ 27720` and `e, e' < 27720`: `g ∣ (e' - e) mod 27720 ↔ e ≡ e' (g)`. -/
theorem shift_mod_iff {g : ℕ} (hg : g ∣ 27720) {e e' : ℕ} (he : e < 27720) :
    (e' + 27720 - e) % 27720 % g = 0 ↔ e % g = e' % g := by
  rw [Nat.mod_mod_of_dvd _ hg, ← Nat.dvd_iff_mod_eq_zero]
  rw [← Nat.modEq_iff_dvd' (by omega : e ≤ e' + 27720)]
  have h3 : e' + 27720 ≡ e' [MOD g] := by
    have := Nat.ModEq.add_left e' (Nat.modEq_zero_iff_dvd.mpr hg)
    simpa using this
  constructor
  · intro h; exact h.trans h3
  · intro h; exact h.trans h3.symm

/-- `Σ_{c < 27720, g ∣ c} n_U(c) = Σ_{e, e' ∈ U, e ≡ e' (g)} 1`. -/
theorem sum_shift (X g : ℕ) (hg : g ∣ 27720) (e : ℕ) (he : e < 27720) :
    (∑ c ∈ range 27720, if c % g = 0 then ind X ((e + c) % 27720) else 0) =
      ∑ e' ∈ range 27720, if e % g = e' % g then ind X e' else 0 := by
  apply Finset.sum_nbij' (fun c => (e + c) % 27720) (fun e' => (e' + 27720 - e) % 27720)
  · intro c _; simp only [mem_range]; exact Nat.mod_lt _ (by norm_num)
  · intro e' _; simp only [mem_range]; exact Nat.mod_lt _ (by norm_num)
  · intro c hc
    simp only [mem_range] at hc
    omega
  · intro e' he'
    simp only [mem_range] at he'
    omega
  · intro c hc
    simp only [mem_range] at hc
    have hc' : ((e + c) % 27720 + 27720 - e) % 27720 = c := by omega
    have hiff : c % g = 0 ↔ e % g = (e + c) % 27720 % g := by
      rw [← shift_mod_iff hg he, hc']
    by_cases h1 : c % g = 0
    · rw [if_pos h1, if_pos (hiff.mp h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2))]

theorem ngOf_nShift (X : ℕ) {g : ℕ} (hg : g ∣ 27720) (hg0 : 0 < g) :
    ngOf (nShift 27720 (full 27720 ^^^ X)) g = SP 27720 X g := by
  have hq := ngOf_eq (nShift 27720 (full 27720 ^^^ X)) (nShift_length _ _) g
  apply Nat.cast_injective (R := ℚ)
  rw [hq]
  have h1 : ∀ c ∈ range 27720, (if c % g = 0 then (((nShift 27720 (full 27720 ^^^ X)).getD c 0 : ℕ) : ℚ) else 0) =
      ((∑ e ∈ range 27720, if c % g = 0 then ind X e * ind X ((e + c) % 27720) else 0 : ℕ) : ℚ) := by
    intro c hc
    rw [nShift_getD _ _ c (mem_range.mp hc), card_filter_eq_sum]
    by_cases h : c % g = 0
    · simp only [h, if_true]
      push_cast
      apply sum_congr rfl
      intro e he
      rw [testBit_fx X (mem_range.mp he), testBit_fx X (Nat.mod_lt _ (show 0 < 27720 by norm_num))]
      unfold ind
      cases X.testBit e <;> cases X.testBit ((e + c) % 27720) <;> simp
    · simp [h]
  rw [sum_congr rfl h1, ← Nat.cast_sum, Nat.cast_inj]
  rw [Finset.sum_comm]
  have h2 : ∀ e ∈ range 27720, (∑ c ∈ range 27720, if c % g = 0 then ind X e * ind X ((e + c) % 27720) else 0) =
      ∑ e' ∈ range 27720, if e % g = e' % g then ind X e * ind X e' else 0 := by
    intro e he
    have h5 : ∀ c ∈ range 27720, (if c % g = 0 then ind X e * ind X ((e + c) % 27720) else 0) =
        ind X e * (if c % g = 0 then ind X ((e + c) % 27720) else 0) := by
      intro c _; split_ifs <;> simp
    rw [sum_congr rfl h5, ← mul_sum, sum_shift X g hg e (mem_range.mp he), mul_sum]
    apply sum_congr rfl
    intro e' _
    split_ifs <;> simp
  rw [sum_congr rfl h2, SP_double 27720 X hg0]

end Romanoff.G.S2
