import GK.Spec1
import Romanoff.G.S2.Core
import Romanoff.G.S2.Ind

/-!
# k45g, proofs part 2: the fibered component at the level of the core rows (at period 360)

For `x < 360` write `ρ = x mod 120` and `w = (x mod 9) / 3`; `x ↦ (ρ, w)` is a bijection `range 360 → range 120 × range 3`
(`sum360_fib`). A mask `M` whose exclusions depend only on `(x mod 12, w)` (the options of 19, 73, 37) gives, for the core row
`Y = repB 120 360 R ∪ M`:
- `cntP 360 Y 4 u = Σ_{i<3} f_M(u + 4 i) n_R(u + 4 i)` (`cnt4_fib`),
- `Tc Y g u v = Σ_{i,j<3} W_M^{[9 | g]}(u + 4 i, v + 4 j) T^R_{gcd(g,120)}(u + 4 i, v + 4 j)` for `g | 360` (`Tc_fib`).
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

/-! ## The bijection `x ↦ (x mod 120, (x mod 9) / 3)` -/

theorem sum3_rot {M : Type*} [AddCommMonoid M] (F : ℕ → M) (c : ℕ) (hc : c < 3) :
    ∑ k ∈ range 3, F ((c + k) % 3) = ∑ w ∈ range 3, F w := by
  interval_cases c <;> simp [sum_range_succ] <;> abel

theorem sum360_fib {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) :
    ∑ x ∈ range 360, F (x % 120) ((x % 9) / 3) = ∑ ρ ∈ range 120, ∑ w ∈ range 3, F ρ w := by
  rw [show (360 : ℕ) = 3 * 120 by norm_num, sum_range_mul_split 120 _ 3, sum_comm]
  refine sum_congr rfl fun ρ hρ => ?_
  have hρ' := mem_range.mp hρ
  have e : ∀ k ∈ range 3, F ((120 * k + ρ) % 120) (((120 * k + ρ) % 9) / 3) = F ρ (((ρ % 9) / 3 + k) % 3) := by
    intro k hk
    have hk' := mem_range.mp hk
    congr 1 <;> omega
  rw [sum_congr rfl e]
  exact sum3_rot (F ρ) ((ρ % 9) / 3) (by omega)

/-! ## The relation `x ≡ x' (mod g)` for `g | 360` -/

/-- The divisors of 360 as a list (`dC.toList`). -/
def dCl : List ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90, 120, 180, 360]

theorem dCl_eq : dCl = dC.toList := by decide

theorem rel360 {g : ℕ} (hg : g ∈ dCl) (x x' : ℕ) :
    x % g = x' % g ↔ x % 120 % Nat.gcd g 120 = x' % 120 % Nat.gcd g 120 ∧ (g % 9 = 0 → (x % 9) / 3 = (x' % 9) / 3) := by
  simp only [dCl, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> norm_num <;> omega

/-! ## Masks that depend only on `(x mod 12, w)` -/

/-- The representative `x < 36` with `x ≡ a (mod 12)` and `(x mod 9) / 3 = w` (`a < 12`, `w < 3`). -/
def xaw (a w : ℕ) : ℕ := a + 12 * ((w + 3 - (a % 9) / 3) % 3)

theorem xaw_spec {a w : ℕ} (ha : a < 12) (hw : w < 3) : xaw a w % 12 = a ∧ (xaw a w % 9) / 3 = w := by
  unfold xaw; constructor <;> omega

/-- `f_M(a) = #{w < 3 : (a, w) survives}`. -/
def fwM (M a : ℕ) : ℕ := ∑ w ∈ range 3, ind M (xaw a w)

/-- `W^1_M(a, b) = #{w < 3 : (a, w) and (b, w) survive}`. -/
def w1M (M a b : ℕ) : ℕ := ∑ w ∈ range 3, ind M (xaw a w) * ind M (xaw b w)

/-- `W_M^{[9 | g]}(a, b)`. -/
def WtM (M g a b : ℕ) : ℕ := if g % 9 = 0 then w1M M a b else fwM M a * fwM M b

/-- The exclusions of `M` below 360 depend only on `(x mod 12, (x mod 9) / 3)`. -/
def Fib (M : ℕ) : Prop := ∀ x < 360, ind M x = ind M (xaw (x % 12) ((x % 9) / 3))

theorem ind_repB120 (R : ℕ) {x : ℕ} (hx : x < 360) : ind (repB 120 360 R) x = ind R (x % 120) := by
  unfold ind; rw [repB_testBit]; simp [hx]

theorem sv_eq_ind (R ρ : ℕ) : sv R ρ = ind R ρ := rfl

/-- The class sizes of the rest row: `n_R(a) = Σ_{m<10} ind R (a + 12 m)`. -/
theorem nR_eq (R a : ℕ) : nR R a = ∑ m ∈ range 10, ind R (a + 12 * m) := by
  unfold nR; rw [sumN_eq]; rfl

/-- `T^R_h(a, b) = Σ_{m, m' < 10} [(a + 12 m) ≡ (b + 12 m') (mod h)] ind R (a + 12 m) ind R (b + 12 m')`. -/
theorem TR_eq (R h a b : ℕ) :
    TR R h a b = ∑ m ∈ range 10, ∑ m' ∈ range 10,
      if (a + 12 * m) % h = (b + 12 * m') % h then ind R (a + 12 * m) * ind R (b + 12 * m') else 0 := by
  unfold TR NR
  rw [sumN_eq]
  refine sum_congr rfl fun m _ => ?_
  rw [sumN_eq, mul_sum]
  refine sum_congr rfl fun m' _ => ?_
  by_cases hc : (b + 12 * m') % h = (a + 12 * m) % h
  · rw [if_pos hc, if_pos hc.symm]; rfl
  · rw [if_neg hc, if_neg (Ne.symm hc), mul_zero]

/-- Sums over `a < 12` with `a ≡ u (mod 4)` are sums over `a = u + 4 i`, `i < 3`. -/
theorem sum12_mod4 {M : Type*} [AddCommMonoid M] (H : ℕ → M) {u : ℕ} (hu : u < 4) :
    ∑ a ∈ range 12, (if a % 4 = u then H a else 0) = ∑ i ∈ range 3, H (u + 4 * i) := by
  rw [show (12 : ℕ) = 3 * 4 by norm_num, sum_range_mul_split 4 _ 3]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [Finset.sum_eq_single u]
  · rw [if_pos (by omega)]; congr 1; ring
  · intro b hb hbu
    rw [if_neg]; have := mem_range.mp hb; omega
  · intro hu'; exact absurd (mem_range.mpr hu) hu'

/-- Sums over `ρ < 120` as sums over `ρ = a + 12 m`, `a < 12`, `m < 10`. -/
theorem sum120_split {M : Type*} [AddCommMonoid M] (H : ℕ → M) :
    ∑ ρ ∈ range 120, H ρ = ∑ a ∈ range 12, ∑ m ∈ range 10, H (a + 12 * m) := by
  rw [show (120 : ℕ) = 10 * 12 by norm_num, sum_range_mul_split 12 _ 10, sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun m _ => ?_
  congr 1; ring

/-! ## `n4` of a fibered core row -/

theorem cnt4_fib (R M : ℕ) (hM : Fib M) {u : ℕ} (hu : u < 4) :
    cntP 360 (repB 120 360 R ||| M) 4 u = ∑ i ∈ range 3, fwM M (u + 4 * i) * nR R (u + 4 * i) := by
  unfold cntP
  have e1 : ∀ x ∈ range 360, (if x % 4 = u then ind (repB 120 360 R ||| M) x else 0) =
      (fun ρ w => if ρ % 4 = u then ind R ρ * ind M (xaw (ρ % 12) w) else 0) (x % 120) ((x % 9) / 3) := by
    intro x hx
    have hx' := mem_range.mp hx
    simp only
    rw [ind_or, ind_repB120 R hx', hM x hx', show x % 120 % 4 = x % 4 by omega, show x % 120 % 12 = x % 12 by omega]
  rw [sum_congr rfl e1, sum360_fib (fun ρ w => if ρ % 4 = u then ind R ρ * ind M (xaw (ρ % 12) w) else 0)]
  have e2 : ∀ ρ ∈ range 120, ∑ w ∈ range 3, (if ρ % 4 = u then ind R ρ * ind M (xaw (ρ % 12) w) else 0) =
      if ρ % 4 = u then ind R ρ * fwM M (ρ % 12) else 0 := by
    intro ρ _
    by_cases h : ρ % 4 = u
    · simp only [h, if_true, fwM, mul_sum]
    · simp [h]
  rw [sum_congr rfl e2, sum120_split]
  have e3 : ∀ a ∈ range 12, ∑ m ∈ range 10, (if (a + 12 * m) % 4 = u then ind R (a + 12 * m) * fwM M ((a + 12 * m) % 12)
      else 0) = if a % 4 = u then fwM M a * nR R a else 0 := by
    intro a ha
    have ha' := mem_range.mp ha
    by_cases h : a % 4 = u
    · rw [if_pos h, nR_eq, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [if_pos (by omega), show (a + 12 * m) % 12 = a by omega, mul_comm]
    · rw [if_neg h]
      exact sum_eq_zero fun m _ => by rw [if_neg (by omega)]
  rw [sum_congr rfl e3, sum12_mod4 (fun a => fwM M a * nR R a) hu]

/-! ## `Tc` of a fibered core row -/

theorem sum_w_pair (M a b : ℕ) (nine : Bool) :
    (∑ w ∈ range 3, ∑ w' ∈ range 3, if (nine = true → w = w') then ind M (xaw a w) * ind M (xaw b w') else 0) =
      if nine = true then w1M M a b else fwM M a * fwM M b := by
  cases nine
  · simp only [Bool.false_eq_true, false_implies, if_true, fwM, sum_mul_sum]
    rfl
  · simp only [if_true, forall_const, w1M]
    refine sum_congr rfl fun w _ => ?_
    rw [Finset.sum_eq_single w]
    · simp
    · intro w' _ hw'; rw [if_neg (Ne.symm hw')]
    · intro hw; exact absurd (by assumption) hw

theorem Tc_fib (R M : ℕ) (hM : Fib M) {g : ℕ} (hg : g ∈ dCl) {u v : ℕ} (hu : u < 4) (hv : v < 4) :
    Tc (repB 120 360 R ||| M) g u v = ∑ i ∈ range 3, ∑ j ∈ range 3,
      WtM M g (u + 4 * i) (v + 4 * j) * TR R (Nat.gcd g 120) (u + 4 * i) (v + 4 * j) := by
  set g' := Nat.gcd g 120 with hg'
  -- the summand as a function of (ρ, w, ρ', w')
  let G : ℕ → ℕ → ℕ → ℕ → ℕ := fun ρ w ρ' w' =>
    if ρ % g' = ρ' % g' ∧ (g % 9 = 0 → w = w') ∧ ρ % 4 = u ∧ ρ' % 4 = v then
      ind R ρ * ind M (xaw (ρ % 12) w) * (ind R ρ' * ind M (xaw (ρ' % 12) w')) else 0
  have e1 : ∀ x ∈ range 360, ∀ x' ∈ range 360,
      (if x % g = x' % g ∧ x % 4 = u ∧ x' % 4 = v then ind (repB 120 360 R ||| M) x * ind (repB 120 360 R ||| M) x'
        else 0) = G (x % 120) ((x % 9) / 3) (x' % 120) ((x' % 9) / 3) := by
    intro x hx x' hx'
    have hx1 := mem_range.mp hx
    have hx2 := mem_range.mp hx'
    simp only [G]
    rw [ind_or, ind_or, ind_repB120 R hx1, ind_repB120 R hx2, hM x hx1, hM x' hx2, show x % 120 % 4 = x % 4 by omega,
      show x' % 120 % 4 = x' % 4 by omega, show x % 120 % 12 = x % 12 by omega, show x' % 120 % 12 = x' % 12 by omega]
    have hr := rel360 hg x x'
    by_cases hc : x % g = x' % g ∧ x % 4 = u ∧ x' % 4 = v
    · rw [if_pos hc, if_pos ⟨(hr.mp hc.1).1, (hr.mp hc.1).2, hc.2.1, hc.2.2⟩]
    · rw [if_neg hc, if_neg]
      intro h'
      exact hc ⟨hr.mpr ⟨h'.1, h'.2.1⟩, h'.2.2.1, h'.2.2.2⟩
  unfold Tc
  rw [sum_congr rfl fun x hx => sum_congr rfl fun x' hx' => e1 x hx x' hx']
  rw [sum_congr rfl fun x _ => sum360_fib (fun ρ' w' => G (x % 120) ((x % 9) / 3) ρ' w')]
  rw [sum360_fib (fun ρ w => ∑ ρ' ∈ range 120, ∑ w' ∈ range 3, G ρ w ρ' w')]
  -- sum over w, w' first
  have e2 : ∀ ρ ∈ range 120, ∀ ρ' ∈ range 120, ∑ w ∈ range 3, ∑ w' ∈ range 3, G ρ w ρ' w' =
      if ρ % g' = ρ' % g' ∧ ρ % 4 = u ∧ ρ' % 4 = v then ind R ρ * ind R ρ' * WtM M g (ρ % 12) (ρ' % 12) else 0 := by
    intro ρ _ ρ' _
    simp only [G]
    by_cases hc : ρ % g' = ρ' % g' ∧ ρ % 4 = u ∧ ρ' % 4 = v
    · rw [if_pos hc]
      have e : ∀ w ∈ range 3, ∀ w' ∈ range 3,
          (if ρ % g' = ρ' % g' ∧ (g % 9 = 0 → w = w') ∧ ρ % 4 = u ∧ ρ' % 4 = v then
            ind R ρ * ind M (xaw (ρ % 12) w) * (ind R ρ' * ind M (xaw (ρ' % 12) w')) else 0) =
          ind R ρ * ind R ρ' * (if (decide (g % 9 = 0) = true → w = w') then ind M (xaw (ρ % 12) w) *
            ind M (xaw (ρ' % 12) w') else 0) := by
        intro w _ w' _
        by_cases h9 : (g % 9 = 0 → w = w')
        · rw [if_pos ⟨hc.1, h9, hc.2.1, hc.2.2⟩, if_pos (by simpa using h9)]; ring
        · rw [if_neg (fun h => h9 h.2.1), if_neg (by simpa using h9), mul_zero]
      rw [sum_congr rfl fun w hw => sum_congr rfl fun w' hw' => e w hw w' hw']
      simp_rw [← mul_sum]
      rw [sum_w_pair M (ρ % 12) (ρ' % 12) (decide (g % 9 = 0))]
      unfold WtM
      by_cases h9 : g % 9 = 0 <;> simp [h9]
    · rw [if_neg hc]
      refine sum_eq_zero fun w _ => sum_eq_zero fun w' _ => ?_
      rw [if_neg (fun h => hc ⟨h.1, h.2.2.1, h.2.2.2⟩)]
  have e_swap : ∀ ρ ∈ range 120, ∑ w ∈ range 3, ∑ ρ' ∈ range 120, ∑ w' ∈ range 3, G ρ w ρ' w' =
      ∑ ρ' ∈ range 120, ∑ w ∈ range 3, ∑ w' ∈ range 3, G ρ w ρ' w' := fun ρ _ => sum_comm
  rw [sum_congr rfl e_swap, sum_congr rfl fun ρ hρ => sum_congr rfl fun ρ' hρ' => e2 ρ hρ ρ' hρ']
  -- split ρ = a + 12 m and ρ' = b + 12 m'
  rw [sum120_split]
  simp_rw [sum120_split (fun ρ' => if (_ : ℕ) % g' = ρ' % g' ∧ _ ∧ ρ' % 4 = v then _ else 0)]
  have e3 : ∀ a ∈ range 12, ∑ m ∈ range 10, ∑ b ∈ range 12, ∑ m' ∈ range 10,
      (if (a + 12 * m) % g' = (b + 12 * m') % g' ∧ (a + 12 * m) % 4 = u ∧ (b + 12 * m') % 4 = v then
        ind R (a + 12 * m) * ind R (b + 12 * m') * WtM M g ((a + 12 * m) % 12) ((b + 12 * m') % 12) else 0) =
      if a % 4 = u then ∑ b ∈ range 12, (if b % 4 = v then WtM M g a b * TR R g' a b else 0) else 0 := by
    intro a ha
    have ha' := mem_range.mp ha
    rw [sum_comm]
    by_cases hau : a % 4 = u
    · rw [if_pos hau]
      refine sum_congr rfl fun b hb => ?_
      have hb' := mem_range.mp hb
      by_cases hbv : b % 4 = v
      · rw [if_pos hbv, TR_eq, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun m' _ => ?_
        rw [show (a + 12 * m) % 12 = a by omega, show (b + 12 * m') % 12 = b by omega]
        by_cases hc : (a + 12 * m) % g' = (b + 12 * m') % g'
        · rw [if_pos ⟨hc, by omega, by omega⟩, if_pos hc]; ring
        · rw [if_neg (fun h => hc h.1), if_neg hc, mul_zero]
      · rw [if_neg hbv]
        exact sum_eq_zero fun m _ => sum_eq_zero fun m' _ => by rw [if_neg (by omega)]
    · rw [if_neg hau]
      exact sum_eq_zero fun b _ => sum_eq_zero fun m _ => sum_eq_zero fun m' _ => by rw [if_neg (by omega)]
  rw [sum_congr rfl e3, sum12_mod4 (fun a => ∑ b ∈ range 12, if b % 4 = v then WtM M g a b * TR R g' a b else 0) hu]
  refine sum_congr rfl fun i _ => ?_
  rw [sum12_mod4 (fun b => WtM M g (u + 4 * i) b * TR R g' (u + 4 * i) b) hv]

end R45.GK
