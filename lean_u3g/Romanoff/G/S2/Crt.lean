import Romanoff.G.S2.Core

/-!
# U3g/V4g stage 2: the factorization of a row at period 27720 = 360 · 7 · 11 (the reduction for the modulus l_3 in Section 6 of the paper)

A row `X` has the product form `ProdForm X Y φ7 φ11` if, for `e < 27720`,
`[e ∉ X] = [e mod 360 ∉ Y] φ7(e mod 4, e mod 7) φ11(e mod 4, e mod 11)`.  Then, by the Chinese remainder theorem
`e ↔ (e mod 360, e mod 77)` and `z ↔ (z mod 7, z mod 11)` (`crt27720`, `crt77`):
* `s_prod`: `|U| = Σ_{u < 4} f7(u) f11(u) N^4_u(Y)`, `f_q(u) = Σ_{y < q} φ(u, y)`;
* `S_prod`: for `g_c ∣ 360` and `τ = tau t ∈ {1, 7, 11, 77}` (`t < 4`),
  `S_{g_c τ}(X) = Σ_{u, v < 4} W7(u, v) W11(u, v) T_{g_c}(u, v)` with `W_q(u, v) = Σ_{y < q} φ(u, y) φ(v, y)` if `q ∣ τ`
  and `f_q(u) f_q(v)` otherwise (`Wq`), and `T` the core class-pair counts `Tc`.
-/

open Finset

namespace Romanoff.G.S2

/-- The Chinese remainder theorem as a reindexing of sums (any additive commutative monoid). -/
theorem sum_range_mul_crt' {M : Type*} [AddCommMonoid M] {p m : ℕ} (hcop : Nat.Coprime p m) (hp : 0 < p) (hm : 0 < m)
    (F : ℕ → ℕ → M) : ∑ k ∈ range (p * m), F (k % p) (k % m) = ∑ a ∈ range p, ∑ b ∈ range m, F a b := by
  rw [← sum_product (range p) (range m) (fun ab => F ab.1 ab.2)]
  have hinj : Set.InjOn (fun k => (k % p, k % m)) (range (p * m) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hab.1, hab.2⟩
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] at h
  have himg : (range (p * m)).image (fun k => (k % p, k % m)) = range p ×ˢ range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨k, _, rfl⟩ := mem_image.mp hy
      exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp), mem_range.mpr (Nat.mod_lt _ hm)⟩
    · rw [card_image_of_injOn hinj, card_product, card_range, card_range, card_range]
  rw [← himg, sum_image hinj]

theorem crt27720 (G : ℕ → ℕ → ℕ) : ∑ e ∈ range 27720, G (e % 360) (e % 77) = ∑ x ∈ range 360, ∑ z ∈ range 77, G x z := by
  have h : (27720 : ℕ) = 360 * 77 := by norm_num
  rw [h]
  exact sum_range_mul_crt' (by norm_num) (by norm_num) (by norm_num) G

theorem crt77 (G : ℕ → ℕ → ℕ) : ∑ z ∈ range 77, G (z % 7) (z % 11) = ∑ a ∈ range 7, ∑ b ∈ range 11, G a b := by
  have h : (77 : ℕ) = 7 * 11 := by norm_num
  rw [h]
  exact sum_range_mul_crt' (by norm_num) (by norm_num) (by norm_num) G

/-- `τ_t = 1, 7, 11, 77`. -/
def tau : ℕ → ℕ
  | 0 => 1
  | 1 => 7
  | 2 => 11
  | _ => 77

/-- `7 ∣ τ_t` and `11 ∣ τ_t`. -/
def b7 (t : ℕ) : Bool := t == 1 || t == 3
def b11 (t : ℕ) : Bool := t == 2 || t == 3

/-- `(7 ∣ τ_t → z ≡ z' (7)) ∧ (11 ∣ τ_t → z ≡ z' (11))`. -/
def cz (t z z' : ℕ) : Bool := (!b7 t || z % 7 == z' % 7) && (!b11 t || z % 11 == z' % 11)

/-- `f(u) = Σ_{y < q} φ(u, y)`. -/
def fq (q : ℕ) (φ : ℕ → ℕ → ℕ) (u : ℕ) : ℕ := ∑ y ∈ range q, φ u y

/-- `W(u, v) = Σ_{y < q} φ(u, y) φ(v, y)` (if `b`) or `f(u) f(v)`. -/
def Wq (q : ℕ) (φ : ℕ → ℕ → ℕ) (b : Bool) (u v : ℕ) : ℕ :=
  if b then ∑ y ∈ range q, φ u y * φ v y else fq q φ u * fq q φ v

/-- The product form of the row `X` (period 27720) over the core mask `Y`. -/
def ProdForm (X Y : ℕ) (φ7 φ11 : ℕ → ℕ → ℕ) : Prop :=
  ∀ e < 27720, ind X e = ind Y (e % 360) * φ7 (e % 360 % 4) (e % 7) * φ11 (e % 360 % 4) (e % 11)

theorem tau_pos (t : ℕ) : 0 < tau t := by unfold tau; split <;> norm_num

theorem tau_dvd77 (t : ℕ) : tau t ∣ 77 := by unfold tau; split <;> norm_num

/-- `e ≡ e' (g_c τ_t) ↔ e mod 360 ≡ e' mod 360 (g_c) ∧ cz t (e mod 77) (e' mod 77)`. -/
theorem mod_iff {gc t : ℕ} (hgc : gc ∣ 360) (ht : t < 4) (e e' : ℕ) :
    e % (gc * tau t) = e' % (gc * tau t) ↔ e % 360 % gc = e' % 360 % gc ∧ cz t (e % 77) (e' % 77) = true := by
  have hcop : Nat.Coprime gc (tau t) :=
    Nat.Coprime.coprime_dvd_left hgc (Nat.Coprime.coprime_dvd_right (tau_dvd77 t) (by norm_num))
  rw [Nat.mod_mod_of_dvd _ hgc, Nat.mod_mod_of_dvd _ hgc]
  have h1 : e % (gc * tau t) = e' % (gc * tau t) ↔ e % gc = e' % gc ∧ e % tau t = e' % tau t :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).symm
  rw [h1]
  apply and_congr_right
  intro _
  unfold cz
  rw [Nat.mod_mod_of_dvd e (by norm_num : 7 ∣ 77), Nat.mod_mod_of_dvd e' (by norm_num : 7 ∣ 77),
    Nat.mod_mod_of_dvd e (by norm_num : 11 ∣ 77), Nat.mod_mod_of_dvd e' (by norm_num : 11 ∣ 77)]
  interval_cases t
  · simp [tau, b7, b11, Nat.mod_one]
  · simp [tau, b7, b11]
  · simp [tau, b7, b11]
  · have h2 : e % 77 = e' % 77 ↔ e % 7 = e' % 7 ∧ e % 11 = e' % 11 :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 7 11)).symm
    simpa [tau, b7, b11] using h2

theorem sum4_ite {M : Type*} [AddCommMonoid M] (x : ℕ) (f : ℕ → M) :
    ∑ u ∈ range 4, (if x % 4 = u then f u else 0) = f (x % 4) := by
  rw [Finset.sum_ite_eq (range 4) (x % 4) f, if_pos (mem_range.mpr (Nat.mod_lt _ (by norm_num)))]

/-- One residue of the product form: `[x ∉ Y] φ7(x mod 4, z mod 7) φ11(x mod 4, z mod 11)`. -/
def Az (Y : ℕ) (φ7 φ11 : ℕ → ℕ → ℕ) (x z : ℕ) : ℕ := ind Y x * φ7 (x % 4) (z % 7) * φ11 (x % 4) (z % 11)

theorem prod_ind {X Y : ℕ} {φ7 φ11 : ℕ → ℕ → ℕ} (h : ProdForm X Y φ7 φ11) {e : ℕ} (he : e < 27720) :
    ind X e = Az Y φ7 φ11 (e % 360) (e % 77) := by
  rw [h e he]
  unfold Az
  rw [Nat.mod_mod_of_dvd e (by norm_num : 7 ∣ 77), Nat.mod_mod_of_dvd e (by norm_num : 11 ∣ 77)]

/-- `φ7(u, a) φ11(u, b)`. -/
def Pz (φ7 φ11 : ℕ → ℕ → ℕ) (u a b : ℕ) : ℕ := φ7 u a * φ11 u b

theorem sumz_Az (Y : ℕ) (φ7 φ11 : ℕ → ℕ → ℕ) (x : ℕ) :
    ∑ z ∈ range 77, Az Y φ7 φ11 x z = ind Y x * (fq 7 φ7 (x % 4) * fq 11 φ11 (x % 4)) := by
  have e1 : ∀ z ∈ range 77, Az Y φ7 φ11 x z = ind Y x * Pz φ7 φ11 (x % 4) (z % 7) (z % 11) := by
    intro z _; unfold Az Pz; ring
  rw [sum_congr rfl e1, ← mul_sum, crt77 (Pz φ7 φ11 (x % 4))]
  unfold Pz fq
  rw [sum_mul_sum]

/-- The class count: `|U| = Σ_{u < 4} f7(u) f11(u) N^4_u(Y)`. -/
theorem s_prod {X Y : ℕ} {φ7 φ11 : ℕ → ℕ → ℕ} (h : ProdForm X Y φ7 φ11) :
    cntP 27720 X 1 0 = ∑ u ∈ range 4, fq 7 φ7 u * fq 11 φ11 u * cntP 360 Y 4 u := by
  have e1 : cntP 27720 X 1 0 = ∑ e ∈ range 27720, Az Y φ7 φ11 (e % 360) (e % 77) := by
    unfold cntP
    refine sum_congr rfl fun e he => ?_
    rw [Nat.mod_one, if_pos rfl, prod_ind h (mem_range.mp he)]
  rw [e1, crt27720 (Az Y φ7 φ11)]
  rw [sum_congr rfl fun x _ => sumz_Az Y φ7 φ11 x]
  have e4 : ∀ x ∈ range 360, ind Y x * (fq 7 φ7 (x % 4) * fq 11 φ11 (x % 4)) =
      ∑ u ∈ range 4, if x % 4 = u then fq 7 φ7 u * fq 11 φ11 u * ind Y x else 0 := by
    intro x _
    rw [sum4_ite x (fun u => fq 7 φ7 u * fq 11 φ11 u * ind Y x)]
    ring
  rw [sum_congr rfl e4, Finset.sum_comm]
  refine sum_congr rfl fun u _ => ?_
  unfold cntP
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-! ## The pair sum of the independent coordinates -/

/-- The pair summand of the coordinates `(a, b) = (z mod 7, z mod 11)`, `(a', b')`. -/
def Kp (φ7 φ11 : ℕ → ℕ → ℕ) (t u v a b a' b' : ℕ) : ℕ :=
  (if (!b7 t || a == a') = true then φ7 u a * φ7 v a' else 0) *
    (if (!b11 t || b == b') = true then φ11 u b * φ11 v b' else 0)

/-- `Σ_{a' < 7} Σ_{b' < 11} Kp … a b a' b'`. -/
def KK (φ7 φ11 : ℕ → ℕ → ℕ) (t u v a b : ℕ) : ℕ := ∑ a' ∈ range 7, ∑ b' ∈ range 11, Kp φ7 φ11 t u v a b a' b'

theorem sum7_W (φ7 : ℕ → ℕ → ℕ) (t u v : ℕ) :
    ∑ a ∈ range 7, ∑ a' ∈ range 7, (if (!b7 t || a == a') = true then φ7 u a * φ7 v a' else 0) = Wq 7 φ7 (b7 t) u v := by
  unfold Wq fq
  cases b7 t
  · simp only [Bool.not_false, Bool.true_or, if_true, Bool.false_eq_true, if_false]
    rw [sum_mul_sum]
  · simp only [Bool.not_true, Bool.false_or, beq_iff_eq, if_true]
    refine sum_congr rfl fun a ha => ?_
    rw [Finset.sum_ite_eq (range 7) a, if_pos ha]

theorem sum11_W (φ11 : ℕ → ℕ → ℕ) (t u v : ℕ) :
    ∑ b ∈ range 11, ∑ b' ∈ range 11, (if (!b11 t || b == b') = true then φ11 u b * φ11 v b' else 0) =
      Wq 11 φ11 (b11 t) u v := by
  unfold Wq fq
  cases b11 t
  · simp only [Bool.not_false, Bool.true_or, if_true, Bool.false_eq_true, if_false]
    rw [sum_mul_sum]
  · simp only [Bool.not_true, Bool.false_or, beq_iff_eq, if_true]
    refine sum_congr rfl fun b hb => ?_
    rw [Finset.sum_ite_eq (range 11) b, if_pos hb]

theorem cz_Kp (φ7 φ11 : ℕ → ℕ → ℕ) (t u v z z' : ℕ) :
    (if cz t z z' = true then φ7 u (z % 7) * φ11 u (z % 11) * (φ7 v (z' % 7) * φ11 v (z' % 11)) else 0) =
      Kp φ7 φ11 t u v (z % 7) (z % 11) (z' % 7) (z' % 11) := by
  unfold cz Kp
  cases h1 : (!b7 t || z % 7 == z' % 7) <;> cases h2 : (!b11 t || z % 11 == z' % 11) <;> simp <;> ring

/-- The pair sum over `z, z' < 77` of one class pair `(u, v)`: `W7(u, v) W11(u, v)`. -/
theorem K_eq (φ7 φ11 : ℕ → ℕ → ℕ) (t u v : ℕ) :
    (∑ z ∈ range 77, ∑ z' ∈ range 77,
      if cz t z z' = true then φ7 u (z % 7) * φ11 u (z % 11) * (φ7 v (z' % 7) * φ11 v (z' % 11)) else 0) =
      Wq 7 φ7 (b7 t) u v * Wq 11 φ11 (b11 t) u v := by
  have e1 : ∀ z ∈ range 77, (∑ z' ∈ range 77,
      if cz t z z' = true then φ7 u (z % 7) * φ11 u (z % 11) * (φ7 v (z' % 7) * φ11 v (z' % 11)) else 0) =
      KK φ7 φ11 t u v (z % 7) (z % 11) := by
    intro z _
    rw [sum_congr rfl fun z' _ => cz_Kp φ7 φ11 t u v z z']
    exact crt77 (Kp φ7 φ11 t u v (z % 7) (z % 11))
  rw [sum_congr rfl e1, crt77 (KK φ7 φ11 t u v), ← sum7_W φ7 t u v, ← sum11_W φ11 t u v, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  unfold KK Kp
  rw [Finset.sum_comm, sum_mul]
  refine sum_congr rfl fun a' _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]

/-! ## The factorization of `S` -/

/-- The pair summand of `S_{g_c τ}` in the residues `(x, z)`, `(x', z')`. -/
def Fz (Y : ℕ) (φ7 φ11 : ℕ → ℕ → ℕ) (gc t x z x' z' : ℕ) : ℕ :=
  if x % gc = x' % gc ∧ cz t z z' = true then Az Y φ7 φ11 x z * Az Y φ7 φ11 x' z' else 0

/-- `Σ_{x' < 360} Σ_{z' < 77} Fz … x z x' z'`. -/
def Gz (Y : ℕ) (φ7 φ11 : ℕ → ℕ → ℕ) (gc t x z : ℕ) : ℕ :=
  ∑ x' ∈ range 360, ∑ z' ∈ range 77, Fz Y φ7 φ11 gc t x z x' z'

theorem sum_swap4 {M : Type*} [AddCommMonoid M] (A B C D : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → M) :
    ∑ u ∈ A, ∑ v ∈ B, ∑ x ∈ C, ∑ x' ∈ D, F u v x x' = ∑ x ∈ C, ∑ x' ∈ D, ∑ u ∈ A, ∑ v ∈ B, F u v x x' := by
  calc ∑ u ∈ A, ∑ v ∈ B, ∑ x ∈ C, ∑ x' ∈ D, F u v x x'
      = ∑ u ∈ A, ∑ x ∈ C, ∑ v ∈ B, ∑ x' ∈ D, F u v x x' := sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ x ∈ C, ∑ u ∈ A, ∑ v ∈ B, ∑ x' ∈ D, F u v x x' := Finset.sum_comm
    _ = ∑ x ∈ C, ∑ u ∈ A, ∑ x' ∈ D, ∑ v ∈ B, F u v x x' :=
        sum_congr rfl fun x _ => sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ x ∈ C, ∑ x' ∈ D, ∑ u ∈ A, ∑ v ∈ B, F u v x x' := sum_congr rfl fun x _ => Finset.sum_comm

/-- Grouping a pair sum over the core by the classes mod 4. -/
theorem group4 (Y gc : ℕ) (K : ℕ → ℕ → ℕ) :
    ∑ x ∈ range 360, ∑ x' ∈ range 360, (if x % gc = x' % gc then ind Y x * ind Y x' else 0) * K (x % 4) (x' % 4) =
      ∑ u ∈ range 4, ∑ v ∈ range 4, K u v * Tc Y gc u v := by
  symm
  unfold Tc
  have e1 : ∀ u ∈ range 4, ∀ v ∈ range 4, K u v * (∑ x ∈ range 360, ∑ x' ∈ range 360,
      if x % gc = x' % gc ∧ x % 4 = u ∧ x' % 4 = v then ind Y x * ind Y x' else 0) =
      ∑ x ∈ range 360, ∑ x' ∈ range 360,
        K u v * (if x % gc = x' % gc ∧ x % 4 = u ∧ x' % 4 = v then ind Y x * ind Y x' else 0) := by
    intro u _ v _
    rw [mul_sum]
    exact sum_congr rfl fun x _ => mul_sum _ _ _
  rw [sum_congr rfl fun u hu => sum_congr rfl (e1 u hu), sum_swap4]
  refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
  have e2 : ∀ u ∈ range 4, (∑ v ∈ range 4,
      K u v * (if x % gc = x' % gc ∧ x % 4 = u ∧ x' % 4 = v then ind Y x * ind Y x' else 0)) =
      if x % 4 = u then K u (x' % 4) * (if x % gc = x' % gc then ind Y x * ind Y x' else 0) else 0 := by
    intro u _
    by_cases hu : x % 4 = u
    · rw [if_pos hu]
      rw [← sum4_ite x' (fun v => K u v * (if x % gc = x' % gc then ind Y x * ind Y x' else 0))]
      refine sum_congr rfl fun v _ => ?_
      by_cases hv : x' % 4 = v <;> by_cases h1 : x % gc = x' % gc <;> simp [hu, hv, h1]
    · rw [if_neg hu]
      apply sum_eq_zero
      intro v _
      simp [hu]
  rw [sum_congr rfl e2, sum4_ite x (fun u => K u (x' % 4) * (if x % gc = x' % gc then ind Y x * ind Y x' else 0))]
  ring

/-- The reduction of Section 6 of the paper: `S_{g_c τ}(X) = Σ_{u, v < 4} W7(u, v) W11(u, v) T_{g_c}(u, v)`. -/
theorem S_prod {X Y : ℕ} {φ7 φ11 : ℕ → ℕ → ℕ} (h : ProdForm X Y φ7 φ11) {gc t : ℕ} (hgc : gc ∣ 360) (hgc0 : 0 < gc)
    (ht : t < 4) :
    SP 27720 X (gc * tau t) =
      ∑ u ∈ range 4, ∑ v ∈ range 4, Wq 7 φ7 (b7 t) u v * Wq 11 φ11 (b11 t) u v * Tc Y gc u v := by
  rw [SP_double 27720 X (Nat.mul_pos hgc0 (tau_pos t))]
  have e1 : ∀ e ∈ range 27720, ∀ e' ∈ range 27720,
      (if e % (gc * tau t) = e' % (gc * tau t) then ind X e * ind X e' else 0) =
        Fz Y φ7 φ11 gc t (e % 360) (e % 77) (e' % 360) (e' % 77) := by
    intro e he e' he'
    unfold Fz
    rw [prod_ind h (mem_range.mp he), prod_ind h (mem_range.mp he')]
    by_cases hc : e % (gc * tau t) = e' % (gc * tau t)
    · rw [if_pos hc, if_pos ((mod_iff hgc ht e e').mp hc)]
    · rw [if_neg hc, if_neg (fun h' => hc ((mod_iff hgc ht e e').mpr h'))]
  rw [sum_congr rfl fun e he => sum_congr rfl (e1 e he)]
  rw [sum_congr rfl fun e _ => crt27720 (Fz Y φ7 φ11 gc t (e % 360) (e % 77))]
  rw [show (∑ e ∈ range 27720, ∑ x' ∈ range 360, ∑ z' ∈ range 77, Fz Y φ7 φ11 gc t (e % 360) (e % 77) x' z') =
    ∑ e ∈ range 27720, Gz Y φ7 φ11 gc t (e % 360) (e % 77) from rfl, crt27720 (Gz Y φ7 φ11 gc t)]
  have e3 : ∀ x ∈ range 360, (∑ z ∈ range 77, Gz Y φ7 φ11 gc t x z) =
      ∑ x' ∈ range 360, (if x % gc = x' % gc then ind Y x * ind Y x' else 0) *
        (Wq 7 φ7 (b7 t) (x % 4) (x' % 4) * Wq 11 φ11 (b11 t) (x % 4) (x' % 4)) := by
    intro x _
    unfold Gz
    rw [Finset.sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    rw [← K_eq φ7 φ11 t (x % 4) (x' % 4), mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun z' _ => ?_
    unfold Fz Az
    by_cases h1 : x % gc = x' % gc <;> by_cases h2 : cz t z z' = true
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]; ring
    · rw [if_neg (fun h' => h2 h'.2), if_neg h2, mul_zero]
    · rw [if_neg (fun h' => h1 h'.1), if_neg h1, zero_mul]
    · rw [if_neg (fun h' => h1 h'.1), if_neg h1, zero_mul]
  rw [sum_congr rfl e3, group4 Y gc (fun u v => Wq 7 φ7 (b7 t) u v * Wq 11 φ11 (b11 t) u v)]

end Romanoff.G.S2
