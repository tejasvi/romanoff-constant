import Romanoff.G.S2.Crt

/-!
# U3g/V4g stage 2: the independent primes 23, 43, 29 (the attached primes of Section 6 of the paper and a table form of its orbits)

* `prodForm_row`: the row `X = Y' ∪ m_23(r23) ∪ m_43(r43) ∪ m_29(r29)` at period 27720 (`Y'` the 27720-bit periodic
  extension of a core mask `Y`) has the product form over `Y` with `φ7 = φ43(r43) φ29(r29)`, `φ11 = φ23(r23)`: the class
  `j mod 14` (`43`) is `(j mod 2, j mod 7)`, `j mod 28` (`29`) is `(j mod 4, j mod 7)`, `j mod 11` (`23`) is `j mod 11`;
* `tab7`, `tab11`: the tables `f`, `W` of every residue pair `(r43, r29)` and residue `r23` are those of its pattern
  `sig7[29 r43 + r29]`, `sig11[r23]` (checked by `decide` over all 1247 + 23 residues);
* `regroup`: the sum over the residue triples of a function of the pattern is the weighted sum over the patterns
  (weights `w7`, `w11`, counted by `decide`).
-/

open Finset R45 R45.EVG

namespace Romanoff.G.S2

/-! ## The masks of the independent primes -/

/-- `[2^j mod p ≠ r]` at the class `j` of `(u mod m_p, y)`: `p = 43` (`j mod 14`), `29` (`j mod 28`), `23` (`j mod 11`). -/
def φ43 (r u y : ℕ) : ℕ := if 2 ^ (((u % 2) * 7 + 8 * y) % 14) % 43 = r then 0 else 1
def φ29 (r u y : ℕ) : ℕ := if 2 ^ (((u % 4) * 21 + 8 * y) % 28) % 29 = r then 0 else 1
def φ23 (r u y : ℕ) : ℕ := if 2 ^ (y % 11) % 23 = r then 0 else 1

/-- The coordinate factors of q = 7 and q = 11. -/
def phi7 (r43 r29 u y : ℕ) : ℕ := φ43 r43 u y * φ29 r29 u y
def phi11 (r23 u y : ℕ) : ℕ := φ23 r23 u y

theorem ind_or (A B e : ℕ) : ind (A ||| B) e = ind A e * ind B e := by
  unfold ind; rw [Nat.testBit_or]; cases A.testBit e <;> cases B.testBit e <;> simp

theorem ind_maskP {per p r e : ℕ} (he : e < per) : ind (maskP per p r) e = if 2 ^ e % p = r then 0 else 1 := by
  unfold ind; rw [maskP_testBit]; by_cases h : 2 ^ e % p = r <;> simp [h, he]

theorem pow_mod_period {p o : ℕ} (hp : 1 < p) (h : 2 ^ o % p = 1) (e : ℕ) : 2 ^ e % p = 2 ^ (e % o) % p := by
  have h1 : (2 ^ o) ^ (e / o) % p = 1 := by rw [Nat.pow_mod, h, one_pow, Nat.mod_eq_of_lt hp]
  calc 2 ^ e % p = (2 ^ o) ^ (e / o) * 2 ^ (e % o) % p := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ = 2 ^ (e % o) % p := by rw [Nat.mul_mod, h1, one_mul, Nat.mod_mod]

theorem ind43 (r : ℕ) {e : ℕ} (he : e < 27720) : ind (maskP 27720 43 r) e = φ43 r (e % 360 % 4) (e % 7) := by
  rw [ind_maskP he, pow_mod_period (by norm_num) (by norm_num : 2 ^ 14 % 43 = 1) e]
  unfold φ43
  rw [show e % 14 = ((e % 360 % 4 % 2) * 7 + 8 * (e % 7)) % 14 by omega]

theorem ind29 (r : ℕ) {e : ℕ} (he : e < 27720) : ind (maskP 27720 29 r) e = φ29 r (e % 360 % 4) (e % 7) := by
  rw [ind_maskP he, pow_mod_period (by norm_num) (by norm_num : 2 ^ 28 % 29 = 1) e]
  unfold φ29
  rw [show e % 28 = ((e % 360 % 4 % 4) * 21 + 8 * (e % 7)) % 28 by omega]

theorem ind23 (r : ℕ) {e : ℕ} (he : e < 27720) : ind (maskP 27720 23 r) e = φ23 r (e % 360 % 4) (e % 11) := by
  rw [ind_maskP he, pow_mod_period (by norm_num) (by norm_num : 2 ^ 11 % 23 = 1) e]
  unfold φ23
  rw [Nat.mod_mod]

theorem repB_testBit (p n x e : ℕ) : (repB p n x).testBit e = (decide (e < n) && x.testBit (e % p)) := by
  unfold repB
  rw [testBit_foldl_or n (fun e => x.testBit (e % p) = true) n 0 e]
  simp

theorem ind_repB (Y : ℕ) {e : ℕ} (he : e < 27720) : ind (repB 360 27720 Y) e = ind Y (e % 360) := by
  unfold ind; rw [repB_testBit]; simp [he]

/-- The product form of Section 6 of the paper for U3g/V4g: the product form of the rows of a core mask. -/
theorem prodForm_row (Y r23 r43 r29 : ℕ) :
    ProdForm (repB 360 27720 Y ||| maskP 27720 23 r23 ||| maskP 27720 43 r43 ||| maskP 27720 29 r29) Y
      (phi7 r43 r29) (phi11 r23) := by
  intro e he
  rw [ind_or, ind_or, ind_or, ind_repB Y he, ind23 r23 he, ind43 r43 he, ind29 r29 he]
  unfold phi7 phi11
  ring

/-! ## The tables of the residues (decide) -/

/-- `Σ_{y < n} f(y)` as a list fold (for `decide`). -/
def lsum (n : ℕ) (f : ℕ → ℕ) : ℕ := (List.range n).foldl (fun acc y => acc + f y) 0

theorem lsum_eq (n : ℕ) (f : ℕ → ℕ) : lsum n f = ∑ y ∈ range n, f y := by
  unfold lsum; rw [foldl_range_add, zero_add]

/-- The tables of the residue pair number `i = 29 r43 + r29` are those of the pattern `σ < np7`. -/
def ok7 (i σ : ℕ) : Bool :=
  decide (σ < np7) && (List.range 4).all fun u =>
    (lsum 7 (phi7 (i / 29) (i % 29) u) == f7.getD (4 * σ + u) 0) && (List.range 4).all fun v =>
      lsum 7 (fun y => phi7 (i / 29) (i % 29) u y * phi7 (i / 29) (i % 29) v y) == q7.getD (16 * σ + 4 * u + v) 0

/-- The tables of the residue `r23 = i` are those of the pattern `σ < np11`. -/
def ok11 (i σ : ℕ) : Bool :=
  decide (σ < np11) && (List.range 4).all fun u =>
    (lsum 11 (phi11 i u) == f11.getD (4 * σ + u) 0) && (List.range 4).all fun v =>
      lsum 11 (fun y => phi11 i u y * phi11 i v y) == q11.getD (16 * σ + 4 * u + v) 0

/-- `ok i σ` along a list (the entries numbered from `i`). -/
def chkL (ok : ℕ → ℕ → Bool) : List ℕ → ℕ → Bool
  | [], _ => true
  | σ :: L, i => ok i σ && chkL ok L (i + 1)

theorem chkL_spec (ok : ℕ → ℕ → Bool) :
    ∀ (L : List ℕ) (i : ℕ), chkL ok L i = true → ∀ j < L.length, ok (i + j) (L.getD j 0) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | σ :: L, i, h, j, hj => by
    simp only [chkL, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := chkL_spec ok L (i + 1) h.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      simpa using this

set_option maxRecDepth 100000 in
theorem chk7 : chkL ok7 sig7.toList 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chk11 : chkL ok11 sig11.toList 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig7_length : sig7.toList.length = 1247 := by decide

set_option maxRecDepth 100000 in
theorem sig11_length : sig11.toList.length = 23 := by decide

theorem getD_toList (A : Array ℕ) (j : ℕ) : A.toList.getD j 0 = A.getD j 0 := by
  by_cases hj : j < A.size
  · rw [getD_eq_getElem' _ _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj), Array.getElem_toList]
  · rw [getD_eq_default' _ _ _ hj, List.getD_eq_default _ _ (by simpa using hj)]

theorem tab7 {r43 r29 : ℕ} (h43 : r43 < 43) (h29 : r29 < 29) :
    sig7.getD (29 * r43 + r29) 0 < np7 ∧ ∀ u < 4,
      fq 7 (phi7 r43 r29) u = f7.getD (4 * sig7.getD (29 * r43 + r29) 0 + u) 0 ∧ ∀ v < 4,
        ∑ y ∈ range 7, phi7 r43 r29 u y * phi7 r43 r29 v y =
          q7.getD (16 * sig7.getD (29 * r43 + r29) 0 + 4 * u + v) 0 := by
  have h := chkL_spec ok7 _ 0 chk7 (29 * r43 + r29) (by rw [sig7_length]; omega)
  rw [zero_add, getD_toList] at h
  have e1 : (29 * r43 + r29) / 29 = r43 := by omega
  have e2 : (29 * r43 + r29) % 29 = r29 := by omega
  simp only [ok7, e1, e2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨h.1, fun u hu => ⟨?_, fun v hv => ?_⟩⟩
  · rw [← (h.2 u hu).1]; unfold fq; rw [lsum_eq]
  · rw [← (h.2 u hu).2 v hv, lsum_eq]

theorem tab11 {r23 : ℕ} (h23 : r23 < 23) :
    sig11.getD r23 0 < np11 ∧ ∀ u < 4,
      fq 11 (phi11 r23) u = f11.getD (4 * sig11.getD r23 0 + u) 0 ∧ ∀ v < 4,
        ∑ y ∈ range 11, phi11 r23 u y * phi11 r23 v y = q11.getD (16 * sig11.getD r23 0 + 4 * u + v) 0 := by
  have h := chkL_spec ok11 _ 0 chk11 r23 (by rw [sig11_length]; omega)
  rw [zero_add, getD_toList] at h
  simp only [ok11, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨h.1, fun u hu => ⟨?_, fun v hv => ?_⟩⟩
  · rw [← (h.2 u hu).1]; unfold fq; rw [lsum_eq]
  · rw [← (h.2 u hu).2 v hv, lsum_eq]

/-! ## Regrouping by the patterns -/

theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∀ m, ∑ i ∈ range (m * n), f i = ∑ a ∈ range m, ∑ b ∈ range n, f (n * a + b)
  | 0 => by simp
  | m + 1 => by
    rw [show (m + 1) * n = m * n + n by ring, Finset.sum_range_add, sum_range_mul_split n f m, sum_range_succ]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [show m * n + b = n * m + b by ring]

theorem sum_range_getD {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∀ L : List ℕ, ∑ i ∈ range L.length, F (L.getD i 0) = (L.map F).sum
  | [] => by simp
  | σ :: L => by
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, ← sum_range_getD F L, add_comm]
    simp

theorem sum_map_count (F : ℕ → ℚ) (n : ℕ) :
    ∀ L : List ℕ, (∀ σ ∈ L, σ < n) → (L.map F).sum = ∑ a ∈ range n, (L.count a : ℚ) * F a
  | [], _ => by simp
  | σ :: L, h => by
    rw [List.map_cons, List.sum_cons, sum_map_count F n L (fun τ hτ => h τ (by simp [hτ]))]
    have hσ : σ < n := h σ (by simp)
    have e1 : ∀ a ∈ range n, ((σ :: L).count a : ℚ) * F a = (if σ = a then F a else 0) + (L.count a : ℚ) * F a := by
      intro a _
      rw [List.count_cons]
      by_cases ha : σ = a
      · subst ha; simp; ring
      · simp [ha, Ne.symm ha]
    rw [sum_congr rfl e1, sum_add_distrib, Finset.sum_ite_eq (range n) σ, if_pos (mem_range.mpr hσ)]

set_option maxRecDepth 100000 in
theorem count7 : (List.range np7).all (fun a => sig7.toList.count a == w7.getD a 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem count11 : (List.range np11).all (fun a => sig11.toList.count a == w11.getD a 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig7_lt : sig7.toList.all (· < np7) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig11_lt : sig11.toList.all (· < np11) = true := by decide +kernel

theorem regroup7 (F : ℕ → ℚ) :
    ∑ r43 ∈ range 43, ∑ r29 ∈ range 29, F (sig7.getD (29 * r43 + r29) 0) = ∑ a ∈ range np7, (w7.getD a 0 : ℚ) * F a := by
  rw [← sum_range_mul_split 29 (fun i => F (sig7.getD i 0)) 43]
  rw [show 43 * 29 = sig7.toList.length by rw [sig7_length]]
  rw [sum_congr rfl fun i _ => by rw [← getD_toList], sum_range_getD F sig7.toList]
  rw [sum_map_count F np7 sig7.toList (fun σ hσ => by
    have := List.all_eq_true.mp sig7_lt σ hσ; simpa using this)]
  refine sum_congr rfl fun a ha => ?_
  have := List.all_eq_true.mp count7 a (List.mem_range.mpr (mem_range.mp ha))
  rw [beq_iff_eq] at this
  rw [this]

theorem regroup11 (F : ℕ → ℚ) :
    ∑ r23 ∈ range 23, F (sig11.getD r23 0) = ∑ b ∈ range np11, (w11.getD b 0 : ℚ) * F b := by
  rw [show (23 : ℕ) = sig11.toList.length by rw [sig11_length]]
  rw [sum_congr rfl fun i _ => by rw [← getD_toList], sum_range_getD F sig11.toList]
  rw [sum_map_count F np11 sig11.toList (fun σ hσ => by
    have := List.all_eq_true.mp sig11_lt σ hσ; simpa using this)]
  refine sum_congr rfl fun b hb => ?_
  have := List.all_eq_true.mp count11 b (List.mem_range.mpr (mem_range.mp hb))
  rw [beq_iff_eq] at this
  rw [this]

/-- The sum over the residue triples of a function of the combined pattern `P = np11 σ7 + σ11`. -/
theorem regroup (G : ℕ → ℚ) :
    ∑ r23 ∈ range 23, ∑ r43 ∈ range 43, ∑ r29 ∈ range 29, G (np11 * sig7.getD (29 * r43 + r29) 0 + sig11.getD r23 0) =
      ∑ P ∈ range npC, (pwt P : ℚ) * G P := by
  have e1 : ∀ r23 ∈ range 23, (∑ r43 ∈ range 43, ∑ r29 ∈ range 29,
      G (np11 * sig7.getD (29 * r43 + r29) 0 + sig11.getD r23 0)) =
      ∑ a ∈ range np7, (w7.getD a 0 : ℚ) * G (np11 * a + sig11.getD r23 0) :=
    fun r23 _ => regroup7 (fun a => G (np11 * a + sig11.getD r23 0))
  rw [sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ a ∈ range np7, (∑ r23 ∈ range 23, (w7.getD a 0 : ℚ) * G (np11 * a + sig11.getD r23 0)) =
      ∑ b ∈ range np11, (w11.getD b 0 : ℚ) * ((w7.getD a 0 : ℚ) * G (np11 * a + b)) :=
    fun a _ => regroup11 (fun b => (w7.getD a 0 : ℚ) * G (np11 * a + b))
  rw [sum_congr rfl e2, show npC = np7 * np11 from rfl, sum_range_mul_split np11 (fun P => (pwt P : ℚ) * G P) np7]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b hb => ?_
  have hb' : b < np11 := mem_range.mp hb
  have e3 : (np11 * a + b) / np11 = a := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < np11), Nat.div_eq_of_lt hb', zero_add]
  have e4 : (np11 * a + b) % np11 = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
  unfold pwt
  rw [e3, e4]
  push_cast
  ring

end Romanoff.G.S2
