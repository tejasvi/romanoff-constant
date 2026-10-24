import Romanoff.E.S2.Arr

/-!
# U3e stage 2: the options of 37 (classes `j mod 36`) from the counts of the prefix row

* `crossLoop_spec`: the loop with the counters `a = x mod g`, `j = x mod 36`;
* `xOf_spec`, `zOf_spec`: `X[j] = Σ_i bn_i Σ_{x < L, x ≡ j (36)} N^g_{x mod g} N^L_x`, `Z[j] = Σ_i bn_i Σ_{x < L, x ≡ j} (N^L_x)^2`;
* `S_or`: `S_g(U \ C_j) = S_g(U) - 2 cross + sq` (CRT), `cnt_or`: `|U \ C_j| = |U| - N^36_j`;
* `Qs_or`: `Q(U \ C_j) = Q(U) + Z[j] - 2 X[j]`.
-/

open Finset R45 R45.EV

namespace Romanoff.E.S2

theorem succ_mod_eq {g : ℕ} (hg : 0 < g) (x : ℕ) : (if x % g + 1 = g then 0 else x % g + 1) = (x + 1) % g := by
  have h2 : x + 1 = (x % g + 1) + g * (x / g) := by have := Nat.mod_add_div x g; omega
  rw [h2, Nat.add_mul_mod_self_left]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact (Nat.mod_eq_of_lt (by have := Nat.mod_lt x hg; omega)).symm

theorem getD_modify (A : Array ℕ) (i j : ℕ) (f : ℕ → ℕ) (hi : i < A.size) :
    (A.modify i f).getD j 0 = if j = i then f (A.getD j 0) else A.getD j 0 := by
  by_cases hj : j < A.size
  · rw [getD_eq_getElem' _ _ _ (by simpa using hj), Array.getElem_modify, getD_eq_getElem' _ _ _ hj]
    by_cases hji : j = i
    · subst hji; simp
    · rw [if_neg (Ne.symm hji), if_neg hji]
  · rw [getD_eq_default' _ _ _ (by simpa using hj), getD_eq_default' _ _ _ hj]
    have : j ≠ i := fun h => hj (h ▸ hi)
    rw [if_neg this]

theorem crossLoop_spec (Ng NL : Array ℕ) {g : ℕ} (hg : 0 < g) :
    ∀ (n x0 : ℕ) (acc : Array ℕ), acc.size = 36 →
      (crossLoop Ng NL g n x0 (x0 % g) (x0 % 36) acc).size = 36 ∧
      ∀ j < 36, (crossLoop Ng NL g n x0 (x0 % g) (x0 % 36) acc).getD j 0 =
        acc.getD j 0 + ∑ x ∈ Ico x0 (x0 + n), if x % 36 = j then Ng.getD (x % g) 0 * NL.getD x 0 else 0
  | 0, x0, acc, h => by simp [crossLoop, h]
  | n + 1, x0, acc, h => by
    simp only [crossLoop]
    rw [succ_mod_eq hg, succ_mod_eq (show 0 < 36 by norm_num)]
    have hm : (acc.modify (x0 % 36) (· + Ng.getD (x0 % g) 0 * NL.getD x0 0)).size = 36 := by simp [h]
    obtain ⟨h1, h2⟩ := crossLoop_spec Ng NL hg n (x0 + 1) _ hm
    refine ⟨h1, fun j hj => ?_⟩
    rw [h2 j hj, Finset.sum_eq_sum_Ico_succ_bot (by omega : x0 < x0 + (n + 1)),
      getD_modify _ _ _ _ (by rw [h]; exact Nat.mod_lt _ (by norm_num)), show x0 + 1 + n = x0 + (n + 1) by ring]
    by_cases hj' : j = x0 % 36
    · rw [if_pos hj', if_pos hj'.symm]; ring
    · rw [if_neg hj', if_neg (Ne.symm hj')]; ring

theorem z36_size : z36.size = 36 := by simp [z36]

theorem z36_getD (j : ℕ) : z36.getD j 0 = 0 := by
  by_cases hj : j < 36
  · rw [getD_eq_getElem' _ _ _ (by rw [z36_size]; exact hj)]; simp [z36]
  · rw [getD_eq_default' _ _ _ (by rw [z36_size]; exact hj)]

/-- The divisor facts of the lcm indices. -/
theorem lIdx_facts : ∀ i < 48, lIdx.getD i 0 < 48 ∧ dA.getD i 0 ∣ dA.getD (lIdx.getD i 0) 0 ∧
    36 ∣ dA.getD (lIdx.getD i 0) 0 ∧ dA.getD (lIdx.getD i 0) 0 ∣ Nat.lcm (dA.getD i 0) 36 ∧
    isL (lIdx.getD i 0) = true := by decide

theorem dA_facts : ∀ i < 48, 0 < dA.getD i 0 ∧ dA.getD i 0 ∣ 3960 := by decide

theorem crossOf_size (X : ℕ) {i : ℕ} (hi : i < 48) : (crossOf (cfam (mrow X)) i).size = 36 := by
  have h := crossLoop_spec (cntArr X (dA.getD i 0)) (cntArr X (dA.getD (lIdx.getD i 0) 0)) (dA_facts i hi).1
    (dA.getD (lIdx.getD i 0) 0) 0 z36 z36_size
  simp only [Nat.zero_mod] at h
  unfold crossOf
  rw [cfam_spec X hi, cfam_spec X (lIdx_facts i hi).1]
  exact h.1

/-- `cross_i[j] = Σ_{x < L, x ≡ j (36)} N^g_{x mod g} N^L_x`. -/
theorem crossOf_spec (X : ℕ) {i : ℕ} (hi : i < 48) {j : ℕ} (hj : j < 36) :
    (crossOf (cfam (mrow X)) i).getD j 0 = ∑ x ∈ range (dA.getD (lIdx.getD i 0) 0),
      if x % 36 = j then cnt X (dA.getD i 0) (x % dA.getD i 0) * cnt X (dA.getD (lIdx.getD i 0) 0) x else 0 := by
  have hg := (dA_facts i hi).1
  have h := crossLoop_spec (cntArr X (dA.getD i 0)) (cntArr X (dA.getD (lIdx.getD i 0) 0)) hg
    (dA.getD (lIdx.getD i 0) 0) 0 z36 z36_size
  simp only [Nat.zero_mod] at h
  unfold crossOf
  rw [cfam_spec X hi, cfam_spec X (lIdx_facts i hi).1, h.2 j hj, z36_getD, zero_add, zero_add, range_eq_Ico]
  apply sum_congr rfl
  intro x hx
  rw [cntArr_getD X _ _ (Nat.mod_lt _ hg), cntArr_getD X _ _ (mem_Ico.mp hx).2]

theorem sqOf_size (X : ℕ) {k : ℕ} (hk : k < 48) : (sqOf (cfam (mrow X)) k).size = 36 := by
  have h := crossLoop_spec (cntArr X (dA.getD k 0)) (cntArr X (dA.getD k 0)) (dA_facts k hk).1
    (dA.getD k 0) 0 z36 z36_size
  simp only [Nat.zero_mod] at h
  unfold sqOf
  rw [cfam_spec X hk]
  exact h.1

/-- `sq_k[j] = Σ_{x < h, x ≡ j (36)} (N^h_x)^2`, `h = dA[k]`. -/
theorem sqOf_spec (X : ℕ) {k : ℕ} (hk : k < 48) {j : ℕ} (hj : j < 36) :
    (sqOf (cfam (mrow X)) k).getD j 0 =
      ∑ x ∈ range (dA.getD k 0), if x % 36 = j then cnt X (dA.getD k 0) x ^ 2 else 0 := by
  have hg := (dA_facts k hk).1
  have h := crossLoop_spec (cntArr X (dA.getD k 0)) (cntArr X (dA.getD k 0)) hg (dA.getD k 0) 0 z36 z36_size
  simp only [Nat.zero_mod] at h
  unfold sqOf
  rw [cfam_spec X hk, h.2 j hj, z36_getD, zero_add, zero_add, range_eq_Ico]
  apply sum_congr rfl
  intro x hx
  have hx' := (mem_Ico.mp hx).2
  rw [Nat.mod_eq_of_lt hx', cntArr_getD X _ _ hx', pow_two]

theorem axpy_size (c : ℕ) (v acc : Array ℕ) (hv : v.size = 36) (ha : acc.size = 36) : (axpy c v acc).size = 36 := by
  simp [axpy, hv, ha]

theorem axpy_getD (c : ℕ) (v acc : Array ℕ) (hv : v.size = acc.size) (j : ℕ) (hj : j < acc.size) :
    (axpy c v acc).getD j 0 = acc.getD j 0 + c * v.getD j 0 := by
  rw [getD_eq_getElem' _ _ _ (by simp [axpy, hv, hj]), getD_eq_getElem' _ _ _ hj,
    getD_eq_getElem' _ _ _ (by rw [hv]; exact hj)]
  simp [axpy]

theorem foldl_axpy (b : ℕ → ℕ) (W : ℕ → Array ℕ) :
    ∀ n, (∀ i < n, (W i).size = 36) → ((List.range n).foldl (fun acc i => axpy (b i) (W i) acc) z36).size = 36 ∧
      ∀ j < 36, ((List.range n).foldl (fun acc i => axpy (b i) (W i) acc) z36).getD j 0 =
        ∑ i ∈ range n, b i * (W i).getD j 0
  | 0, _ => by
    refine ⟨z36_size, fun j _ => ?_⟩
    simp only [List.range_zero, List.foldl_nil, sum_range_zero]
    exact z36_getD j
  | n + 1, hW => by
    obtain ⟨h1, h2⟩ := foldl_axpy b W n fun i hi => hW i (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hn := hW n (by omega)
    refine ⟨axpy_size _ _ _ hn h1, fun j hj => ?_⟩
    rw [axpy_getD _ _ _ (by rw [hn, h1]) j (by rw [h1]; exact hj), h2 j hj, sum_range_succ]

/-- `X[j] = Σ_i bn_i cross_i[j]`. -/
theorem xOf_spec (X : ℕ) {j : ℕ} (hj : j < 36) :
    (xOf (cfam (mrow X))).getD j 0 = ∑ i ∈ range 48, bnA.getD i 0 * (crossOf (cfam (mrow X)) i).getD j 0 :=
  (foldl_axpy (fun i => bnA.getD i 0) (fun i => crossOf (cfam (mrow X)) i) 48
    (fun i hi => crossOf_size X hi)).2 j hj

theorem sqFam_getD (X : ℕ) {k : ℕ} (hk : k < 48) (hL : isL k = true) :
    (sqFam (cfam (mrow X))).getD k #[] = sqOf (cfam (mrow X)) k := by
  rw [getD_eq_getElem' _ _ _ (by simp [sqFam, hk])]
  simp [sqFam, hL]

/-- `Z[j] = Σ_i bn_i sq_{lIdx[i]}[j]`. -/
theorem zOf_spec (X : ℕ) {j : ℕ} (hj : j < 36) :
    (zOf (cfam (mrow X))).getD j 0 =
      ∑ i ∈ range 48, bnA.getD i 0 * (sqOf (cfam (mrow X)) (lIdx.getD i 0)).getD j 0 := by
  unfold zOf
  simp only
  rw [(foldl_axpy (fun i => bnA.getD i 0) (fun i => (sqFam (cfam (mrow X))).getD (lIdx.getD i 0) #[]) 48
    (fun i hi => by
      rw [sqFam_getD X (lIdx_facts i hi).1 (lIdx_facts i hi).2.2.2.2]
      exact sqOf_size X (lIdx_facts i hi).1)).2 j hj]
  apply sum_congr rfl
  intro i hi
  rw [sqFam_getD X (lIdx_facts i (mem_range.mp hi)).1 (lIdx_facts i (mem_range.mp hi)).2.2.2.2]

/-! ## Removing the class `j mod 36` -/

theorem testBit_cmask36 (j e : ℕ) : (cmask36 j).testBit e = (decide (e < 3960) && decide (e % 36 = j)) := by
  unfold cmask36
  rw [testBit_foldl_or 3960 (fun e => e % 36 = j) 3960 0 e]
  simp

theorem ind_or (X : ℕ) {j e : ℕ} (he : e < 3960) : ind (X ||| cmask36 j) e = if e % 36 = j then 0 else ind X e := by
  unfold ind
  rw [Nat.testBit_or, testBit_cmask36]
  by_cases h : e % 36 = j <;> cases X.testBit e <;> simp [h, he]

/-- `|U \ C_j| + N^36_j = |U|`. -/
theorem cnt_or (X : ℕ) {j : ℕ} : cnt (X ||| cmask36 j) 1 0 + cnt X 36 j = cnt X 1 0 := by
  unfold cnt
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  rw [ind_or X (mem_range.mp he), Nat.mod_one]
  by_cases h : e % 36 = j <;> simp [h]

/-- The cross term `Σ_{x < L, x ≡ j (36)} N^g_{x mod g} N^L_x`. -/
def crossV (X g L j : ℕ) : ℕ := ∑ x ∈ range L, if x % 36 = j then cnt X g (x % g) * cnt X L x else 0

/-- The square term `Σ_{x < L, x ≡ j (36)} (N^L_x)^2`. -/
def sqV (X L j : ℕ) : ℕ := ∑ x ∈ range L, if x % 36 = j then cnt X L x ^ 2 else 0

theorem sum_x_collapse {L : ℕ} (hL : 0 < L) (y : ℕ) (P : ℕ → Prop) [DecidablePred P] (v : ℕ) :
    (∑ x ∈ range L, if y % L = x ∧ P x then v else 0) = if P (y % L) then v else 0 := by
  have : ∀ x ∈ range L, (if y % L = x ∧ P x then v else 0) = if y % L = x then (if P x then v else 0) else 0 := by
    intro x _; by_cases h : y % L = x <;> simp [h]
  rw [sum_congr rfl this, Finset.sum_ite_eq, if_pos (mem_range.mpr (Nat.mod_lt _ hL))]

theorem crossV_eq (X : ℕ) {g L j : ℕ} (hL0 : 0 < L) (hgL : g ∣ L) (h36L : 36 ∣ L) :
    crossV X g L j = ∑ e ∈ range 3960, ∑ e' ∈ range 3960,
      if e % g = e' % g ∧ e % 36 = j then ind X e * ind X e' else 0 := by
  unfold crossV cnt
  have h1 : ∀ x ∈ range L, (if x % 36 = j then (∑ e' ∈ range 3960, if e' % g = x % g then ind X e' else 0) *
      (∑ e ∈ range 3960, if e % L = x then ind X e else 0) else 0) =
      ∑ e ∈ range 3960, ∑ e' ∈ range 3960,
        if e % L = x ∧ (x % 36 = j ∧ e' % g = x % g) then ind X e * ind X e' else 0 := by
    intro x _
    by_cases hx : x % 36 = j
    · rw [if_pos hx, sum_mul_sum, Finset.sum_comm]
      apply sum_congr rfl; intro e _; apply sum_congr rfl; intro e' _
      by_cases h1 : e % L = x <;> by_cases h2 : e' % g = x % g <;> simp [h1, h2, hx, mul_comm]
    · rw [if_neg hx]; symm
      apply sum_eq_zero; intro e _; apply sum_eq_zero; intro e' _; simp [hx]
  rw [sum_congr rfl h1, Finset.sum_comm]
  apply sum_congr rfl; intro e _
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro e' _
  rw [sum_x_collapse hL0 e (fun x => x % 36 = j ∧ e' % g = x % g), Nat.mod_mod_of_dvd _ h36L,
    Nat.mod_mod_of_dvd _ hgL]
  by_cases h1 : e % 36 = j <;> by_cases h2 : e % g = e' % g <;> simp [h1, h2, eq_comm]

theorem crt_iff {g L e e' j : ℕ} (hgL : g ∣ L) (h36L : 36 ∣ L) (hLl : L ∣ Nat.lcm g 36) :
    (e % 36 = j ∧ e' % L = e % L) ↔ (e % g = e' % g ∧ e % 36 = j ∧ e' % 36 = j) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hg : e' % L % g = e % L % g := by rw [h2]
    have h3 : e' % L % 36 = e % L % 36 := by rw [h2]
    rw [Nat.mod_mod_of_dvd _ hgL, Nat.mod_mod_of_dvd _ hgL] at hg
    rw [Nat.mod_mod_of_dvd _ h36L, Nat.mod_mod_of_dvd _ h36L] at h3
    exact ⟨hg.symm, h1, h3.trans h1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_⟩
    have hm : e' ≡ e [MOD Nat.lcm g 36] := Nat.mod_lcm h1.symm (h3.trans h2.symm)
    exact Nat.ModEq.of_dvd hLl hm

theorem sqV_eq (X : ℕ) {g L j : ℕ} (hL0 : 0 < L) (hgL : g ∣ L) (h36L : 36 ∣ L) (hLl : L ∣ Nat.lcm g 36) :
    sqV X L j = ∑ e ∈ range 3960, ∑ e' ∈ range 3960,
      if e % g = e' % g ∧ e % 36 = j ∧ e' % 36 = j then ind X e * ind X e' else 0 := by
  unfold sqV cnt
  have h1 : ∀ x ∈ range L, (if x % 36 = j then (∑ e ∈ range 3960, if e % L = x then ind X e else 0) ^ 2 else 0) =
      ∑ e ∈ range 3960, ∑ e' ∈ range 3960,
        if e % L = x ∧ (x % 36 = j ∧ e' % L = x) then ind X e * ind X e' else 0 := by
    intro x _
    by_cases hx : x % 36 = j
    · rw [if_pos hx, pow_two, sum_mul_sum]
      apply sum_congr rfl; intro e _; apply sum_congr rfl; intro e' _
      by_cases h1 : e % L = x <;> by_cases h2 : e' % L = x <;> simp [h1, h2, hx]
    · rw [if_neg hx]; symm
      apply sum_eq_zero; intro e _; apply sum_eq_zero; intro e' _; simp [hx]
  rw [sum_congr rfl h1, Finset.sum_comm]
  apply sum_congr rfl; intro e _
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro e' _
  rw [sum_x_collapse hL0 e (fun x => x % 36 = j ∧ e' % L = x), Nat.mod_mod_of_dvd _ h36L]
  by_cases h : e % 36 = j ∧ e' % L = e % L
  · rw [if_pos h, if_pos ((crt_iff hgL h36L hLl).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((crt_iff hgL h36L hLl).mpr h'))]

/-- `S_g(U \ C_j) + 2 cross = S_g(U) + sq` (natural numbers). -/
theorem S_or (X : ℕ) {g L j : ℕ} (hg0 : 0 < g) (hL0 : 0 < L) (hgL : g ∣ L) (h36L : 36 ∣ L)
    (hLl : L ∣ Nat.lcm g 36) :
    S (X ||| cmask36 j) g + 2 * crossV X g L j = S X g + sqV X L j := by
  have hc' : crossV X g L j = ∑ e ∈ range 3960, ∑ e' ∈ range 3960,
      if e % g = e' % g ∧ e' % 36 = j then ind X e * ind X e' else 0 := by
    rw [crossV_eq X hL0 hgL h36L, Finset.sum_comm]
    apply sum_congr rfl; intro e _; apply sum_congr rfl; intro e' _
    by_cases h1 : e' % g = e % g
    · simp [h1, mul_comm]
    · simp [h1, Ne.symm h1]
  rw [two_mul]
  nth_rewrite 1 [crossV_eq X hL0 hgL h36L]
  rw [hc', S_double _ hg0, S_double _ hg0, sqV_eq X hL0 hgL h36L hLl, ← sum_add_distrib, ← sum_add_distrib,
    ← sum_add_distrib]
  apply sum_congr rfl; intro e he
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro e' he'
  rw [ind_or X (mem_range.mp he), ind_or X (mem_range.mp he')]
  by_cases hg : e % g = e' % g <;> by_cases h1 : e % 36 = j <;> by_cases h2 : e' % 36 = j <;> simp [hg, h1, h2]

theorem Qs_or (X : ℕ) {j : ℕ} (hj : j < 36) :
    Qs (X ||| cmask36 j) + 2 * (xOf (cfam (mrow X))).getD j 0 = Qs X + (zOf (cfam (mrow X))).getD j 0 := by
  rw [xOf_spec X hj, zOf_spec X hj]
  unfold Qs
  have key : ∀ i ∈ range 48, bnA.getD i 0 * (S (X ||| cmask36 j) (dA.getD i 0) +
      2 * (crossOf (cfam (mrow X)) i).getD j 0) =
      bnA.getD i 0 * (S X (dA.getD i 0) + (sqOf (cfam (mrow X)) (lIdx.getD i 0)).getD j 0) := by
    intro i hi
    have hi' := mem_range.mp hi
    obtain ⟨hk, hgL, h36L, hLl, _⟩ := lIdx_facts i hi'
    obtain ⟨hg0, _⟩ := dA_facts i hi'
    obtain ⟨hL0, _⟩ := dA_facts _ hk
    rw [crossOf_spec X hi' hj, sqOf_spec X hk hj]
    exact congrArg (bnA.getD i 0 * ·) (S_or X (j := j) hg0 hL0 hgL h36L hLl)
  calc (∑ i ∈ range 48, bnA.getD i 0 * S (X ||| cmask36 j) (dA.getD i 0)) +
        2 * ∑ i ∈ range 48, bnA.getD i 0 * (crossOf (cfam (mrow X)) i).getD j 0
      = ∑ i ∈ range 48, bnA.getD i 0 * (S (X ||| cmask36 j) (dA.getD i 0) +
          2 * (crossOf (cfam (mrow X)) i).getD j 0) := by
        rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro i _; ring
    _ = ∑ i ∈ range 48, bnA.getD i 0 * (S X (dA.getD i 0) + (sqOf (cfam (mrow X)) (lIdx.getD i 0)).getD j 0) :=
        sum_congr rfl key
    _ = _ := by rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; ring

end Romanoff.E.S2
