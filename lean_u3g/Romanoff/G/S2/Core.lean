import Romanoff.G.S2.Basic

/-!
# U3g/V4g stage 2: the core rows (period 360) of the evaluator

For a core mask `Y` (the core row `C = {x < 360 : x ∉ Y}`):
* `cfam_spec`: the count family of `mrow Y` is `cntArr Y (dC[i])` at every index (the count plan at 360);
* `cls4_eq`: the class rows are `mrow (nm4 u)`, `nm4 u = {x < 360 : x ≢ u (4)}`, so `zmul (mrow Y) (cls4 u)` is the row of
  `C_u = {x ∈ C : x ≡ u (4)}`;
* `Tc Y h u v = Σ_{x, x' < 360, x ≡ x' (h), x ≡ u, x' ≡ v (4)} [x ∉ Y] [x' ∉ Y]`, and `Tc_eq_dot`: for `h ∣ 360`,
  `Tc Y h u v = Σ_{a < h} N^h_a(C_u) N^h_a(C_v)`;
* `tOf_spec`, `zOf_spec`, `n4_spec`: the arrays `T`, `Z` and the class sizes `n_u` of `rowStep`.
-/

open Finset R45 R45.EVG

namespace Romanoff.G.S2

theorem getD_eq_getElem' {α : Type*} (A : Array α) (i : ℕ) (d : α) (h : i < A.size) : A.getD i d = A[i] := by
  simp [Array.getD, h]

theorem getD_eq_default' {α : Type*} (A : Array α) (i : ℕ) (d : α) (h : ¬ i < A.size) : A.getD i d = d := by
  simp [Array.getD, h]

theorem getD_setIfInBounds {α : Type*} (A : Array α) (i j : ℕ) (v d : α) (hi : i < A.size) :
    (A.setIfInBounds i v).getD j d = if j = i then v else A.getD j d := by
  by_cases hj : j < A.size
  · rw [getD_eq_getElem' _ _ _ (by simpa using hj), Array.getElem_setIfInBounds (by simpa using hj)]
    by_cases hji : j = i
    · subst hji; simp
    · rw [if_neg (Ne.symm hji), if_neg hji, getD_eq_getElem' _ _ _ hj]
  · rw [getD_eq_default' _ _ _ (by simpa using hj), getD_eq_default' _ _ _ hj]
    have : j ≠ i := fun h => hj (h ▸ hi)
    rw [if_neg this]

theorem foldl_range_add (f : ℕ → ℕ) : ∀ (n a : ℕ), (List.range n).foldl (fun acc i => acc + f i) a = a + ∑ i ∈ range n, f i
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_range_add f n a, List.foldl_cons, List.foldl_nil, sum_range_succ]
    ring

theorem dC_facts : ∀ c < 24, 0 < dC.getD c 0 ∧ dC.getD c 0 ∣ 360 := by decide

/-! ## Rows -/

theorem mrow_size (m : ℕ) : (mrow m).size = 360 := by simp [mrow]

theorem mrow_getD (m x : ℕ) (hx : x < 360) : (mrow m).getD x 0 = ind m x := by
  rw [getD_eq_getElem' _ _ _ (by rw [mrow_size]; exact hx)]
  simp [mrow, ind]

theorem zmul_mrow (x m : ℕ) : zmul (mrow x) (mrow m) = mrow (x ||| m) := by
  apply Array.ext
  · simp [zmul, mrow_size]
  · intro i h1 h2
    simp only [zmul, Array.getElem_zipWith, mrow, Array.getElem_ofFn, Nat.testBit_or]
    cases x.testBit i <;> cases m.testBit i <;> simp

/-- The 360-bit mask of the residues `x ≢ u (mod 4)`. -/
def nm4 (u : ℕ) : ℕ := (List.range 360).foldl (fun acc x => if x % 4 ≠ u then acc ||| (1 <<< x) else acc) 0

theorem nm4_testBit (u x : ℕ) : (nm4 u).testBit x = (decide (x < 360) && decide (x % 4 ≠ u)) := by
  unfold nm4
  rw [testBit_foldl_or 360 (fun x => x % 4 ≠ u) 360 0 x]
  simp

theorem cls4_eq (u : ℕ) : cls4 u = mrow (nm4 u) := by
  apply Array.ext
  · simp [cls4, mrow_size]
  · intro i h1 h2
    have hi : i < 360 := by simpa [cls4] using h1
    simp only [cls4, mrow, Array.getElem_ofFn, nm4_testBit]
    by_cases h : i % 4 = u <;> simp [h, hi]

theorem c4_getD (u : ℕ) (hu : u < 4) : c4.getD u #[] = mrow (nm4 u) := by
  rw [← cls4_eq]
  interval_cases u <;> simp [c4]

theorem ind_or_nm4 (Y u x : ℕ) (hx : x < 360) : ind (Y ||| nm4 u) x = ind Y x * (if x % 4 = u then 1 else 0) := by
  unfold ind
  rw [Nat.testBit_or, nm4_testBit]
  by_cases h : x % 4 = u <;> cases Y.testBit x <;> simp [h, hx]

/-! ## The count family at period 360 -/

/-- The count array `N^h_a(Y)`, `a < h`, at period 360. -/
def cntArr (Y h : ℕ) : Array ℕ := Array.ofFn (n := h) fun a => cntP 360 Y h a.val

theorem cntArr_size (Y h : ℕ) : (cntArr Y h).size = h := by simp [cntArr]

theorem cntArr_getD (Y h a : ℕ) (ha : a < h) : (cntArr Y h).getD a 0 = cntP 360 Y h a := by
  rw [getD_eq_getElem' _ _ _ (by rw [cntArr_size]; exact ha)]
  simp [cntArr]

theorem cntArr_360 (Y : ℕ) : cntArr Y 360 = mrow Y := by
  apply Array.ext
  · rw [cntArr_size, mrow_size]
  · intro i h1 h2
    rw [cntArr_size] at h1
    rw [← getD_eq_getElem' _ _ 0 (by rw [cntArr_size]; exact h1), ← getD_eq_getElem' _ _ 0 h2,
      cntArr_getD Y 360 i h1, mrow_getD Y i h1, cntP_top 360 Y h1]

theorem sumT_eq (A : Array ℕ) (a h : ℕ) :
    ∀ q acc, sumT A a h q acc = acc + ∑ t ∈ range q, A.getD (a + h * t) 0
  | 0, acc => by simp [sumT]
  | q + 1, acc => by
    rw [sumT, sumT_eq A a h q, sum_range_succ]
    ring

theorem red_cntArr (Y : ℕ) {h q : ℕ} (hh : 0 < h) (hq : 0 < q) : red (cntArr Y (h * q)) h q = cntArr Y h := by
  apply Array.ext
  · simp [red, cntArr_size]
  · intro a h1 h2
    have ha : a < h := by simpa [red] using h1
    rw [← getD_eq_getElem' _ _ 0 h1, ← getD_eq_getElem' _ _ 0 h2, cntArr_getD Y h a ha]
    rw [getD_eq_getElem' _ _ _ h1]
    simp only [red, Array.getElem_ofFn]
    rw [sumT_eq, zero_add, cntP_split 360 Y hh hq ha]
    apply sum_congr rfl
    intro t ht
    have : a + h * t < h * q := by
      have := mem_range.mp ht
      calc a + h * t < h + h * t := by omega
        _ = h * (t + 1) := by ring
        _ ≤ h * q := Nat.mul_le_mul_left _ this
    rw [cntArr_getD Y (h * q) _ this]

/-- The plan is valid from the done list `D`: every parent is done, `dC[I] = dC[i] q`, `q > 0`, `dC[i] > 0`, `i < 24`. -/
def planOKb : List (ℕ × ℕ × ℕ) → List ℕ → Bool
  | [], _ => true
  | s :: pl, D => (D.contains s.2.1 && dC.getD s.2.1 0 == dC.getD s.1 0 * s.2.2 && decide (0 < s.2.2) &&
      decide (0 < dC.getD s.1 0) && decide (s.1 < 24)) && planOKb pl (s.1 :: D)

/-- The indices done after the plan. -/
def planDone : List (ℕ × ℕ × ℕ) → List ℕ → List ℕ
  | [], D => D
  | s :: pl, D => planDone pl (s.1 :: D)

theorem planOK : planOKb plan [23] = true := by decide

theorem planDone_all : ∀ i < 24, i ∈ planDone plan [23] := by decide

/-- The invariant: 24 entries, and the done entries are the count arrays. -/
def Inv (Y : ℕ) (D : List ℕ) (cs : Array (Array ℕ)) : Prop :=
  cs.size = 24 ∧ ∀ i ∈ D, cs.getD i #[] = cntArr Y (dC.getD i 0)

theorem fold_inv (Y : ℕ) : ∀ (pl : List (ℕ × ℕ × ℕ)) (D : List ℕ) (cs : Array (Array ℕ)),
    planOKb pl D = true → Inv Y D cs → Inv Y (planDone pl D) (pl.foldl cstep cs)
  | [], D, cs, _, hI => hI
  | (i, I, q) :: pl, D, cs, hok, hI => by
    simp only [planOKb, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨hID, hdq⟩, hq⟩, hdi⟩, hi⟩, hrest⟩ := hok
    rw [List.foldl_cons]
    apply fold_inv Y pl (i :: D) _ hrest
    have hsz := hI.1
    refine ⟨by simp [cstep, hsz], ?_⟩
    intro j hj
    unfold cstep
    simp only
    rw [getD_setIfInBounds _ _ _ _ _ (by rw [hsz]; exact hi)]
    by_cases hji : j = i
    · rw [if_pos hji, hji, hI.2 I hID, hdq, red_cntArr Y hdi hq]
    · rw [if_neg hji]
      exact hI.2 j ((List.mem_cons.mp hj).resolve_left hji)

theorem dC_23 : dC.getD 23 0 = 360 := by decide

theorem inv0 (Y : ℕ) : Inv Y [23] (cfam0 (mrow Y)) := by
  refine ⟨by simp [cfam0], ?_⟩
  intro j hj
  rw [List.mem_singleton.mp hj, cfam0, getD_setIfInBounds _ _ _ _ _ (by simp), if_pos rfl, dC_23, cntArr_360]

theorem cfam_spec (Y : ℕ) {i : ℕ} (hi : i < 24) : (cfam (mrow Y)).getD i #[] = cntArr Y (dC.getD i 0) :=
  (fold_inv Y plan [23] _ planOK (inv0 Y)).2 i (planDone_all i hi)

/-! ## `T`, `Z` and the class sizes -/

/-- `T_h(u, v) = Σ_{x, x' < 360, x ≡ x' (h), x ≡ u, x' ≡ v (4)} [x ∉ Y] [x' ∉ Y]`. -/
def Tc (Y h u v : ℕ) : ℕ :=
  ∑ x ∈ range 360, ∑ x' ∈ range 360, if x % h = x' % h ∧ x % 4 = u ∧ x' % 4 = v then ind Y x * ind Y x' else 0

theorem Tc_eq_dot (Y : ℕ) {h : ℕ} (hh : 0 < h) (u v : ℕ) :
    Tc Y h u v = ∑ a ∈ range h, cntP 360 (Y ||| nm4 u) h a * cntP 360 (Y ||| nm4 v) h a := by
  rw [dotP_double 360 _ _ hh]
  unfold Tc
  refine sum_congr rfl fun x hx => sum_congr rfl fun x' hx' => ?_
  rw [ind_or_nm4 Y u x (mem_range.mp hx), ind_or_nm4 Y v x' (mem_range.mp hx')]
  by_cases h1 : x % h = x' % h <;> by_cases h2 : x % 4 = u <;> by_cases h3 : x' % 4 = v <;> simp [h1, h2, h3]

theorem Tc_symm (Y h u v : ℕ) : Tc Y h u v = Tc Y h v u := by
  unfold Tc
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
  by_cases h1 : x % h = x' % h <;> by_cases h2 : x % 4 = v <;> by_cases h3 : x' % 4 = u <;>
    simp [h1, h2, h3, Eq.comm, mul_comm]

theorem dotL_eq (A B : Array ℕ) : ∀ n acc, dotL A B n acc = acc + ∑ a ∈ range n, A.getD a 0 * B.getD a 0
  | 0, acc => by simp [dotL]
  | n + 1, acc => by
    rw [dotL, dotL_eq A B n, sum_range_succ]
    ring

/-- The count families of the four class rows of `mrow Y`. -/
def csOf (Y : ℕ) : Array (Array (Array ℕ)) := c4.map fun m => cfam (zmul (mrow Y) m)

theorem csOf_getD (Y u : ℕ) (hu : u < 4) : (csOf Y).getD u #[] = cfam (mrow (Y ||| nm4 u)) := by
  have hs : u < (csOf Y).size := by simp [csOf, c4]; omega
  rw [getD_eq_getElem' _ _ _ hs]
  simp only [csOf, Array.getElem_map]
  rw [← getD_eq_getElem' c4 u #[] (by simp [c4]; omega), c4_getD u hu, zmul_mrow]

theorem pu_lt : ∀ k < 10, pu.getD k 0 < 4 := by decide
theorem pv_lt : ∀ k < 10, pv.getD k 0 < 4 := by decide

theorem tOf_spec (Y : ℕ) {c k : ℕ} (hc : c < 24) (hk : k < 10) :
    (tOf (csOf Y)).getD (10 * c + k) 0 = Tc Y (dC.getD c 0) (pu.getD k 0) (pv.getD k 0) := by
  have hi : 10 * c + k < 240 := by omega
  rw [getD_eq_getElem' _ _ _ (by simp [tOf]; exact hi)]
  simp only [tOf, Array.getElem_ofFn]
  have e1 : (10 * c + k) % 10 = k := by omega
  have e2 : (10 * c + k) / 10 = c := by omega
  rw [e1, e2, csOf_getD Y _ (pu_lt k hk), csOf_getD Y _ (pv_lt k hk), cfam_spec _ hc, cfam_spec _ hc, dotL_eq, zero_add,
    Tc_eq_dot Y (dC_facts c hc).1]
  refine sum_congr rfl fun a ha => ?_
  rw [cntArr_getD _ _ _ (mem_range.mp ha), cntArr_getD _ _ _ (mem_range.mp ha)]

theorem zOf_spec (T : Array ℕ) {t k : ℕ} (ht : t < 4) (hk : k < 10) :
    (zOf T).getD (10 * t + k) 0 = ∑ c ∈ range 24, bnC.getD (24 * t + c) 0 * T.getD (10 * c + k) 0 := by
  have hi : 10 * t + k < 40 := by omega
  rw [getD_eq_getElem' _ _ _ (by simp [zOf]; exact hi)]
  simp only [zOf, Array.getElem_ofFn]
  have e1 : (10 * t + k) % 10 = k := by omega
  have e2 : (10 * t + k) / 10 = t := by omega
  rw [e1, e2, foldl_range_add, zero_add]

theorem cnt1_or_nm4 (Y u : ℕ) : cntP 360 (Y ||| nm4 u) 1 0 = cntP 360 Y 4 u := by
  unfold cntP
  refine sum_congr rfl fun x hx => ?_
  rw [ind_or_nm4 Y u x (mem_range.mp hx), Nat.mod_one, if_pos rfl]
  by_cases h : x % 4 = u <;> simp [h]

theorem n4_spec (Y u : ℕ) (hu : u < 4) :
    ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0).getD u 0 = cntP 360 Y 4 u := by
  have hs : u < ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0).size := by simp [csOf, c4]; omega
  rw [getD_eq_getElem' _ _ _ hs]
  simp only [Array.getElem_map]
  rw [← getD_eq_getElem' (csOf Y) u #[] (by simpa using hs), csOf_getD Y u hu, cfam_spec _ (by norm_num),
    show dC.getD 0 0 = 1 by decide, cntArr_getD _ 1 0 Nat.one_pos, cnt1_or_nm4]

end Romanoff.G.S2
