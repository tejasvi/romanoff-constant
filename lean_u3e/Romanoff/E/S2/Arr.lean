import Romanoff.E.S2.Basic

/-!
# U3e stage 2: the count arrays of the evaluator

* `zmul_mrow`: `zmul (mrow x) (mrow m) = mrow (x ||| m)` (rows of the exclusion masks);
* `cfam_spec`: the count family of `mrow X` is `cntArr X (dA[i])` at every index (`red_cntArr` and the count plan);
* `qOf_cfam`: `qOf (cfam (mrow X)) = Qs X`.
-/

open Finset R45 R45.EV

namespace Romanoff.E.S2

theorem getD_eq_getElem' {α : Type*} (A : Array α) (i : ℕ) (d : α) (h : i < A.size) : A.getD i d = A[i] := by
  simp [Array.getD, h]

theorem getD_eq_default' {α : Type*} (A : Array α) (i : ℕ) (d : α) (h : ¬ i < A.size) : A.getD i d = d := by
  simp [Array.getD, h]

theorem mrow_size (m : ℕ) : (mrow m).size = 3960 := by simp [mrow]

theorem mrow_getD (m e : ℕ) (he : e < 3960) : (mrow m).getD e 0 = ind m e := by
  rw [getD_eq_getElem' _ _ _ (by rw [mrow_size]; exact he)]
  simp [mrow, ind]

theorem zmul_mrow (x m : ℕ) : zmul (mrow x) (mrow m) = mrow (x ||| m) := by
  apply Array.ext
  · simp [zmul, mrow_size]
  · intro i h1 h2
    simp only [zmul, Array.getElem_zipWith, mrow, Array.getElem_ofFn, Nat.testBit_or]
    cases x.testBit i <;> cases m.testBit i <;> simp

/-- The count array `N^h_a(X)`, `a < h`. -/
def cntArr (X h : ℕ) : Array ℕ := Array.ofFn (n := h) fun a => cnt X h a.val

theorem cntArr_size (X h : ℕ) : (cntArr X h).size = h := by simp [cntArr]

theorem cntArr_getD (X h a : ℕ) (ha : a < h) : (cntArr X h).getD a 0 = cnt X h a := by
  rw [getD_eq_getElem' _ _ _ (by rw [cntArr_size]; exact ha)]
  simp [cntArr]

theorem cntArr_3960 (X : ℕ) : cntArr X 3960 = mrow X := by
  apply Array.ext
  · rw [cntArr_size, mrow_size]
  · intro i h1 h2
    rw [cntArr_size] at h1
    rw [← getD_eq_getElem' _ _ 0 (by rw [cntArr_size]; exact h1), ← getD_eq_getElem' _ _ 0 h2,
      cntArr_getD X 3960 i h1, mrow_getD X i h1, cnt_3960 X h1]

theorem sumT_eq (A : Array ℕ) (a h : ℕ) :
    ∀ q acc, sumT A a h q acc = acc + ∑ t ∈ range q, A.getD (a + h * t) 0
  | 0, acc => by simp [sumT]
  | q + 1, acc => by
    rw [sumT, sumT_eq A a h q, sum_range_succ]
    ring

theorem red_cntArr (X : ℕ) {h q : ℕ} (hh : 0 < h) (hq : 0 < q) : red (cntArr X (h * q)) h q = cntArr X h := by
  apply Array.ext
  · simp [red, cntArr_size]
  · intro a h1 h2
    have ha : a < h := by simpa [red] using h1
    rw [← getD_eq_getElem' _ _ 0 h1, ← getD_eq_getElem' _ _ 0 h2, cntArr_getD X h a ha]
    rw [getD_eq_getElem' _ _ _ h1]
    simp only [red, Array.getElem_ofFn]
    rw [sumT_eq, zero_add, cnt_split X hh hq ha]
    apply sum_congr rfl
    intro t ht
    have : a + h * t < h * q := by
      have := mem_range.mp ht
      calc a + h * t < h + h * t := by omega
        _ = h * (t + 1) := by ring
        _ ≤ h * q := Nat.mul_le_mul_left _ this
    rw [cntArr_getD X (h * q) _ this]

/-! ## The count plan -/

/-- The plan is valid from the done list `D`: every parent is done, `dA[I] = dA[i] q`, `q > 0`, `dA[i] > 0`, `i < 48`. -/
def planOKb : List (ℕ × ℕ × ℕ) → List ℕ → Bool
  | [], _ => true
  | s :: pl, D => (D.contains s.2.1 && dA.getD s.2.1 0 == dA.getD s.1 0 * s.2.2 && decide (0 < s.2.2) &&
      decide (0 < dA.getD s.1 0) && decide (s.1 < 48)) && planOKb pl (s.1 :: D)

/-- The indices done after the plan. -/
def planDone : List (ℕ × ℕ × ℕ) → List ℕ → List ℕ
  | [], D => D
  | s :: pl, D => planDone pl (s.1 :: D)

theorem planOK : planOKb plan [47] = true := by decide

theorem planDone_all : ∀ i < 48, i ∈ planDone plan [47] := by decide

/-- The invariant: 48 entries, and the done entries are the count arrays. -/
def Inv (X : ℕ) (D : List ℕ) (cs : Array (Array ℕ)) : Prop :=
  cs.size = 48 ∧ ∀ i ∈ D, cs.getD i #[] = cntArr X (dA.getD i 0)

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

theorem fold_inv (X : ℕ) : ∀ (pl : List (ℕ × ℕ × ℕ)) (D : List ℕ) (cs : Array (Array ℕ)),
    planOKb pl D = true → Inv X D cs → Inv X (planDone pl D) (pl.foldl cstep cs)
  | [], D, cs, _, hI => hI
  | (i, I, q) :: pl, D, cs, hok, hI => by
    simp only [planOKb, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨hID, hdq⟩, hq⟩, hdi⟩, hi⟩, hrest⟩ := hok
    rw [List.foldl_cons]
    apply fold_inv X pl (i :: D) _ hrest
    have hsz := hI.1
    refine ⟨by simp [cstep, hsz], ?_⟩
    intro j hj
    unfold cstep
    simp only
    rw [getD_setIfInBounds _ _ _ _ _ (by rw [hsz]; exact hi)]
    by_cases hji : j = i
    · rw [if_pos hji, hji, hI.2 I hID, hdq, red_cntArr X hdi hq]
    · rw [if_neg hji]
      exact hI.2 j ((List.mem_cons.mp hj).resolve_left hji)

theorem dA_47 : dA.getD 47 0 = 3960 := by decide

theorem cfam_spec (X : ℕ) {i : ℕ} (hi : i < 48) : (cfam (mrow X)).getD i #[] = cntArr X (dA.getD i 0) := by
  have h0 : Inv X [47] (cfam0 (mrow X)) := by
    refine ⟨by simp [cfam0], ?_⟩
    intro j hj
    rw [List.mem_singleton.mp hj, cfam0, getD_setIfInBounds _ _ _ _ _ (by simp), if_pos rfl, dA_47, cntArr_3960]
  exact (fold_inv X plan [47] _ planOK h0).2 i (planDone_all i hi)

theorem cfam_size (X : ℕ) : (cfam (mrow X)).size = 48 := by
  have h0 : Inv X [47] (cfam0 (mrow X)) := by
    refine ⟨by simp [cfam0], ?_⟩
    intro j hj
    rw [List.mem_singleton.mp hj, cfam0, getD_setIfInBounds _ _ _ _ _ (by simp), if_pos rfl, dA_47, cntArr_3960]
  exact (fold_inv X plan [47] _ planOK h0).1

/-! ## Squares and `Q` -/

theorem foldl_sq (L : List ℕ) : ∀ a, L.foldl (fun acc v => acc + v * v) a = a + ∑ i ∈ range L.length, L.getD i 0 ^ 2 := by
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    rw [List.foldl_cons, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem sqs_eq (A : Array ℕ) : sqs A = ∑ i ∈ range A.size, A.getD i 0 ^ 2 := by
  unfold sqs
  rw [← Array.foldl_toList, foldl_sq, zero_add, Array.length_toList]
  apply sum_congr rfl
  intro i hi
  rw [getD_eq_getElem' _ _ _ (mem_range.mp hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using mem_range.mp hi), Array.getElem_toList]

theorem sqs_cntArr (X g : ℕ) : sqs (cntArr X g) = S X g := by
  rw [sqs_eq, cntArr_size]
  unfold S
  apply sum_congr rfl
  intro a ha
  rw [cntArr_getD X g a (mem_range.mp ha)]

theorem foldl_range_add (f : ℕ → ℕ) : ∀ (n a : ℕ), (List.range n).foldl (fun acc i => acc + f i) a = a + ∑ i ∈ range n, f i
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_range_add f n a, List.foldl_cons, List.foldl_nil, sum_range_succ]
    ring

theorem qOf_cfam (X : ℕ) : qOf (cfam (mrow X)) = Qs X := by
  unfold qOf Qs
  rw [foldl_range_add, zero_add]
  apply sum_congr rfl
  intro i hi
  rw [cfam_spec X (mem_range.mp hi), sqs_cntArr]

theorem s_cfam (X : ℕ) : ((cfam (mrow X)).getD 0 #[]).getD 0 0 = cnt X 1 0 := by
  rw [cfam_spec X (by norm_num), show dA.getD 0 0 = 1 by decide, cntArr_getD X 1 0 Nat.one_pos]

theorem n36_cfam (X : ℕ) {j : ℕ} (hj : j < 36) : ((cfam (mrow X)).getD 18 #[]).getD j 0 = cnt X 36 j := by
  rw [cfam_spec X (by norm_num), show dA.getD 18 0 = 36 by decide, cntArr_getD X 36 j hj]

end Romanoff.E.S2
