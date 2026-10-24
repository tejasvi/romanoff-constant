import Romanoff.E.S2.Cross
import Romanoff.U3.Minorant

/-!
# U3e stage 2: the value of the accumulators

`V acc = Σ_J vt J acc[2J] acc[2J+1]` is linear: `addRow` adds `w · vt J s Q` (`J = jIdx s Q`), `lastStep` adds
`w · (mv X + Σ_{j ∈ o37} mv (X ∪ C_j))` with `mv X = vt J (|U|) (Q(U))` for the row of `X`, and `evalKey x` is the nested
option sum `T1 x` of these row values; `evalList` and `evalPar` give `Σ_{(x, c)} c · V (evalKey x)`.
-/

open Finset R45 R45.EV

namespace Romanoff.E.S2

theorem V_eq (acc : Array ℕ) : V acc = ∑ J ∈ range 64, vt J (acc.getD (2 * J) 0) (acc.getD (2 * J + 1) 0) := by
  unfold V; rw [range_map_sum]

theorem vt_add (J a q w s Q : ℕ) : vt J (a + w * s) (q + w * Q) = vt J a q + (w : ℚ) * vt J s Q := by
  unfold vt; push_cast; ring

theorem vt_zero (J : ℕ) : vt J 0 0 = 0 := by unfold vt; simp

theorem jIdx_le (s Q : ℕ) : jIdx s Q ≤ 63 := by
  unfold jIdx; split_ifs <;> omega

theorem jIdx_pos (s Q : ℕ) : 1 ≤ jIdx s Q := by
  unfold jIdx; split_ifs <;> omega

theorem addRow_size (acc : Array ℕ) (w s Q : ℕ) : (addRow acc w s Q).size = acc.size := by
  simp [addRow]

theorem V_addRow (acc : Array ℕ) (hacc : acc.size = 128) (w s Q : ℕ) :
    V (addRow acc w s Q) = V acc + (w : ℚ) * vt (jIdx s Q) s Q := by
  have hJ := jIdx_le s Q
  set J := jIdx s Q with hJdef
  have hm1 : (acc.modify (2 * J) (· + w * s)).size = 128 := by simp [hacc]
  have e1 : ∀ k, (addRow acc w s Q).getD k 0 =
      if k = 2 * J + 1 then (if k = 2 * J then acc.getD k 0 + w * s else acc.getD k 0) + w * Q
      else (if k = 2 * J then acc.getD k 0 + w * s else acc.getD k 0) := by
    intro k
    unfold addRow
    simp only
    rw [← hJdef, getD_modify _ _ _ _ (by rw [hm1]; omega), getD_modify _ _ _ _ (by rw [hacc]; omega)]
  rw [V_eq, V_eq]
  have h2 : ∀ J' ∈ range 64, vt J' ((addRow acc w s Q).getD (2 * J') 0) ((addRow acc w s Q).getD (2 * J' + 1) 0) =
      vt J' (acc.getD (2 * J') 0) (acc.getD (2 * J' + 1) 0) + if J' = J then (w : ℚ) * vt J s Q else 0 := by
    intro J' _
    rw [e1, e1]
    by_cases h : J' = J
    · rw [if_pos h, h]
      have n1 : ¬ (2 * J = 2 * J + 1) := by omega
      have n2 : ¬ (2 * J + 1 = 2 * J) := by omega
      simp only [n1, n2, if_true, if_false, eq_self_iff_true]
      rw [vt_add]
    · have n1 : ¬ (2 * J' = 2 * J + 1) := by omega
      have n2 : ¬ (2 * J' = 2 * J) := by omega
      have n3 : ¬ (2 * J' + 1 = 2 * J + 1) := by omega
      have n4 : ¬ (2 * J' + 1 = 2 * J) := by omega
      simp only [n1, n2, n3, n4, if_false, h, add_zero]
  rw [sum_congr rfl h2, sum_add_distrib, Finset.sum_ite_eq' (range 64) J, if_pos (mem_range.mpr (by omega))]

/-- A fold whose steps add `v b` to `V`. -/
theorem V_foldl {β : Type*} (F : Array ℕ → β → Array ℕ) (v : β → ℚ) :
    ∀ (L : List β), (∀ acc b, b ∈ L → acc.size = 128 → (F acc b).size = 128 ∧ V (F acc b) = V acc + v b) →
      ∀ acc, acc.size = 128 → (L.foldl F acc).size = 128 ∧ V (L.foldl F acc) = V acc + (L.map v).sum
  | [], _, acc, h => by simp [h]
  | b :: L, hF, acc, h => by
    obtain ⟨h1, h2⟩ := hF acc b (by simp) h
    obtain ⟨h3, h4⟩ := V_foldl F v L (fun acc' b' hb' => hF acc' b' (by simp [hb'])) _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]; ring

/-- The minorant of the row of `X` with its own Pintz index. -/
def mv (X : ℕ) : ℚ := vt (jIdx (cnt X 1 0) (Qs X)) (cnt X 1 0) (Qs X)

theorem o37_lt : ∀ j ∈ o37, j < 36 := by decide

theorem V_lastStep (X : ℕ) (acc : Array ℕ) (hacc : acc.size = 128) (w : ℕ) :
    (lastStep acc w (mrow X)).size = 128 ∧
      V (lastStep acc w (mrow X)) = V acc + (w : ℚ) * (mv X + (o37.map fun j => mv (X ||| cmask36 j)).sum) := by
  unfold lastStep
  simp only
  rw [s_cfam, qOf_cfam]
  have h0 : (addRow acc w (cnt X 1 0) (Qs X)).size = 128 := by rw [addRow_size, hacc]
  have hstep : ∀ acc' j, j ∈ o37 → acc'.size = 128 →
      (addRow acc' w (cnt X 1 0 - ((cfam (mrow X)).getD 18 #[]).getD j 0)
        (Qs X + (zOf (cfam (mrow X))).getD j 0 - 2 * (xOf (cfam (mrow X))).getD j 0)).size = 128 ∧
      V (addRow acc' w (cnt X 1 0 - ((cfam (mrow X)).getD 18 #[]).getD j 0)
        (Qs X + (zOf (cfam (mrow X))).getD j 0 - 2 * (xOf (cfam (mrow X))).getD j 0)) =
        V acc' + (w : ℚ) * mv (X ||| cmask36 j) := by
    intro acc' j hj hacc'
    have hj36 := o37_lt j hj
    have e1 : cnt X 1 0 - ((cfam (mrow X)).getD 18 #[]).getD j 0 = cnt (X ||| cmask36 j) 1 0 := by
      rw [n36_cfam X hj36]; have := cnt_or X (j := j); omega
    have e2 : Qs X + (zOf (cfam (mrow X))).getD j 0 - 2 * (xOf (cfam (mrow X))).getD j 0 = Qs (X ||| cmask36 j) := by
      have := Qs_or X hj36; omega
    rw [e1, e2]
    exact ⟨by rw [addRow_size, hacc'], V_addRow acc' hacc' w _ _⟩
  obtain ⟨h1, h2⟩ := V_foldl _ (fun j => (w : ℚ) * mv (X ||| cmask36 j)) o37 hstep _ h0
  refine ⟨h1, ?_⟩
  rw [h2, V_addRow acc hacc, List.sum_map_mul_left]
  unfold mv
  ring

/-! ## The options of the added primes -/

/-- The row values of the options of 37 after the prefix `X`. -/
def R4 (X : ℕ) : ℚ := mv X + (o37.map fun j => mv (X ||| cmask36 j)).sum

/-- The nested option sums of the row values (`23`, `73`, `19`, `41`). -/
def T4 (X : ℕ) : ℚ := ((optsP 3960 23).map fun mc => (mc.2 : ℚ) * R4 (X ||| mc.1)).sum
def T3 (X : ℕ) : ℚ := ((optsP 3960 73).map fun mc => (mc.2 : ℚ) * T4 (X ||| mc.1)).sum
def T2 (X : ℕ) : ℚ := ((optsP 3960 19).map fun mc => (mc.2 : ℚ) * T3 (X ||| mc.1)).sum
def T1 (X : ℕ) : ℚ := ((optsP 3960 41).map fun mc => (mc.2 : ℚ) * T2 (X ||| mc.1)).sum

/-- One level of the option folds: the options of `p` (rows `[e ∉ m]`, weights) after the prefix `X`. -/
theorem lvl_gen (p : ℕ) (Inner : ℕ → Array ℕ → Array ℕ → Array ℕ) (Tin : ℕ → ℚ)
    (hIn : ∀ X' W' acc, acc.size = 128 →
      (Inner W' (mrow X') acc).size = 128 ∧ V (Inner W' (mrow X') acc) = V acc + (W' : ℚ) * Tin X')
    (X W : ℕ) : ∀ acc, acc.size = 128 →
      ((optRows p).foldl (fun acc mw => Inner (W * mw.2) (zmul (mrow X) mw.1) acc) acc).size = 128 ∧
      V ((optRows p).foldl (fun acc mw => Inner (W * mw.2) (zmul (mrow X) mw.1) acc) acc) =
        V acc + (W : ℚ) * ((optsP 3960 p).map fun mc => (mc.2 : ℚ) * Tin (X ||| mc.1)).sum := by
  intro acc hacc
  unfold optRows
  rw [List.foldl_map]
  dsimp only
  obtain ⟨h1, h2⟩ := V_foldl (fun acc mc => Inner (W * mc.2) (zmul (mrow X) (mrow mc.1)) acc)
    (fun mc => ((W * mc.2 : ℕ) : ℚ) * Tin (X ||| mc.1)) (optsP 3960 p)
    (fun acc' mc _ hacc' => by rw [zmul_mrow]; exact hIn _ _ acc' hacc') acc hacc
  refine ⟨h1, ?_⟩
  rw [h2, ← List.sum_map_mul_left]
  apply congrArg (V acc + ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro mc _
  push_cast; ring

theorem lvl4 (X W : ℕ) : ∀ acc, acc.size = 128 →
    (o23.foldl (fun acc mw4 => lastStep acc (W * mw4.2) (zmul (mrow X) mw4.1)) acc).size = 128 ∧
    V (o23.foldl (fun acc mw4 => lastStep acc (W * mw4.2) (zmul (mrow X) mw4.1)) acc) = V acc + (W : ℚ) * T4 X := by
  intro acc hacc
  have h := lvl_gen 23 (fun W' r acc => lastStep acc W' r) R4 (fun X' W' acc hacc => V_lastStep X' acc hacc W') X W
    acc hacc
  unfold T4
  exact h

theorem lvl3 (X W : ℕ) : ∀ acc, acc.size = 128 →
    (o73.foldl (fun acc mw3 => o23.foldl (fun acc mw4 => lastStep acc (W * mw3.2 * mw4.2)
      (zmul (zmul (mrow X) mw3.1) mw4.1)) acc) acc).size = 128 ∧
    V (o73.foldl (fun acc mw3 => o23.foldl (fun acc mw4 => lastStep acc (W * mw3.2 * mw4.2)
      (zmul (zmul (mrow X) mw3.1) mw4.1)) acc) acc) = V acc + (W : ℚ) * T3 X := by
  intro acc hacc
  let Inner : ℕ → Array ℕ → Array ℕ → Array ℕ := fun W' r acc =>
    o23.foldl (fun acc mw4 => lastStep acc (W' * mw4.2) (zmul r mw4.1)) acc
  have hIn : ∀ X' W' acc, acc.size = 128 → (Inner W' (mrow X') acc).size = 128 ∧
      V (Inner W' (mrow X') acc) = V acc + (W' : ℚ) * T4 X' := fun X' W' acc hacc => lvl4 X' W' acc hacc
  have h := lvl_gen 73 Inner T4 hIn X W acc hacc
  unfold T3
  exact h

theorem lvl2 (X W : ℕ) : ∀ acc, acc.size = 128 →
    (o19.foldl (fun acc mw2 => o73.foldl (fun acc mw3 => o23.foldl (fun acc mw4 =>
      lastStep acc (W * mw2.2 * mw3.2 * mw4.2) (zmul (zmul (zmul (mrow X) mw2.1) mw3.1) mw4.1)) acc) acc) acc).size
      = 128 ∧
    V (o19.foldl (fun acc mw2 => o73.foldl (fun acc mw3 => o23.foldl (fun acc mw4 =>
      lastStep acc (W * mw2.2 * mw3.2 * mw4.2) (zmul (zmul (zmul (mrow X) mw2.1) mw3.1) mw4.1)) acc) acc) acc) =
      V acc + (W : ℚ) * T2 X := by
  intro acc hacc
  let Inner : ℕ → Array ℕ → Array ℕ → Array ℕ := fun W' r acc =>
    o73.foldl (fun acc mw3 => o23.foldl (fun acc mw4 => lastStep acc (W' * mw3.2 * mw4.2)
      (zmul (zmul r mw3.1) mw4.1)) acc) acc
  have hIn : ∀ X' W' acc, acc.size = 128 → (Inner W' (mrow X') acc).size = 128 ∧
      V (Inner W' (mrow X') acc) = V acc + (W' : ℚ) * T3 X' := fun X' W' acc hacc => lvl3 X' W' acc hacc
  have h := lvl_gen 19 Inner T3 hIn X W acc hacc
  unfold T2
  exact h

theorem z128_size : z128.size = 128 := by simp [z128]

theorem V_z128 : V z128 = 0 := by
  rw [V_eq]; apply sum_eq_zero; intro J _
  have : ∀ k, z128.getD k 0 = 0 := by
    intro k
    by_cases hk : k < 128
    · rw [getD_eq_getElem' _ _ _ (by simp [z128, hk])]; simp [z128]
    · rw [getD_eq_default' _ _ _ (by simp [z128]; omega)]
  rw [this, this, vt_zero]

theorem V_evalKey (x : ℕ) : (evalKey x).size = 128 ∧ V (evalKey x) = T1 x := by
  let Inner : ℕ → Array ℕ → Array ℕ → Array ℕ := fun W' r acc =>
    o19.foldl (fun acc mw2 => o73.foldl (fun acc mw3 => o23.foldl (fun acc mw4 =>
      lastStep acc (W' * mw2.2 * mw3.2 * mw4.2) (zmul (zmul (zmul r mw2.1) mw3.1) mw4.1)) acc) acc) acc
  have hIn : ∀ X' W' acc, acc.size = 128 → (Inner W' (mrow X') acc).size = 128 ∧
      V (Inner W' (mrow X') acc) = V acc + (W' : ℚ) * T2 X' := fun X' W' acc hacc => lvl2 X' W' acc hacc
  have h := lvl_gen 41 Inner T2 hIn x 1 z128 (by simp [z128])
  have hz : V z128 = 0 := by
    rw [V_eq]; apply sum_eq_zero; intro J _
    have : ∀ k, z128.getD k 0 = 0 := by
      intro k
      by_cases hk : k < 128
      · rw [getD_eq_getElem' _ _ _ (by simp [z128, hk])]; simp [z128]
      · rw [getD_eq_default' _ _ _ (by simp [z128]; omega)]
    rw [this, this, vt_zero]
  simp only [one_mul, Nat.cast_one, hz, zero_add] at h
  unfold evalKey T1
  exact h

end Romanoff.E.S2
