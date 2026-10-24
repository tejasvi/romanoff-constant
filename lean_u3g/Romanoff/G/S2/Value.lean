import Romanoff.G.S2.Mino

/-!
# U3g/V4g stage 2: the value of the accumulators

For a slot function `vt` that is linear in the slot sums (`Lin vt`; both `vtM` instances are), `Vf vt acc =
Σ_J vt J acc[2J] acc[2J+1]` is linear: `addRow` adds `w · vt J s Q` (`J = jIdx s Q`), `rowStep` adds `w · Rrow vt Y` (the
weighted sum over the patterns of the core row of `Y`), `evalKey x` is the nested option sum `T1 vt (repB 120 360 x)`, and
`evalList`, `evalPar` give `Σ_{(x, c)} c · Vf vt (evalKey x)`.
-/

open Finset R45 R45.EVG

namespace Romanoff.G.S2

/-- `Σ_{J < 64} vt J acc[2J] acc[2J+1]`. -/
def Vf (vt : ℕ → ℕ → ℕ → ℚ) (acc : Array ℕ) : ℚ := ∑ J ∈ range 64, vt J (acc.getD (2 * J) 0) (acc.getD (2 * J + 1) 0)

/-- Linearity in the slot sums. -/
def Lin (vt : ℕ → ℕ → ℕ → ℚ) : Prop :=
  (∀ J a q w s Q, vt J (a + w * s) (q + w * Q) = vt J a q + (w : ℚ) * vt J s Q) ∧ ∀ J, vt J 0 0 = 0

theorem vtM_lin (mu c1 : ℚ) (istar : ℕ → ℕ) : Lin (fun J a q => vtM mu c1 (istar J) J a q) := by
  refine ⟨fun J a q w s Q => ?_, fun J => ?_⟩
  · unfold vtM; push_cast; ring
  · unfold vtM; simp

theorem VU_eq (acc : Array ℕ) : VU acc = Vf (fun J a q => vtM 0 0 J J a q) acc := by
  unfold VU Vf; rw [range_map_sum]

theorem VV_eq (acc : Array ℕ) : VV acc = Vf (fun J a q => vtM muV c1V (istarV.getD J 1) J a q) acc := by
  unfold VV Vf; rw [range_map_sum]

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

theorem jIdx_le (s Q : ℕ) : jIdx s Q ≤ 63 := by
  unfold jIdx; split_ifs <;> omega

theorem jIdx_pos (s Q : ℕ) : 1 ≤ jIdx s Q := by
  unfold jIdx; split_ifs <;> omega

theorem addRow_size (acc : Array ℕ) (w s Q : ℕ) : (addRow acc w s Q).size = acc.size := by
  simp [addRow]

theorem Vf_addRow {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (acc : Array ℕ) (hacc : acc.size = 128) (w s Q : ℕ) :
    Vf vt (addRow acc w s Q) = Vf vt acc + (w : ℚ) * vt (jIdx s Q) s Q := by
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
  unfold Vf
  have h2 : ∀ J' ∈ range 64, vt J' ((addRow acc w s Q).getD (2 * J') 0) ((addRow acc w s Q).getD (2 * J' + 1) 0) =
      vt J' (acc.getD (2 * J') 0) (acc.getD (2 * J' + 1) 0) + if J' = J then (w : ℚ) * vt J s Q else 0 := by
    intro J' _
    rw [e1, e1]
    by_cases h : J' = J
    · rw [if_pos h, h]
      have n1 : ¬ (2 * J = 2 * J + 1) := by omega
      have n2 : ¬ (2 * J + 1 = 2 * J) := by omega
      simp only [n1, n2, if_true, if_false, eq_self_iff_true]
      rw [hvt.1]
    · have n1 : ¬ (2 * J' = 2 * J + 1) := by omega
      have n2 : ¬ (2 * J' = 2 * J) := by omega
      have n3 : ¬ (2 * J' + 1 = 2 * J + 1) := by omega
      have n4 : ¬ (2 * J' + 1 = 2 * J) := by omega
      simp only [n1, n2, n3, n4, if_false, h, add_zero]
  rw [sum_congr rfl h2, sum_add_distrib, Finset.sum_ite_eq' (range 64) J, if_pos (mem_range.mpr (by omega))]

/-- A fold whose steps add `v b` to `Vf vt`. -/
theorem Vf_foldl {β : Type*} (vt : ℕ → ℕ → ℕ → ℚ) (F : Array ℕ → β → Array ℕ) (v : β → ℚ) :
    ∀ (L : List β), (∀ acc b, b ∈ L → acc.size = 128 → (F acc b).size = 128 ∧ Vf vt (F acc b) = Vf vt acc + v b) →
      ∀ acc, acc.size = 128 → (L.foldl F acc).size = 128 ∧ Vf vt (L.foldl F acc) = Vf vt acc + (L.map v).sum
  | [], _, acc, h => by simp [h]
  | b :: L, hF, acc, h => by
    obtain ⟨h1, h2⟩ := hF acc b (by simp) h
    obtain ⟨h3, h4⟩ := Vf_foldl vt F v L (fun acc' b' hb' => hF acc' b' (by simp [hb'])) _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]; ring

/-! ## One core row -/

/-- The value added by the core row of `Y` (weight 1): `Σ_P pw_P vt(J_P, s_P, Q_P)`. -/
def Rrow (vt : ℕ → ℕ → ℕ → ℚ) (Y : ℕ) : ℚ :=
  ((List.range npC).map fun P =>
    (pwA.getD P 0 : ℚ) * vt (jIdx (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P) (qOf (zOf (tOf (csOf Y))) P))
      (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P) (qOf (zOf (tOf (csOf Y))) P)).sum

theorem Vf_rowStep {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (Y : ℕ) (acc : Array ℕ) (hacc : acc.size = 128) (w : ℕ) :
    (rowStep acc w (mrow Y)).size = 128 ∧ Vf vt (rowStep acc w (mrow Y)) = Vf vt acc + (w : ℚ) * Rrow vt Y := by
  unfold rowStep
  simp only
  have h := Vf_foldl vt (fun acc P => addRow acc (w * pwA.getD P 0)
      (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P) (qOf (zOf (tOf (csOf Y))) P))
    (fun P => ((w * pwA.getD P 0 : ℕ) : ℚ) * vt (jIdx (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P)
      (qOf (zOf (tOf (csOf Y))) P)) (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P) (qOf (zOf (tOf (csOf Y))) P))
    (List.range npC) (fun acc' P _ hacc' => ⟨by rw [addRow_size, hacc'], Vf_addRow hvt acc' hacc' _ _ _⟩) acc hacc
  refine ⟨h.1, ?_⟩
  have e : csOf Y = c4.map fun m => cfam (zmul (mrow Y) m) := rfl
  rw [← e, h.2]
  unfold Rrow
  rw [← List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro P _
  push_cast; ring

/-! ## The options of the core primes -/

/-- The nested option sums of the core rows (`37`, `73`, `19`, `41`). -/
def T4 (vt : ℕ → ℕ → ℕ → ℚ) (X : ℕ) : ℚ := ((optsP 360 37).map fun mc => (mc.2 : ℚ) * Rrow vt (X ||| mc.1)).sum
def T3 (vt : ℕ → ℕ → ℕ → ℚ) (X : ℕ) : ℚ := ((optsP 360 73).map fun mc => (mc.2 : ℚ) * T4 vt (X ||| mc.1)).sum
def T2 (vt : ℕ → ℕ → ℕ → ℚ) (X : ℕ) : ℚ := ((optsP 360 19).map fun mc => (mc.2 : ℚ) * T3 vt (X ||| mc.1)).sum
def T1 (vt : ℕ → ℕ → ℕ → ℚ) (X : ℕ) : ℚ := ((optsP 360 41).map fun mc => (mc.2 : ℚ) * T2 vt (X ||| mc.1)).sum

/-- One level of the option folds: the options of `p` (rows `[x ∉ m]`, weights) after the prefix `X`. -/
theorem lvl_gen (vt : ℕ → ℕ → ℕ → ℚ) (p : ℕ) (Inner : ℕ → Array ℕ → Array ℕ → Array ℕ) (Tin : ℕ → ℚ)
    (hIn : ∀ X' W' acc, acc.size = 128 →
      (Inner W' (mrow X') acc).size = 128 ∧ Vf vt (Inner W' (mrow X') acc) = Vf vt acc + (W' : ℚ) * Tin X')
    (X W : ℕ) : ∀ acc, acc.size = 128 →
      ((optRows p).foldl (fun acc mw => Inner (W * mw.2) (zmul (mrow X) mw.1) acc) acc).size = 128 ∧
      Vf vt ((optRows p).foldl (fun acc mw => Inner (W * mw.2) (zmul (mrow X) mw.1) acc) acc) =
        Vf vt acc + (W : ℚ) * ((optsP 360 p).map fun mc => (mc.2 : ℚ) * Tin (X ||| mc.1)).sum := by
  intro acc hacc
  unfold optRows
  rw [List.foldl_map]
  dsimp only
  obtain ⟨h1, h2⟩ := Vf_foldl vt (fun acc mc => Inner (W * mc.2) (zmul (mrow X) (mrow mc.1)) acc)
    (fun mc => ((W * mc.2 : ℕ) : ℚ) * Tin (X ||| mc.1)) (optsP 360 p)
    (fun acc' mc _ hacc' => by rw [zmul_mrow]; exact hIn _ _ acc' hacc') acc hacc
  refine ⟨h1, ?_⟩
  rw [h2, ← List.sum_map_mul_left]
  apply congrArg (Vf vt acc + ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro mc _
  push_cast; ring

theorem lvl4 {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (X W : ℕ) : ∀ acc, acc.size = 128 →
    (o37.foldl (fun acc mw4 => rowStep acc (W * mw4.2) (zmul (mrow X) mw4.1)) acc).size = 128 ∧
    Vf vt (o37.foldl (fun acc mw4 => rowStep acc (W * mw4.2) (zmul (mrow X) mw4.1)) acc) =
      Vf vt acc + (W : ℚ) * T4 vt X := by
  intro acc hacc
  have h := lvl_gen vt 37 (fun W' r acc => rowStep acc W' r) (Rrow vt)
    (fun X' W' acc hacc => Vf_rowStep hvt X' acc hacc W') X W acc hacc
  unfold T4
  exact h

theorem lvl3 {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (X W : ℕ) : ∀ acc, acc.size = 128 →
    (o73.foldl (fun acc mw3 => o37.foldl (fun acc mw4 => rowStep acc (W * mw3.2 * mw4.2)
      (zmul (zmul (mrow X) mw3.1) mw4.1)) acc) acc).size = 128 ∧
    Vf vt (o73.foldl (fun acc mw3 => o37.foldl (fun acc mw4 => rowStep acc (W * mw3.2 * mw4.2)
      (zmul (zmul (mrow X) mw3.1) mw4.1)) acc) acc) = Vf vt acc + (W : ℚ) * T3 vt X := by
  intro acc hacc
  let Inner : ℕ → Array ℕ → Array ℕ → Array ℕ := fun W' r acc =>
    o37.foldl (fun acc mw4 => rowStep acc (W' * mw4.2) (zmul r mw4.1)) acc
  have hIn : ∀ X' W' acc, acc.size = 128 → (Inner W' (mrow X') acc).size = 128 ∧
      Vf vt (Inner W' (mrow X') acc) = Vf vt acc + (W' : ℚ) * T4 vt X' := fun X' W' acc hacc => lvl4 hvt X' W' acc hacc
  have h := lvl_gen vt 73 Inner (T4 vt) hIn X W acc hacc
  unfold T3
  exact h

theorem lvl2 {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (X W : ℕ) : ∀ acc, acc.size = 128 →
    (o19.foldl (fun acc mw2 => o73.foldl (fun acc mw3 => o37.foldl (fun acc mw4 =>
      rowStep acc (W * mw2.2 * mw3.2 * mw4.2) (zmul (zmul (zmul (mrow X) mw2.1) mw3.1) mw4.1)) acc) acc) acc).size
      = 128 ∧
    Vf vt (o19.foldl (fun acc mw2 => o73.foldl (fun acc mw3 => o37.foldl (fun acc mw4 =>
      rowStep acc (W * mw2.2 * mw3.2 * mw4.2) (zmul (zmul (zmul (mrow X) mw2.1) mw3.1) mw4.1)) acc) acc) acc) =
      Vf vt acc + (W : ℚ) * T2 vt X := by
  intro acc hacc
  let Inner : ℕ → Array ℕ → Array ℕ → Array ℕ := fun W' r acc =>
    o73.foldl (fun acc mw3 => o37.foldl (fun acc mw4 => rowStep acc (W' * mw3.2 * mw4.2)
      (zmul (zmul r mw3.1) mw4.1)) acc) acc
  have hIn : ∀ X' W' acc, acc.size = 128 → (Inner W' (mrow X') acc).size = 128 ∧
      Vf vt (Inner W' (mrow X') acc) = Vf vt acc + (W' : ℚ) * T3 vt X' := fun X' W' acc hacc => lvl3 hvt X' W' acc hacc
  have h := lvl_gen vt 19 Inner (T3 vt) hIn X W acc hacc
  unfold T2
  exact h

theorem z128_size : z128.size = 128 := by simp [z128]

theorem Vf_z128 {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) : Vf vt z128 = 0 := by
  unfold Vf; apply sum_eq_zero; intro J _
  have : ∀ k, z128.getD k 0 = 0 := by
    intro k
    by_cases hk : k < 128
    · rw [getD_eq_getElem' _ _ _ (by simp [z128, hk])]; simp [z128]
    · rw [getD_eq_default' _ _ _ (by simp [z128]; omega)]
  rw [this, this, hvt.2]

theorem Vf_evalKey {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (x : ℕ) :
    (evalKey x).size = 128 ∧ Vf vt (evalKey x) = T1 vt (repB 120 360 x) := by
  let Inner : ℕ → Array ℕ → Array ℕ → Array ℕ := fun W' r acc =>
    o19.foldl (fun acc mw2 => o73.foldl (fun acc mw3 => o37.foldl (fun acc mw4 =>
      rowStep acc (W' * mw2.2 * mw3.2 * mw4.2) (zmul (zmul (zmul r mw2.1) mw3.1) mw4.1)) acc) acc) acc
  have hIn : ∀ X' W' acc, acc.size = 128 → (Inner W' (mrow X') acc).size = 128 ∧
      Vf vt (Inner W' (mrow X') acc) = Vf vt acc + (W' : ℚ) * T2 vt X' := fun X' W' acc hacc => lvl2 hvt X' W' acc hacc
  have h := lvl_gen vt 41 Inner (T2 vt) hIn (repB 120 360 x) 1 z128 z128_size
  simp only [one_mul, Nat.cast_one, Vf_z128 hvt, zero_add] at h
  unfold evalKey T1
  exact h

/-! ## The parallel evaluation -/

theorem axpy_getD (c : ℕ) (v acc : Array ℕ) (hv : v.size = acc.size) (j : ℕ) (hj : j < acc.size) :
    (axpy c v acc).getD j 0 = acc.getD j 0 + c * v.getD j 0 := by
  have hs : (axpy c v acc).size = acc.size := by simp [axpy, hv]
  rw [getD_eq_getElem' _ _ _ (by rw [hs]; exact hj), getD_eq_getElem' _ _ _ hj, getD_eq_getElem' _ _ _ (by rw [hv]; exact hj)]
  simp [axpy]

theorem Vf_axpy {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (c : ℕ) (v acc : Array ℕ) (hv : v.size = 128)
    (ha : acc.size = 128) : (axpy c v acc).size = 128 ∧ Vf vt (axpy c v acc) = Vf vt acc + (c : ℚ) * Vf vt v := by
  have hs : (axpy c v acc).size = 128 := by simp [axpy, hv, ha]
  refine ⟨hs, ?_⟩
  unfold Vf
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro J hJ
  have hJ' := mem_range.mp hJ
  rw [axpy_getD c v acc (by rw [hv, ha]) _ (by rw [ha]; omega),
    axpy_getD c v acc (by rw [hv, ha]) _ (by rw [ha]; omega), hvt.1]

theorem Vf_evalList {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (L : List (ℕ × ℕ)) :
    (evalList L).size = 128 ∧ Vf vt (evalList L) = (L.map fun xc => (xc.2 : ℚ) * Vf vt (evalKey xc.1)).sum := by
  let F : Array ℕ → ℕ × ℕ → Array ℕ := fun acc xc => axpy xc.2 (evalKey xc.1) acc
  let v : ℕ × ℕ → ℚ := fun xc => (xc.2 : ℚ) * Vf vt (evalKey xc.1)
  have hF : ∀ (acc : Array ℕ) (xc : ℕ × ℕ), xc ∈ L → acc.size = 128 →
      (F acc xc).size = 128 ∧ Vf vt (F acc xc) = Vf vt acc + v xc :=
    fun acc xc _ hacc => Vf_axpy hvt xc.2 (evalKey xc.1) acc (Vf_evalKey hvt xc.1).1 hacc
  have h := Vf_foldl vt F v L hF z128 z128_size
  rw [Vf_z128 hvt, zero_add] at h
  exact h

theorem chunks_flatten {β : Type} (k : ℕ) (L : List β) : (chunks k L).flatten = L := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    rw [chunks]
    split_ifs with hc
    · simp
    · simp only [not_or] at hc
      rw [List.flatten_cons, ih (L.drop k).length (by
        have : L.length ≠ 0 := fun h0 => hc.2 (List.eq_nil_of_length_eq_zero h0)
        simp only [List.length_drop]; omega) _ rfl, List.take_append_drop]

theorem sum_flatten_map {β : Type} (f : β → ℚ) : ∀ (LL : List (List β)),
    (LL.map fun l => (l.map f).sum).sum = (LL.flatten.map f).sum
  | [] => by simp
  | l :: LL => by rw [List.map_cons, List.sum_cons, sum_flatten_map f LL, List.flatten_cons, List.map_append,
      List.sum_append]

theorem Vf_evalPar {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (k : ℕ) (L : List (ℕ × ℕ)) :
    Vf vt (evalPar k L) = (L.map fun xc => (xc.2 : ℚ) * Vf vt (evalKey xc.1)).sum := by
  let F : Array ℕ → List (ℕ × ℕ) → Array ℕ := fun acc ch => axpy 1 (evalList ch) acc
  let v : List (ℕ × ℕ) → ℚ := fun ch => (1 : ℚ) * Vf vt (evalList ch)
  have hF : ∀ (acc : Array ℕ) (ch : List (ℕ × ℕ)), ch ∈ chunks k L → acc.size = 128 →
      (F acc ch).size = 128 ∧ Vf vt (F acc ch) = Vf vt acc + v ch := by
    intro acc ch _ hacc
    have := Vf_axpy hvt 1 (evalList ch) acc (Vf_evalList hvt ch).1 hacc
    exact ⟨this.1, by rw [this.2]; simp [v]⟩
  have h := Vf_foldl vt F v (chunks k L) hF z128 z128_size
  have e : evalPar k L = List.foldl F z128 (chunks k L) := by
    unfold evalPar
    rw [List.foldl_map]
    rfl
  rw [e, h.2, Vf_z128 hvt, zero_add]
  simp only [v, one_mul]
  have e2 : ∀ ch ∈ chunks k L, Vf vt (evalList ch) = (ch.map fun xc => (xc.2 : ℚ) * Vf vt (evalKey xc.1)).sum :=
    fun ch _ => (Vf_evalList hvt ch).2
  rw [List.map_congr_left e2, sum_flatten_map, chunks_flatten]

end Romanoff.G.S2
