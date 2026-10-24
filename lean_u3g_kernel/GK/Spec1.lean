import GK.Ev
import Romanoff.G.S2.Value

/-!
# k45g, proofs part 1: the value of the fibered evaluator's accumulator

`VfA vt t = Σ_{J < 64} vt J (Σ w s)_J (Σ w Q)_J` for the tree accumulator, its linearity under `Acc.add`, and the value of
`restStep` and `evalKeyK` as weighted sums of the row values `vt (jIdx s Q) s Q` over (signature, pattern).
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

attribute [local irreducible] R45.GK.pats R45.GK.sigs R45.GK.zrRow R45.GK.nRg R45.GK.o41r

/-! ## Elementary sums -/

theorem sumN_eq (f : ℕ → ℕ) : ∀ n, sumN f n = ∑ i ∈ range n, f i
  | 0 => by simp [sumN]
  | n + 1 => by rw [sumN, sumN_eq f n, sum_range_succ]

theorem sumL_eq : ∀ L : List ℕ, sumL L = L.sum
  | [] => rfl
  | a :: L => by rw [sumL, sumL_eq L, List.sum_cons]

theorem dotL_nil_left (B : List ℕ) : dotL [] B = 0 := by cases B <;> rfl

theorem dotL_cons_cons (a b : ℕ) (A B : List ℕ) : dotL (a :: A) (b :: B) = a * b + dotL A B := rfl

/-- `dotL` as a sum of products over the zipped list. -/
theorem dotL_eq_sum_zip : ∀ (A B : List ℕ), dotL A B = ((A.zip B).map fun p => p.1 * p.2).sum
  | [], B => by rw [dotL_nil_left]; simp
  | a :: A, [] => by simp [dotL]
  | a :: A, b :: B => by rw [dotL_cons_cons, dotL_eq_sum_zip A B]; simp

/-! ## The tree accumulator -/

/-- The slot `J` of a tree of depth `d`. -/
def Acc.get : ℕ → Acc → ℕ → ℕ × ℕ
  | _, .leaf a q, _ => (a, q)
  | 0, .node _ _, _ => (0, 0)
  | d + 1, .node l r, J => if J < 2 ^ d then Acc.get d l J else Acc.get d r (J - 2 ^ d)

/-- A complete tree of depth `d`. -/
def Acc.WF : ℕ → Acc → Prop
  | 0, .leaf _ _ => True
  | 0, .node _ _ => False
  | _ + 1, .leaf _ _ => False
  | d + 1, .node l r => Acc.WF d l ∧ Acc.WF d r

theorem Acc.wf_zero : ∀ d, Acc.WF d (Acc.zero d)
  | 0 => trivial
  | d + 1 => ⟨Acc.wf_zero d, Acc.wf_zero d⟩

theorem Acc.get_zero : ∀ d J, (Acc.zero d).get d J = (0, 0)
  | 0, _ => rfl
  | d + 1, J => by
    simp only [Acc.zero, Acc.get]
    split_ifs <;> exact Acc.get_zero d _

theorem Acc.wf_add : ∀ (d J a q : ℕ) (t : Acc), Acc.WF d t → Acc.WF d (t.add d J a q)
  | 0, _, _, _, .leaf _ _, _ => trivial
  | 0, _, _, _, .node _ _, h => h.elim
  | _ + 1, _, _, _, .leaf _ _, h => h.elim
  | d + 1, J, a, q, .node l r, ⟨hl, hr⟩ => by
    simp only [Acc.add]
    split_ifs
    · exact ⟨Acc.wf_add d J a q l hl, hr⟩
    · exact ⟨hl, Acc.wf_add d (J - 2 ^ d) a q r hr⟩

theorem Acc.get_add : ∀ (d J a q : ℕ) (t : Acc), Acc.WF d t → J < 2 ^ d → ∀ K, K < 2 ^ d →
    (t.add d J a q).get d K = if K = J then ((t.get d K).1 + a, (t.get d K).2 + q) else t.get d K
  | 0, J, a, q, .leaf a' q', _, hJ, K, hK => by
    have hJ0 : J = 0 := by simpa using hJ
    have hK0 : K = 0 := by simpa using hK
    subst hJ0; subst hK0; simp [Acc.add, Acc.get]
  | 0, _, _, _, .node _ _, h, _, _, _ => h.elim
  | _ + 1, _, _, _, .leaf _ _, h, _, _, _ => h.elim
  | d + 1, J, a, q, .node l r, ⟨hl, hr⟩, hJ, K, hK => by
    have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
    simp only [Acc.add]
    by_cases hJd : J < 2 ^ d
    · rw [if_pos hJd]
      simp only [Acc.get]
      by_cases hKd : K < 2 ^ d
      · rw [if_pos hKd, if_pos hKd, Acc.get_add d J a q l hl hJd K hKd]
      · rw [if_neg hKd, if_neg hKd]
        have : K ≠ J := by omega
        rw [if_neg this]
    · rw [if_neg hJd]
      simp only [Acc.get]
      by_cases hKd : K < 2 ^ d
      · rw [if_pos hKd, if_pos hKd]
        have : K ≠ J := by omega
        rw [if_neg this]
      · rw [if_neg hKd, if_neg hKd, Acc.get_add d (J - 2 ^ d) a q r hr (by omega) (K - 2 ^ d) (by omega)]
        by_cases hKJ : K = J
        · subst hKJ; simp
        · have : K - 2 ^ d ≠ J - 2 ^ d := by omega
          rw [if_neg this, if_neg hKJ]

/-- The value of a tree of depth 6 for a slot function `vt`. -/
def VfA (vt : ℕ → ℕ → ℕ → ℚ) (t : Acc) : ℚ := ∑ J ∈ range 64, vt J (t.get 6 J).1 (t.get 6 J).2

theorem VfA_zero {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) : VfA vt (Acc.zero 6) = 0 := by
  unfold VfA
  apply sum_eq_zero
  intro J _
  rw [Acc.get_zero, hvt.2]

theorem VfA_add {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (t : Acc) (ht : Acc.WF 6 t) (J w s Q : ℕ) (hJ : J < 64) :
    VfA vt (t.add 6 J (w * s) (w * Q)) = VfA vt t + (w : ℚ) * vt J s Q := by
  unfold VfA
  have h : ∀ K ∈ range 64, vt K ((t.add 6 J (w * s) (w * Q)).get 6 K).1 ((t.add 6 J (w * s) (w * Q)).get 6 K).2 =
      vt K (t.get 6 K).1 (t.get 6 K).2 + if K = J then (w : ℚ) * vt J s Q else 0 := by
    intro K hK
    have hK' : K < 2 ^ 6 := by simpa using mem_range.mp hK
    rw [Acc.get_add 6 J _ _ t ht (by norm_num; exact hJ) K hK']
    by_cases hKJ : K = J
    · subst hKJ; simp only [if_true]; rw [hvt.1]
    · simp [hKJ]
  rw [sum_congr rfl h, sum_add_distrib, sum_ite_eq' (range 64) J, if_pos (mem_range.mpr hJ)]

/-! ## The value of `restStep` and `evalKeyK` -/

/-- The value of one (rest row, signature, pattern) row: `(s, Q)` and its weight `pw`. -/
def rowSQ (n12 : List (List ℕ)) (Z : List (List (List ℕ))) (σ : Sig) (P : Pat) : ℕ × ℕ :=
  (dotL P.pf (List.zipWith dotL σ.fwg n12), sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt)))

/-- The value added by the patterns of one signature (weight 1). -/
def sigVal (vt : ℕ → ℕ → ℕ → ℚ) (n12 : List (List ℕ)) (Z : List (List (List ℕ))) (σ : Sig) : ℚ :=
  (pats.map fun P => (P.pw : ℚ) * vt (jIdx (rowSQ n12 Z σ P).1 (rowSQ n12 Z σ P).2) (rowSQ n12 Z σ P).1
    (rowSQ n12 Z σ P).2).sum

/-- The value added by a rest row (weight 1): `Σ_σ wt_σ sigVal σ`. -/
def RK (vt : ℕ → ℕ → ℕ → ℚ) (R : ℕ) : ℚ := (sigs.map fun σ => (σ.wt : ℚ) * sigVal vt (nRg R) (zrRow R) σ).sum

theorem jIdx_lt64 (s Q : ℕ) : jIdx s Q < 64 := by have := jIdx_le s Q; omega

/-- A fold whose steps add `v b` to `VfA vt` and keep the tree well formed. -/
theorem VfA_foldl {β : Type*} (vt : ℕ → ℕ → ℕ → ℚ) (F : Acc → β → Acc) (v : β → ℚ) :
    ∀ (L : List β), (∀ acc b, b ∈ L → Acc.WF 6 acc → Acc.WF 6 (F acc b) ∧ VfA vt (F acc b) = VfA vt acc + v b) →
      ∀ acc, Acc.WF 6 acc → Acc.WF 6 (L.foldl F acc) ∧ VfA vt (L.foldl F acc) = VfA vt acc + (L.map v).sum
  | [], _, acc, h => by simp [h]
  | b :: L, hF, acc, h => by
    obtain ⟨h1, h2⟩ := hF acc b (by simp) h
    obtain ⟨h3, h4⟩ := VfA_foldl vt F v L (fun acc' b' hb' => hF acc' b' (by simp [hb'])) _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]; ring

/-- The fold over the patterns of one signature (any pattern list), with `sh = ŝ`, `Y = Y_σ` and weight `ws`. -/
theorem VfA_patFold {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (sh : List ℕ) (Y : List (List ℕ)) (ws : ℕ) :
    ∀ (Ps : List Pat) (acc : Acc), Acc.WF 6 acc →
      Acc.WF 6 (Ps.foldl (fun acc P => acc.add 6 (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)))
        (ws * P.pw * dotL P.pf sh) (ws * P.pw * sumL (List.zipWith dotL P.pq Y))) acc) ∧
      VfA vt (Ps.foldl (fun acc P => acc.add 6 (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)))
        (ws * P.pw * dotL P.pf sh) (ws * P.pw * sumL (List.zipWith dotL P.pq Y))) acc) =
        VfA vt acc + (ws : ℚ) * (Ps.map fun P => (P.pw : ℚ) * vt (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)))
          (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y))).sum
  | [], acc, h => by simp [h]
  | P :: Ps, acc, h => by
    have h1 := Acc.wf_add 6 (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y))) (ws * P.pw * dotL P.pf sh)
      (ws * P.pw * sumL (List.zipWith dotL P.pq Y)) acc h
    have h2 := VfA_add hvt acc h (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y))) (ws * P.pw) (dotL P.pf sh)
      (sumL (List.zipWith dotL P.pq Y)) (jIdx_lt64 _ _)
    obtain ⟨h3, h4⟩ := VfA_patFold hvt sh Y ws Ps _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]
    push_cast; ring

/-- The fold over the signatures (any signature list) for fixed `n12`, `Z` and weight `w`. -/
theorem VfA_sigFold {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (n12 : List (List ℕ)) (Z : List (List (List ℕ))) (w : ℕ) :
    ∀ (Ss : List Sig) (acc : Acc), Acc.WF 6 acc →
      Acc.WF 6 (Ss.foldl (fun acc σ => pats.foldl (fun acc P =>
        acc.add 6 (jIdx (dotL P.pf (List.zipWith dotL σ.fwg n12)) (sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt))))
          (w * σ.wt * P.pw * dotL P.pf (List.zipWith dotL σ.fwg n12))
          (w * σ.wt * P.pw * sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt)))) acc) acc) ∧
      VfA vt (Ss.foldl (fun acc σ => pats.foldl (fun acc P =>
        acc.add 6 (jIdx (dotL P.pf (List.zipWith dotL σ.fwg n12)) (sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt))))
          (w * σ.wt * P.pw * dotL P.pf (List.zipWith dotL σ.fwg n12))
          (w * σ.wt * P.pw * sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt)))) acc) acc) =
        VfA vt acc + (w : ℚ) * (Ss.map fun σ => (σ.wt : ℚ) * sigVal vt n12 Z σ).sum
  | [], acc, h => by simp [h]
  | σ :: Ss, acc, h => by
    obtain ⟨h1, h2⟩ := VfA_patFold hvt (List.zipWith dotL σ.fwg n12) (Z.map fun Zt => List.zipWith dotL σ.c Zt)
      (w * σ.wt) pats acc h
    obtain ⟨h3, h4⟩ := VfA_sigFold hvt n12 Z w Ss _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]
    unfold sigVal rowSQ
    push_cast; ring

theorem VfA_restStep {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (acc : Acc) (hacc : Acc.WF 6 acc) (w R : ℕ) :
    Acc.WF 6 (restStep acc w R) ∧ VfA vt (restStep acc w R) = VfA vt acc + (w : ℚ) * RK vt R :=
  VfA_sigFold hvt (nRg R) (zrRow R) w sigs acc hacc

theorem VfA_evalKeyK {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (x : ℕ) :
    Acc.WF 6 (evalKeyK x) ∧ VfA vt (evalKeyK x) = (o41r.map fun mc => (mc.2 : ℚ) * RK vt (x ||| mc.1)).sum := by
  unfold evalKeyK
  have h := VfA_foldl vt (fun acc mc => restStep acc mc.2 (x ||| mc.1)) (fun mc => (mc.2 : ℚ) * RK vt (x ||| mc.1)) o41r
    (fun acc mc _ hacc => VfA_restStep hvt acc hacc mc.2 (x ||| mc.1)) (Acc.zero 6) (Acc.wf_zero 6)
  rw [VfA_zero hvt, zero_add] at h
  exact h

end R45.GK
