import GK.Spec5

/-!
# k45g, glue part 1: trees as sums of rest rows, linearity of `VfA`, and the 128-slot array

- `evalKeyK x` is the sum of the 21 trees `evalRestK x j` (`evalKeyK_eq_sum`).
- `VfA` is additive and homogeneous on well-formed trees; `VfA vt t = Vf vt t.toArr` (`VfA_eq_Vf`).
- `Acc.beq t s = true ↔ t = s` (`Acc.beq_iff`).
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

attribute [local irreducible] R45.GK.pats R45.GK.sigs R45.GK.sigF R45.GK.o41r

/-! ## Equality of trees -/

theorem Acc.beq_iff : ∀ t s : Acc, Acc.beq t s = true ↔ t = s
  | .leaf a q, .leaf a' q' => by simp [Acc.beq]
  | .node l r, .node l' r' => by simp [Acc.beq, Acc.beq_iff l l', Acc.beq_iff r r']
  | .leaf _ _, .node _ _ => by simp [Acc.beq]
  | .node _ _, .leaf _ _ => by simp [Acc.beq]

/-! ## Sums and multiples of trees -/

/-- Slotwise sum of two trees of the same shape (the left shape wins elsewhere). -/
def Acc.plus : Acc → Acc → Acc
  | .leaf a q, .leaf a' q' => .leaf (a + a') (q + q')
  | .node l r, .node l' r' => .node (Acc.plus l l') (Acc.plus r r')
  | t, _ => t

/-- Slotwise multiple. -/
def Acc.scale (c : ℕ) : Acc → Acc
  | .leaf a q => .leaf (c * a) (c * q)
  | .node l r => .node (Acc.scale c l) (Acc.scale c r)

theorem Acc.wf_plus : ∀ (d : ℕ) (t s : Acc), Acc.WF d t → Acc.WF d s → Acc.WF d (Acc.plus t s)
  | 0, .leaf _ _, .leaf _ _, _, _ => trivial
  | 0, .node _ _, _, h, _ => h.elim
  | 0, .leaf _ _, .node _ _, _, h => h.elim
  | _ + 1, .leaf _ _, _, h, _ => h.elim
  | _ + 1, .node _ _, .leaf _ _, _, h => h.elim
  | d + 1, .node l r, .node l' r', ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨Acc.wf_plus d l l' h1 h3, Acc.wf_plus d r r' h2 h4⟩

theorem Acc.wf_scale (c : ℕ) : ∀ (d : ℕ) (t : Acc), Acc.WF d t → Acc.WF d (Acc.scale c t)
  | 0, .leaf _ _, _ => trivial
  | 0, .node _ _, h => h.elim
  | _ + 1, .leaf _ _, h => h.elim
  | d + 1, .node l r, ⟨h1, h2⟩ => ⟨Acc.wf_scale c d l h1, Acc.wf_scale c d r h2⟩

theorem Acc.get_plus : ∀ (d : ℕ) (t s : Acc), Acc.WF d t → Acc.WF d s → ∀ J,
    (Acc.plus t s).get d J = ((t.get d J).1 + (s.get d J).1, (t.get d J).2 + (s.get d J).2)
  | 0, .leaf _ _, .leaf _ _, _, _, _ => rfl
  | 0, .node _ _, _, h, _, _ => h.elim
  | 0, .leaf _ _, .node _ _, _, h, _ => h.elim
  | _ + 1, .leaf _ _, _, h, _, _ => h.elim
  | _ + 1, .node _ _, .leaf _ _, _, h, _ => h.elim
  | d + 1, .node l r, .node l' r', ⟨h1, h2⟩, ⟨h3, h4⟩, J => by
    simp only [Acc.plus, Acc.get]
    split_ifs
    · exact Acc.get_plus d l l' h1 h3 J
    · exact Acc.get_plus d r r' h2 h4 _

theorem Acc.get_scale (c : ℕ) : ∀ (d : ℕ) (t : Acc), Acc.WF d t → ∀ J,
    (Acc.scale c t).get d J = (c * (t.get d J).1, c * (t.get d J).2)
  | 0, .leaf _ _, _, _ => rfl
  | 0, .node _ _, h, _ => h.elim
  | _ + 1, .leaf _ _, h, _ => h.elim
  | d + 1, .node l r, ⟨h1, h2⟩, J => by
    simp only [Acc.scale, Acc.get]
    split_ifs
    · exact Acc.get_scale c d l h1 J
    · exact Acc.get_scale c d r h2 _

theorem Lin.add {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (J a q a' q' : ℕ) :
    vt J (a + a') (q + q') = vt J a q + vt J a' q' := by
  have := hvt.1 J a q 1 a' q'
  simpa using this

theorem Lin.smul {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (J c a q : ℕ) : vt J (c * a) (c * q) = (c : ℚ) * vt J a q := by
  have := hvt.1 J 0 0 c a q
  simpa [hvt.2] using this

theorem VfA_plus {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (t s : Acc) (ht : Acc.WF 6 t) (hs : Acc.WF 6 s) :
    VfA vt (Acc.plus t s) = VfA vt t + VfA vt s := by
  unfold VfA
  rw [← sum_add_distrib]
  refine sum_congr rfl fun J _ => ?_
  rw [Acc.get_plus 6 t s ht hs J, Lin.add hvt]

theorem VfA_scale {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (c : ℕ) (t : Acc) (ht : Acc.WF 6 t) :
    VfA vt (Acc.scale c t) = (c : ℚ) * VfA vt t := by
  unfold VfA
  rw [mul_sum]
  refine sum_congr rfl fun J _ => ?_
  rw [Acc.get_scale c 6 t ht J, Lin.smul hvt]

/-! ## `restStep` adds its rows to the accumulator -/

theorem Acc.add_plus : ∀ (d J a q : ℕ) (t s : Acc), Acc.WF d t → Acc.WF d s →
    (Acc.plus t s).add d J a q = Acc.plus t (s.add d J a q)
  | 0, _, _, _, .leaf _ _, .leaf _ _, _, _ => by simp [Acc.plus, Acc.add]; omega
  | 0, _, _, _, .node _ _, _, h, _ => h.elim
  | 0, _, _, _, .leaf _ _, .node _ _, _, h => h.elim
  | _ + 1, _, _, _, .leaf _ _, _, h, _ => h.elim
  | _ + 1, _, _, _, .node _ _, .leaf _ _, _, h => h.elim
  | d + 1, J, a, q, .node l r, .node l' r', ⟨h1, h2⟩, ⟨h3, h4⟩ => by
    simp only [Acc.plus, Acc.add]
    split_ifs
    · rw [Acc.add_plus d J a q l l' h1 h3]; simp only [Acc.plus]
    · rw [Acc.add_plus d (J - 2 ^ d) a q r r' h2 h4]; simp only [Acc.plus]

theorem Acc.plus_zero : ∀ (d : ℕ) (t : Acc), Acc.WF d t → Acc.plus t (Acc.zero d) = t
  | 0, .leaf a q, _ => by simp [Acc.plus, Acc.zero]
  | 0, .node _ _, h => h.elim
  | _ + 1, .leaf _ _, h => h.elim
  | d + 1, .node l r, ⟨h1, h2⟩ => by simp [Acc.plus, Acc.zero, Acc.plus_zero d l h1, Acc.plus_zero d r h2]

/-- A fold of `Acc.add` steps (any step list) commutes with `plus` on the left. -/
theorem foldl_add_plus {β : Type*} (F : β → ℕ × ℕ × ℕ) :
    ∀ (L : List β) (t s : Acc), Acc.WF 6 t → Acc.WF 6 s →
      L.foldl (fun acc b => acc.add 6 (F b).1 (F b).2.1 (F b).2.2) (Acc.plus t s) =
        Acc.plus t (L.foldl (fun acc b => acc.add 6 (F b).1 (F b).2.1 (F b).2.2) s)
  | [], _, _, _, _ => rfl
  | b :: L, t, s, ht, hs => by
    rw [List.foldl_cons, List.foldl_cons, Acc.add_plus 6 _ _ _ t s ht hs]
    exact foldl_add_plus F L t _ ht (Acc.wf_add _ _ _ _ _ hs)

theorem patFold_plus (sh : List ℕ) (Y : List (List ℕ)) (ws : ℕ) (Ps : List Pat) (t s : Acc) (ht : Acc.WF 6 t)
    (hs : Acc.WF 6 s) :
    Ps.foldl (fun acc P => acc.add 6 (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)))
      (ws * P.pw * dotL P.pf sh) (ws * P.pw * sumL (List.zipWith dotL P.pq Y))) (Acc.plus t s) =
    Acc.plus t (Ps.foldl (fun acc P => acc.add 6 (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)))
      (ws * P.pw * dotL P.pf sh) (ws * P.pw * sumL (List.zipWith dotL P.pq Y))) s) :=
  foldl_add_plus (fun P => (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)),
    ws * P.pw * dotL P.pf sh, ws * P.pw * sumL (List.zipWith dotL P.pq Y))) Ps t s ht hs

theorem wf_patFold (sh : List ℕ) (Y : List (List ℕ)) (ws : ℕ) : ∀ (Ps : List Pat) (s : Acc), Acc.WF 6 s →
    Acc.WF 6 (Ps.foldl (fun acc P => acc.add 6 (jIdx (dotL P.pf sh) (sumL (List.zipWith dotL P.pq Y)))
      (ws * P.pw * dotL P.pf sh) (ws * P.pw * sumL (List.zipWith dotL P.pq Y))) s)
  | [], _, h => h
  | _ :: Ps, s, h => wf_patFold sh Y ws Ps _ (Acc.wf_add _ _ _ _ _ h)

theorem sigFold_plus (n12 : List (List ℕ)) (Z : List (List (List ℕ))) (w : ℕ) :
    ∀ (Ss : List Sig) (t s : Acc), Acc.WF 6 t → Acc.WF 6 s →
      Ss.foldl (fun acc σ => pats.foldl (fun acc P =>
        acc.add 6 (jIdx (dotL P.pf (List.zipWith dotL σ.fwg n12)) (sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt))))
          (w * σ.wt * P.pw * dotL P.pf (List.zipWith dotL σ.fwg n12))
          (w * σ.wt * P.pw * sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt)))) acc) (Acc.plus t s) =
      Acc.plus t (Ss.foldl (fun acc σ => pats.foldl (fun acc P =>
        acc.add 6 (jIdx (dotL P.pf (List.zipWith dotL σ.fwg n12)) (sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt))))
          (w * σ.wt * P.pw * dotL P.pf (List.zipWith dotL σ.fwg n12))
          (w * σ.wt * P.pw * sumL (List.zipWith dotL P.pq (Z.map fun Zt => List.zipWith dotL σ.c Zt)))) acc) s)
  | [], _, _, _, _ => rfl
  | σ :: Ss, t, s, ht, hs => by
    rw [List.foldl_cons, List.foldl_cons]
    rw [patFold_plus (List.zipWith dotL σ.fwg n12) (Z.map fun Zt => List.zipWith dotL σ.c Zt) (w * σ.wt) pats t s ht hs]
    exact sigFold_plus n12 Z w Ss t _ ht
      (wf_patFold (List.zipWith dotL σ.fwg n12) (Z.map fun Zt => List.zipWith dotL σ.c Zt) (w * σ.wt) pats s hs)

theorem restStep_plus (acc : Acc) (hacc : Acc.WF 6 acc) (w R : ℕ) :
    restStep acc w R = Acc.plus acc (restStep (Acc.zero 6) w R) := by
  have h := sigFold_plus (nRg R) (zrRow R) w sigs acc (Acc.zero 6) hacc (Acc.wf_zero 6)
  rw [Acc.plus_zero 6 acc hacc] at h
  exact h

/-- `evalKeyK x` as the left-nested sum of its rest-row trees. -/
theorem evalKeyK_eq_sum (x : ℕ) :
    evalKeyK x = (List.range o41r.length).foldl (fun acc j => Acc.plus acc (evalRestK x j)) (Acc.zero 6) := by
  have key : ∀ (L : List (ℕ × ℕ)) (pre : List (ℕ × ℕ)) (acc : Acc), Acc.WF 6 acc → pre ++ L = o41r →
      L.foldl (fun acc mc => restStep acc mc.2 (x ||| mc.1)) acc =
        (List.range' pre.length L.length).foldl (fun acc j => Acc.plus acc (evalRestK x j)) acc := by
    intro L
    induction L with
    | nil => intro pre acc _ _; simp
    | cons mc L ih =>
      intro pre acc hacc hsplit
      rw [List.foldl_cons, List.length_cons, List.range'_succ, List.foldl_cons]
      have hj : evalRestK x pre.length = restStep (Acc.zero 6) mc.2 (x ||| mc.1) := by
        unfold evalRestK
        rw [show o41r[pre.length]? = some mc by rw [← hsplit, List.getElem?_append_right (le_refl _)]; simp]
      rw [hj, ← restStep_plus acc hacc mc.2 (x ||| mc.1)]
      have hwf : Acc.WF 6 (restStep acc mc.2 (x ||| mc.1)) :=
        (VfA_restStep (vt := fun _ _ _ => 0) ⟨fun _ _ _ _ _ _ => by simp, fun _ => rfl⟩ acc hacc mc.2 (x ||| mc.1)).1
      have e := ih (pre ++ [mc]) _ hwf (by rw [List.append_assoc]; exact hsplit)
      rw [e, List.length_append, List.length_singleton]
  have h := key o41r [] (Acc.zero 6) (Acc.wf_zero 6) rfl
  unfold evalKeyK
  rw [h, List.length_nil, List.range_eq_range']

end R45.GK
