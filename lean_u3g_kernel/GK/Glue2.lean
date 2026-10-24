import GK.Glue

/-!
# k45g, glue part 2: the 21 rest rows written out, `VfA` as a list sum, and weighted sums of trees
-/

set_option maxRecDepth 100000

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

theorem o41r_length : o41r.length = 21 := by simp only [o41r, List.length_cons, List.length_nil]

attribute [local irreducible] R45.GK.o41r R45.GK.evalRestK R45.GK.evalKeyK R45.GK.restStep R45.GK.sigs R45.GK.pats

/-- `evalKeyK x` with its 21 rest-row trees written out. -/
theorem evalKeyK_eq21 (x : ℕ) : evalKeyK x = ((((((((((((((((((((((Acc.zero 6).plus (evalRestK x 0)).plus (evalRestK x 1)).plus (evalRestK x 2)).plus (evalRestK x 3)).plus (evalRestK x 4)).plus (evalRestK x 5)).plus (evalRestK x 6)).plus (evalRestK x 7)).plus (evalRestK x 8)).plus (evalRestK x 9)).plus (evalRestK x 10)).plus (evalRestK x 11)).plus (evalRestK x 12)).plus (evalRestK x 13)).plus (evalRestK x 14)).plus (evalRestK x 15)).plus (evalRestK x 16)).plus (evalRestK x 17)).plus (evalRestK x 18)).plus (evalRestK x 19)).plus (evalRestK x 20)) := by
  rw [evalKeyK_eq_sum, o41r_length]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wf_evalKeyK (x : ℕ) : Acc.WF 6 (evalKeyK x) :=
  (VfA_evalKeyK (vt := fun _ _ _ => 0) ⟨fun _ _ _ _ _ _ => by simp, fun _ => rfl⟩ x).1

/-- `VfA` as a list sum over the 64 slots (for kernel evaluation). -/
theorem VfA_list (vt : ℕ → ℕ → ℕ → ℚ) (t : Acc) :
    VfA vt t = ((List.range 64).map fun J => vt J (t.get 6 J).1 (t.get 6 J).2).sum := by
  unfold VfA; rw [sum_map_range]

/-- Weighted sums of well-formed trees. -/
def wsumAcc (L : List (Acc × ℕ)) : Acc := L.foldl (fun acc p => acc.plus (Acc.scale p.2 p.1)) (Acc.zero 6)

theorem VfA_wsum_aux {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) : ∀ (L : List (Acc × ℕ)) (acc : Acc), Acc.WF 6 acc →
    (∀ p ∈ L, Acc.WF 6 p.1) →
      Acc.WF 6 (L.foldl (fun acc p => acc.plus (Acc.scale p.2 p.1)) acc) ∧
      VfA vt (L.foldl (fun acc p => acc.plus (Acc.scale p.2 p.1)) acc) = VfA vt acc + (L.map fun p => (p.2 : ℚ) * VfA vt p.1).sum
  | [], acc, h, _ => by simp [h]
  | p :: L, acc, h, hL => by
    have hp := hL p (by simp)
    have h1 : Acc.WF 6 (acc.plus (Acc.scale p.2 p.1)) := Acc.wf_plus 6 _ _ h (Acc.wf_scale _ 6 _ hp)
    obtain ⟨h2, h3⟩ := VfA_wsum_aux hvt L _ h1 (fun q hq => hL q (by simp [hq]))
    refine ⟨h2, ?_⟩
    rw [List.foldl_cons, h3, VfA_plus hvt _ _ h (Acc.wf_scale _ 6 _ hp), VfA_scale hvt _ _ hp, List.map_cons, List.sum_cons]
    ring

theorem VfA_wsum {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (L : List (Acc × ℕ)) (hL : ∀ p ∈ L, Acc.WF 6 p.1) :
    VfA vt (wsumAcc L) = (L.map fun p => (p.2 : ℚ) * VfA vt p.1).sum := by
  have h := (VfA_wsum_aux hvt L (Acc.zero 6) (Acc.wf_zero 6) hL).2
  rw [VfA_zero hvt, zero_add] at h
  exact h

theorem wf_wsum (L : List (Acc × ℕ)) (hL : ∀ p ∈ L, Acc.WF 6 p.1) : Acc.WF 6 (wsumAcc L) :=
  (VfA_wsum_aux (vt := fun _ _ _ => 0) ⟨fun _ _ _ _ _ _ => by simp, fun _ => rfl⟩ L (Acc.zero 6) (Acc.wf_zero 6) hL).1

/-- A chunk of BASE keys (x, count) whose trees are known: its weighted value is the value of one tree. -/
theorem chunk_value {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (ch : List (ℕ × ℕ)) (L : List (Acc × ℕ))
    (hmap : ch.map (fun xc => (evalKeyK xc.1, xc.2)) = L) (T : Acc) (hT : wsumAcc L = T) :
    (ch.map fun xc => (xc.2 : ℚ) * VfA vt (evalKeyK xc.1)).sum = VfA vt T := by
  have hL : ∀ p ∈ L, Acc.WF 6 p.1 := by
    intro p hp
    rw [← hmap] at hp
    obtain ⟨xc, _, rfl⟩ := List.mem_map.mp hp
    exact wf_evalKeyK xc.1
  rw [← hT, VfA_wsum hvt L hL, ← hmap]
  simp only [List.map_map, Function.comp_def]

end R45.GK
