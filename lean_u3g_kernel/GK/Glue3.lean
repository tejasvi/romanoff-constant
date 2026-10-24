import GK.Glue2

/-!
# k45g, glue part 3: a Boolean check of well-formedness, and sums of tree values
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

/-- Boolean well-formedness (complete tree of depth `d`). -/
def Acc.wfb : ℕ → Acc → Bool
  | 0, .leaf _ _ => true
  | 0, .node _ _ => false
  | _ + 1, .leaf _ _ => false
  | d + 1, .node l r => Acc.wfb d l && Acc.wfb d r

theorem Acc.wf_of_wfb : ∀ (d : ℕ) (t : Acc), Acc.wfb d t = true → Acc.WF d t
  | 0, .leaf _ _, _ => trivial
  | 0, .node _ _, h => by simp [Acc.wfb] at h
  | _ + 1, .leaf _ _, h => by simp [Acc.wfb] at h
  | d + 1, .node l r, h => by
    simp only [Acc.wfb, Bool.and_eq_true] at h
    exact ⟨Acc.wf_of_wfb d l h.1, Acc.wf_of_wfb d r h.2⟩

/-- The value of a left fold of `plus` over well-formed trees. -/
theorem VfA_foldl_plus {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) : ∀ (Ts : List Acc) (acc : Acc), Acc.WF 6 acc →
    (∀ t ∈ Ts, Acc.WF 6 t) → Acc.WF 6 (Ts.foldl Acc.plus acc) ∧
      VfA vt (Ts.foldl Acc.plus acc) = VfA vt acc + (Ts.map (VfA vt)).sum
  | [], acc, h, _ => by simp [h]
  | t :: Ts, acc, h, hT => by
    have ht := hT t (by simp)
    obtain ⟨h1, h2⟩ := VfA_foldl_plus hvt Ts (acc.plus t) (Acc.wf_plus 6 _ _ h ht) (fun s hs => hT s (by simp [hs]))
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, VfA_plus hvt _ _ h ht, List.map_cons, List.sum_cons]
    ring

theorem sum_VfA_eq {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (Ts : List Acc) (hT : ∀ t ∈ Ts, Acc.WF 6 t) (TOT : Acc)
    (hTOT : Ts.foldl Acc.plus (Acc.zero 6) = TOT) : (Ts.map (VfA vt)).sum = VfA vt TOT := by
  have h := (VfA_foldl_plus hvt Ts (Acc.zero 6) (Acc.wf_zero 6) hT).2
  rw [VfA_zero hvt, zero_add, hTOT] at h
  exact h.symm

end R45.GK
