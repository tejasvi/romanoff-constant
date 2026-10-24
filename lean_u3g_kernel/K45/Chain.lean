import K45.Norm

/-!
# Weighted-sum equivalence of fold lists, and the step checks

`WEq L M`: `wsum L H = wsum M H` for every `H`.  A fold step checked in chunks (`normK (prodK per C opts) = B` for each
chunk `C`, then `mergeRuns Bs = L'`) gives `WEq L' (foldStep per Cs.flatten opts)`, and `WEq` passes through `foldStep`.
-/

namespace K45

open R45 Romanoff

def WEq (L M : List (ℕ × ℕ)) : Prop := ∀ H : ℕ → ℚ, wsum L H = wsum M H

theorem WEq.refl (L : List (ℕ × ℕ)) : WEq L L := fun _ => rfl

theorem WEq.symm {L M : List (ℕ × ℕ)} (h : WEq L M) : WEq M L := fun H => (h H).symm

theorem WEq.trans {L M N : List (ℕ × ℕ)} (h1 : WEq L M) (h2 : WEq M N) : WEq L N := fun H => (h1 H).trans (h2 H)

theorem WEq.append {A A' B B' : List (ℕ × ℕ)} (hA : WEq A A') (hB : WEq B B') : WEq (A ++ B) (A' ++ B') :=
  fun H => by rw [wsum_append, wsum_append, hA H, hB H]

theorem WEq.flatten : ∀ {ls ms : List (List (ℕ × ℕ))}, List.Forall₂ WEq ls ms → WEq ls.flatten ms.flatten
  | [], [], .nil => WEq.refl _
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.flatten_cons]
    exact h.append (WEq.flatten t)

theorem WEq.foldStep {L M : List (ℕ × ℕ)} (h : WEq L M) (per : ℕ) (opts : List (ℕ × ℕ)) :
    WEq (foldStep per L opts) (foldStep per M opts) := fun H => by
  rw [wsum_foldStep, wsum_foldStep, h]

theorem weq_mergeRuns (ls : List (List (ℕ × ℕ))) : WEq (mergeRuns ls) ls.flatten := wsum_mergeRuns ls

theorem weq_normK (L : List (ℕ × ℕ)) : WEq (normK L) L := wsum_normK L

theorem weq_prodK (per : ℕ) (L opts : List (ℕ × ℕ)) : WEq (prodK per L opts) (foldStep per L opts) :=
  fun H => (wsum_foldStep_prodK per L opts H).symm

theorem prodK_flatten (per : ℕ) (opts : List (ℕ × ℕ)) :
    ∀ Cs : List (List (ℕ × ℕ)), prodK per Cs.flatten opts = (Cs.map fun C => prodK per C opts).flatten
  | [] => rfl
  | C :: Cs => by rw [List.flatten_cons, prodK_append, prodK_flatten per opts Cs, List.map_cons, List.flatten_cons]

/-- One fold step checked in chunks: the chunks `Cs` of the input, their normalized products `Bs` (each checked by the
kernel), and the merge `mergeRuns Bs = L'`. -/
theorem step_check {per : ℕ} {opts : List (ℕ × ℕ)} {Cs Bs : List (List (ℕ × ℕ))}
    (hB : List.Forall₂ (fun C B => normK (prodK per C opts) = B) Cs Bs) {L' : List (ℕ × ℕ)}
    (hM : mergeRuns Bs = L') : WEq L' (foldStep per Cs.flatten opts) := by
  have h1 : List.Forall₂ WEq Bs (Cs.map fun C => prodK per C opts) := by
    clear hM
    induction hB with
    | nil => exact .nil
    | cons h _ ih =>
      rw [List.map_cons]
      exact .cons (h ▸ weq_normK _) ih
  rw [← hM]
  exact ((weq_mergeRuns Bs).trans (WEq.flatten h1)).trans (by rw [← prodK_flatten]; exact weq_prodK per _ opts)

/-- A merge of checked runs: `mergeRuns Ms = L'` with `WEq` runs. -/
theorem merge_check {Ms Ns : List (List (ℕ × ℕ))} (h : List.Forall₂ WEq Ms Ns) {L' : List (ℕ × ℕ)}
    (hM : mergeRuns Ms = L') : WEq L' Ns.flatten := by
  rw [← hM]
  exact (weq_mergeRuns Ms).trans (WEq.flatten h)

end K45
