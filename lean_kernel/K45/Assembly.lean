import K45.OrbF

/-!
# Glue for the generated fold assembly (`K45.G.Fold`)

A whole step from `normK (prodK per L opts) = L'`, a chunked step with a two-level merge, and the orbit chunks.
-/

namespace K45

open R45 Romanoff

theorem step_of_normK {per : ℕ} {L opts L' : List (ℕ × ℕ)} (hL : ∀ x ∈ L, 0 < x.2) (ho : ∀ x ∈ opts, 0 < x.2)
    (h : normK (prodK per L opts) = L') (hs : strictPos L' = true) : foldStep per L opts = L' :=
  step_exact hL ho (h ▸ (weq_normK _).trans (weq_prodK per L opts)) hs

/-- The normalized products of the chunks, concatenated, against the step. -/
theorem chunks_weq {per : ℕ} {opts : List (ℕ × ℕ)} {Cs Bs : List (List (ℕ × ℕ))}
    (hB : List.Forall₂ (fun C B => normK (prodK per C opts) = B) Cs Bs) :
    WEq Bs.flatten (foldStep per Cs.flatten opts) := by
  have h1 : List.Forall₂ WEq Bs (Cs.map fun C => prodK per C opts) := by
    induction hB with
    | nil => exact .nil
    | cons h _ ih =>
      rw [List.map_cons]
      exact .cons (h ▸ weq_normK _) ih
  exact (WEq.flatten h1).trans (by rw [← prodK_flatten]; exact weq_prodK per _ opts)

theorem groups_weq : ∀ {Gs : List (List (List (ℕ × ℕ)))} {Ms : List (List (ℕ × ℕ))},
    List.Forall₂ (fun G M => mergeRuns G = M) Gs Ms → WEq Ms.flatten Gs.flatten.flatten
  | [], [], .nil => WEq.refl _
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.flatten_cons, List.flatten_append]
    exact (h ▸ weq_mergeRuns _).append (groups_weq t)

/-- A chunked step whose chunk outputs are merged in groups, then the group results merged. -/
theorem step_check2 {per : ℕ} {opts : List (ℕ × ℕ)} {Cs Bs : List (List (ℕ × ℕ))}
    {Gs : List (List (List (ℕ × ℕ)))} {Ms : List (List (ℕ × ℕ))}
    (hB : List.Forall₂ (fun C B => normK (prodK per C opts) = B) Cs Bs)
    (hG : List.Forall₂ (fun G M => mergeRuns G = M) Gs Ms) (hGB : Gs.flatten = Bs) {L' : List (ℕ × ℕ)}
    (hM : mergeRuns Ms = L') : WEq L' (foldStep per Cs.flatten opts) := by
  rw [← hM]
  refine (weq_mergeRuns Ms).trans ((groups_weq hG).trans ?_)
  rw [hGB]
  exact chunks_weq hB

end K45
