import Romanoff.FoldSound
import K45.Defs

/-!
# A kernel-reducible normalization (structural merge sort with fuel, structural combine)

`List.mergeSort` does not reduce in the kernel (well-founded recursion).  `normK` sorts by a structural bottom-up merge
sort with fuel and merges equal adjacent keys by a structural combine.  Only `wsum` preservation is proved (it is a
permutation followed by merging equal keys); a kernel check `normK L = M` against a literal `M` then gives
`wsum M H = wsum L H` for every `H`.
-/

namespace K45

open R45 Romanoff

theorem mergeF_perm : ∀ (n : ℕ) (as bs : List (ℕ × ℕ)), (mergeF n as bs).Perm (as ++ bs)
  | 0, as, bs => List.Perm.refl _
  | _ + 1, [], bs => by simp [mergeF]
  | _ + 1, a :: as, [] => by simp [mergeF]
  | n + 1, a :: as, b :: bs => by
    unfold mergeF
    split_ifs
    · exact (mergeF_perm n as (b :: bs)).cons a
    · exact ((mergeF_perm n (a :: as) bs).cons b).trans List.perm_middle.symm

theorem mergePairs_perm : ∀ ls : List (List (ℕ × ℕ)), (mergePairs ls).flatten.Perm ls.flatten
  | [] => by simp [mergePairs]
  | [a] => by simp [mergePairs]
  | a :: b :: rest => by
    simp only [mergePairs, List.flatten_cons]
    refine ((mergeF_perm _ a b).append (mergePairs_perm rest)).trans ?_
    rw [List.append_assoc]

theorem msortK_perm : ∀ (n : ℕ) (ls : List (List (ℕ × ℕ))), (msortK n ls).Perm ls.flatten
  | 0, ls => by simp [msortK]
  | _ + 1, [] => by simp [msortK]
  | _ + 1, [l] => by simp [msortK]
  | n + 1, a :: b :: rest => by
    simp only [msortK]
    exact (msortK_perm n _).trans (mergePairs_perm _)

theorem wsum_combineS (H : ℕ → ℚ) : ∀ (a : ℕ × ℕ) (L : List (ℕ × ℕ)), wsum (combineS a L) H = wsum (a :: L) H
  | a, [] => rfl
  | a, b :: L => by
    unfold combineS
    split_ifs with h
    · rw [wsum_combineS H (a.1, a.2 + b.2) L, wsum_cons, wsum_cons, wsum_cons, h]
      push_cast
      ring
    · rw [wsum_cons, wsum_combineS H b L, wsum_cons a (b :: L)]

theorem wsum_combineAll (L : List (ℕ × ℕ)) (H : ℕ → ℚ) : wsum (combineAll L) H = wsum L H := by
  cases L with
  | nil => rfl
  | cons a L => exact wsum_combineS H a L

theorem wsum_mergeRuns (ls : List (List (ℕ × ℕ))) (H : ℕ → ℚ) : wsum (mergeRuns ls) H = wsum ls.flatten H := by
  unfold mergeRuns
  rw [wsum_combineAll, wsum_perm (msortK_perm 40 ls)]

theorem flatten_map_singleton (L : List (ℕ × ℕ)) : (L.map fun x => [x]).flatten = L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem wsum_normK (L : List (ℕ × ℕ)) (H : ℕ → ℚ) : wsum (normK L) H = wsum L H := by
  unfold normK
  rw [wsum_mergeRuns, flatten_map_singleton]

theorem prodK_append (per : ℕ) (A B opts : List (ℕ × ℕ)) :
    prodK per (A ++ B) opts = prodK per A opts ++ prodK per B opts := by
  unfold prodK
  rw [List.flatMap_append]

/-- One step against the products: `wsum (foldStep per L opts) H = wsum (prodK per L opts) H`. -/
theorem wsum_foldStep_prodK (per : ℕ) (L opts : List (ℕ × ℕ)) (H : ℕ → ℚ) :
    wsum (foldStep per L opts) H = wsum (prodK per L opts) H := by
  unfold foldStep prodK
  rw [wsum_normalize]

end K45
