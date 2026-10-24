import K45.Exact
import K45.NFast

/-!
# The orbit list from the last fold list, with the fast `nShift`

`orbits per ps` maps each entry `(x, cnt)` of the fold to `⟨cnt, popcount u, nShift u⟩`, `u = full ^^^ x` (dropping
`u = 0`).  `orbF` computes the same with `nFast` and `s = n(0)`.  Orbits are stored one natural number each,
`z = cnt·2^847 + s·2^840 + Σ_c n(c)·2^(7c)`, decoded by `orbOf`.
-/

namespace K45

open R45 Romanoff

theorem headD_eq_getD (l : List ℕ) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

theorem popcount_eq_headD {per : ℕ} (hper : 0 < per) (u : ℕ) : popcount per u = (nShift per u).headD 0 := by
  rw [headD_eq_getD, nShift_getD per u 0 hper, popcount_eq]
  congr 1
  refine Finset.filter_congr fun e he => ?_
  rw [Nat.add_zero, Nat.mod_eq_of_lt (Finset.mem_range.mp he)]
  simp

theorem orbits_eq_filterMap (ps : List ℕ) : orbits 120 ps = (foldOrbits 120 ps).filterMap orbF := by
  unfold orbits
  congr 1
  funext xc
  dsimp only
  unfold orbF
  split_ifs with h
  · rfl
  · rw [nFast_eq (by norm_num), ← popcount_eq_headD (by norm_num)]

theorem filterMap_flatten {α β : Type} (f : α → Option β) :
    ∀ ls : List (List α), ls.flatten.filterMap f = (ls.map (List.filterMap f)).flatten
  | [] => rfl
  | l :: ls => by rw [List.flatten_cons, List.filterMap_append, filterMap_flatten f ls, List.map_cons, List.flatten_cons]

theorem map_filterMap_of_forall₂ {cs : List (List (ℕ × ℕ))} {os : List (List Orb)}
    (h : List.Forall₂ (fun c o => c.filterMap orbF = o) cs os) : cs.map (List.filterMap orbF) = os := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.map_cons, h, ih]

end K45
