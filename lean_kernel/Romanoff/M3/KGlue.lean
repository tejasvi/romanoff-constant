import Romanoff.M3.KSplit

/-!
# M3, K version: chaining lemmas for the shards
-/

namespace Romanoff.M3

open R45.M3

theorem runDPD_append : ∀ (gs1 gs2 : List Grp) (tab : List Ent) (d : ℕ),
    runDPD tab d (gs1 ++ gs2) = runDPD (runDPD tab d gs1).1 (runDPD tab d gs1).2 gs2
  | [], gs2, tab, d => rfl
  | g :: gs1, gs2, tab, d => by
    simp only [List.cons_append, runDPD]
    exact runDPD_append gs1 gs2 _ _

theorem seg_step (tab : List Ent) (d : ℕ) (gs : List Grp) (n : ℕ) (lb : List ℕ) (db : ℕ)
    (h : segOK tab d (gs.take n) lb db = true) : runDPD tab d gs = runDPD (decTabK lb) db (gs.drop n) := by
  conv_lhs => rw [← List.take_append_drop n gs]
  rw [runDPD_append, segOK_sound _ _ _ _ _ h]

theorem drop_drop' {α : Type*} (l : List α) (a n b : ℕ) (h : a + n = b) : (l.drop a).drop n = l.drop b := by
  rw [List.drop_drop, ← h, Nat.add_comm]

theorem map_seg {α β : Type*} (f : α → β) (l : List α) (n : ℕ) (bds : List β) (h : (l.take n).map f = bds) :
    l.map f = bds ++ (l.drop n).map f := by
  conv_lhs => rw [← List.take_append_drop n l]
  rw [List.map_append, h]

theorem beq_true {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

end Romanoff.M3

namespace Romanoff.M3

open R45.M3

theorem accSplitK_sound' (s : ℕ) (tab : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = div120.map fun h => (h, tab.filter fun x => keyH x == h)) (acc : List ℕ)
    (h1 : (accSplitK s subs).2 = true) (h2 : (accSplitK s subs).1 = acc) : accG s tab = acc :=
  accSplitK_sound s tab subs hsubs acc (Prod.ext h2 h1)

end Romanoff.M3

namespace Romanoff.M3

open R45.M3

theorem segR_step (tab : List Ent) (gs : List Grp) (n : ℕ) (lb : List ℕ) (h : segROK tab (gs.take n) lb = true) :
    runDP tab gs = runDP (decTabK lb) (gs.drop n) := by
  conv_lhs => rw [← List.take_append_drop n gs]
  rw [runDP_append, segROK_sound _ _ _ h]

end Romanoff.M3
