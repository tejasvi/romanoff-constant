import K45.Chain

/-!
# Exactness of a checked fold step

`normalize` returns a list with strictly increasing keys and positive counts (`combine` of a key-sorted list).  Two such
lists with equal weighted sums are equal (`eq_of_weq`), so a literal `L'` with `strictPos L' = true` (a kernel check) and
`WEq L' (foldStep per L opts)` (the chunked checks of `K45.Chain`) is exactly `foldStep per L opts`.
-/

namespace K45

open R45 Romanoff

theorem strictPos_spec : ∀ L : List (ℕ × ℕ), strictPos L = true →
    L.Pairwise (fun a b => a.1 < b.1) ∧ ∀ x ∈ L, 0 < x.2
  | [], _ => ⟨List.Pairwise.nil, by simp⟩
  | [a], h => by
    simp only [strictPos, decide_eq_true_eq] at h
    exact ⟨List.pairwise_singleton _ _, by simpa using h⟩
  | a :: b :: L, h => by
    simp only [strictPos, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, hab⟩, ht⟩ := h
    obtain ⟨hp, hpos⟩ := strictPos_spec (b :: L) ht
    refine ⟨List.Pairwise.cons (fun y hy => ?_) hp, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hab
      · exact lt_trans hab ((List.pairwise_cons.mp hp).1 y hy)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact h0
      · exact hpos x hx

/-- The count of key `k`. -/
def cntK (k : ℕ) (L : List (ℕ × ℕ)) : ℚ := wsum L fun x => if x = k then 1 else 0

theorem cntK_cons (k : ℕ) (a : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    cntK k (a :: L) = (if a.1 = k then (a.2 : ℚ) else 0) + cntK k L := by
  unfold cntK
  rw [wsum_cons]
  split_ifs <;> simp

theorem cntK_of_lt (k : ℕ) : ∀ L : List (ℕ × ℕ), (∀ x ∈ L, k < x.1) → cntK k L = 0
  | [], _ => rfl
  | a :: L, h => by
    have ha := h a List.mem_cons_self
    rw [cntK_cons, ite_eq_right (show ¬ a.1 = k by omega),
      cntK_of_lt k L (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

theorem cntK_head {a : ℕ × ℕ} {L : List (ℕ × ℕ)} (h : (a :: L).Pairwise (fun a b => a.1 < b.1)) :
    cntK a.1 (a :: L) = a.2 := by
  rw [cntK_cons, ite_eq_left rfl, cntK_of_lt _ L (List.pairwise_cons.mp h).1, add_zero]

theorem cntK_weq {A B : List (ℕ × ℕ)} (h : WEq A B) (k : ℕ) : cntK k A = cntK k B := h _

/-- Two lists with strictly increasing keys, positive counts and equal weighted sums are equal. -/
theorem eq_of_weq : ∀ (A B : List (ℕ × ℕ)), A.Pairwise (fun a b => a.1 < b.1) → B.Pairwise (fun a b => a.1 < b.1) →
    (∀ x ∈ A, 0 < x.2) → (∀ x ∈ B, 0 < x.2) → WEq A B → A = B
  | [], [], _, _, _, _, _ => rfl
  | [], b :: B, _, hB, _, hB0, h => by
    have h1 := cntK_weq h b.1
    rw [cntK_head hB] at h1
    have : (0 : ℚ) < b.2 := by exact_mod_cast hB0 b List.mem_cons_self
    exact absurd h1 (by rw [show cntK b.1 [] = 0 from rfl]; exact ne_of_lt this)
  | a :: A, [], hA, _, hA0, _, h => by
    have h1 := cntK_weq h a.1
    rw [cntK_head hA] at h1
    have : (0 : ℚ) < a.2 := by exact_mod_cast hA0 a List.mem_cons_self
    exact absurd h1 (by rw [show cntK a.1 [] = 0 from rfl]; exact ne_of_gt this)
  | a :: A, b :: B, hA, hB, hA0, hB0, h => by
    have hAt := (List.pairwise_cons.mp hA).1
    have hBt := (List.pairwise_cons.mp hB).1
    have hapos : (0 : ℚ) < a.2 := by exact_mod_cast hA0 a List.mem_cons_self
    have hbpos : (0 : ℚ) < b.2 := by exact_mod_cast hB0 b List.mem_cons_self
    have hab : a.1 = b.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h1 := cntK_weq h a.1
        rw [cntK_head hA, cntK_of_lt a.1 (b :: B) (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hlt
          · exact lt_trans hlt (hBt x hx))] at h1
        exact absurd h1 (ne_of_gt hapos)
      · have h1 := cntK_weq h b.1
        rw [cntK_head hB, cntK_of_lt b.1 (a :: A) (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hlt
          · exact lt_trans hlt (hAt x hx))] at h1
        exact absurd h1 (ne_of_lt hbpos)
    have h2 : a.2 = b.2 := by
      have h1 := cntK_weq h a.1
      rw [cntK_head hA, hab, cntK_head hB] at h1
      exact_mod_cast h1
    have hab' : a = b := Prod.ext hab h2
    subst hab'
    congr 1
    refine eq_of_weq A B hA.of_cons hB.of_cons (fun x hx => hA0 x (List.mem_cons_of_mem _ hx))
      (fun x hx => hB0 x (List.mem_cons_of_mem _ hx)) fun H => ?_
    have := h H
    rw [wsum_cons, wsum_cons] at this
    linarith

/-- `combine` of a key-sorted list has strictly increasing keys. -/
theorem combine_sorted : ∀ L : List (ℕ × ℕ), L.Pairwise (fun a b => a.1 ≤ b.1) →
    (combine L).Pairwise (fun a b => a.1 < b.1)
  | [], _ => by simp [combine]
  | [a], _ => by simp [combine]
  | a :: b :: L, h => by
    unfold combine
    have hab := (List.pairwise_cons.mp h).1 b List.mem_cons_self
    have hbL := (List.pairwise_cons.mp h).2
    split_ifs with he
    · have he' : a.1 = b.1 := beq_iff_eq.mp he
      refine combine_sorted ((a.1, a.2 + b.2) :: L) (List.Pairwise.cons (fun y hy => ?_) hbL.of_cons)
      rw [he']
      exact (List.pairwise_cons.mp hbL).1 y hy
    · have hne : a.1 ≠ b.1 := fun e => he (beq_iff_eq.mpr e)
      refine List.Pairwise.cons ?_ (combine_sorted (b :: L) hbL)
      intro y hy
      refine combine_keys (fun k => a.1 < k) (b :: L) (fun z hz => ?_) y hy
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · have := (List.pairwise_cons.mp hbL).1 z hz
        omega
termination_by L => L.length

theorem combine_pos : ∀ L : List (ℕ × ℕ), (∀ x ∈ L, 0 < x.2) → ∀ x ∈ combine L, 0 < x.2
  | [], _ => by simp [combine]
  | [a], h => by simpa [combine] using h
  | a :: b :: L, h => by
    unfold combine
    split_ifs
    · refine combine_pos ((a.1, a.2 + b.2) :: L) (fun y hy => ?_)
      rcases List.mem_cons.mp hy with rfl | hy
      · have := h a List.mem_cons_self
        simp only
        omega
      · exact h y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h x List.mem_cons_self
      · exact combine_pos (b :: L) (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx
termination_by L => L.length

theorem normalize_strictPos (L : List (ℕ × ℕ)) (h : ∀ x ∈ L, 0 < x.2) :
    (R45.normalize L).Pairwise (fun a b => a.1 < b.1) ∧ ∀ x ∈ R45.normalize L, 0 < x.2 := by
  unfold R45.normalize
  have hs : (L.mergeSort fun a b => a.1 ≤ b.1).Pairwise (fun a b => a.1 ≤ b.1) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ × ℕ => decide (a.1 ≤ b.1))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) L
    exact this.imp fun h => by simpa using h
  have hp : ∀ x ∈ L.mergeSort (fun a b => a.1 ≤ b.1), 0 < x.2 :=
    fun x hx => h x ((List.mergeSort_perm L _).mem_iff.mp hx)
  exact ⟨combine_sorted _ hs, combine_pos _ hp⟩

theorem prodK_pos {per : ℕ} {L opts : List (ℕ × ℕ)} (hL : ∀ x ∈ L, 0 < x.2) (ho : ∀ x ∈ opts, 0 < x.2) :
    ∀ x ∈ prodK per L opts, 0 < x.2 := by
  intro x hx
  unfold prodK at hx
  obtain ⟨xc, hxc, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨mc, hmc, rfl⟩ := List.mem_map.mp hx
  exact Nat.mul_pos (hL xc hxc) (ho mc hmc)

/-- A checked step is exact. -/
theorem step_exact {per : ℕ} {L opts L' : List (ℕ × ℕ)} (hL : ∀ x ∈ L, 0 < x.2) (ho : ∀ x ∈ opts, 0 < x.2)
    (hw : WEq L' (foldStep per L opts)) (hs : strictPos L' = true) : foldStep per L opts = L' := by
  have hn := normalize_strictPos (prodK per L opts) (prodK_pos hL ho)
  obtain ⟨hs1, hs2⟩ := strictPos_spec L' hs
  exact eq_of_weq _ _ hn.1 hs1 hn.2 hs2 hw.symm

end K45
