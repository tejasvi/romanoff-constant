import GK.Spec3

/-!
# k45g, proofs part 4: `Rrow` of a fibered core row, `T2 = RK`, and the key theorem `VfA (evalKeyK x) = Vf (evalKey x)`
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

attribute [local irreducible] R45.GK.pats R45.GK.sigs R45.GK.sigF R45.GK.o41r R45.EVG.zOf R45.EVG.tOf
  Romanoff.G.S2.csOf R45.EVG.pqA R45.EVG.pfA R45.EVG.pwA

/-! ## The pattern check unpacked -/

theorem patsOK_spec (h : patsOK = true) : pats.length = 38 ∧ ∀ P < 38,
    (pats.getD P patD).pw = pwA.getD P 0 ∧
    (pats.getD P patD).pf = (List.range 4).map (fun u => pfA.getD (4 * P + u) 0) ∧
    (pats.getD P patD).pq = (List.range 4).map (fun t => (List.range 10).map fun k => pqA.getD (40 * P + (10 * t + k)) 0) := by
  unfold patsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun P hP => ⟨(h.2 P hP).1.1, (h.2 P hP).1.2, (h.2 P hP).2⟩⟩

theorem list_eq_map_getD {α : Type*} (L : List α) (d : α) : L = (List.range L.length).map fun i => L.getD i d := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD, List.getElem?_eq_getElem h1]

theorem zrRow_length (R : ℕ) : (zrRow R).length = 4 := by simp [zrRow, bn0, bn1]

theorem zrRow_get_length (R : ℕ) {t : ℕ} (ht : t < 4) : ((zrRow R).getD t []).length = 10 := by
  interval_cases t <;> simp [zrRow, puL, pvL, bn0, bn1]

theorem cOfT_length (M : ℕ) (fw : List ℕ) : (cOfT M fw).length = 10 := by simp [cOfT, puL, pvL]

theorem getD_zipWith_dotL (A B : List (List ℕ)) {k : ℕ} (hA : k < A.length) (hB : k < B.length) :
    (List.zipWith dotL A B).getD k 0 = dotL (A.getD k []) (B.getD k []) := by
  rw [List.getD_eq_getElem _ _ (by simp [hA, hB]), List.getElem_zipWith, List.getD_eq_getElem _ _ hA,
    List.getD_eq_getElem _ _ hB]

theorem getD_map_zip (σc : List (List ℕ)) : ∀ (Z : List (List (List ℕ))) (t : ℕ),
    (Z.map fun Zt => List.zipWith dotL σc Zt).getD t [] = List.zipWith dotL σc (Z.getD t [])
  | [], t => by simp
  | z :: Z, 0 => by simp
  | z :: Z, t + 1 => by rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]; exact getD_map_zip σc Z t

/-! ## `Q` of a pattern -/

theorem Q_eq (R M : ℕ) (hM : Fib M) (σ : Sig) (hc : σ.c = cOfT M ((List.range 12).map (fwE M))) (P : ℕ)
    (hpq : (pats.getD P patD).pq = (List.range 4).map (fun t => (List.range 10).map fun k => pqA.getD (40 * P + (10 * t + k)) 0)) :
    qOf (zOf (tOf (csOf (repB 120 360 R ||| M)))) P =
      sumL (List.zipWith dotL (pats.getD P patD).pq ((zrRow R).map fun Zt => List.zipWith dotL σ.c Zt)) := by
  rw [qOf_eq, sumL_zipWith_dotL _ _ 4 (by rw [hpq]; simp) (by simp [zrRow_length])]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hlen : (((zrRow R).map fun Zt => List.zipWith dotL σ.c Zt).getD t []).length = 10 := by
    rw [getD_map_zip, List.length_zipWith, hc, cOfT_length, zrRow_get_length R ht']
    rfl
  rw [hpq, List.getD_eq_getElem _ _ (by simp [ht']), List.getElem_map, List.getElem_range,
    dotL_map_range _ _ 10 hlen]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have hz : (zOf (tOf (csOf (repB 120 360 R ||| M)))).getD (10 * t + k) 0 =
      (((zrRow R).map fun Zt => List.zipWith dotL σ.c Zt).getD t []).getD k 0 := by
    rw [getD_map_zip, getD_zipWith_dotL _ _ (by rw [hc, cOfT_length]; exact hk')
        (by rw [zrRow_get_length R ht']; exact hk')]
    exact Z_eq R M hM σ hc ht' hk'
  rw [hz]

/-! ## `Rrow` of a fibered core row -/

theorem Rrow_eq_sigVal (vt : ℕ → ℕ → ℕ → ℚ) (R M : ℕ) (hM : Fib M) (σ : Sig) (hσ : sigOKb M σ = true)
    (hP : patsOK = true) : Rrow vt (repB 120 360 R ||| M) = sigVal vt (nRg R) (zrRow R) σ := by
  obtain ⟨hlen, hpat⟩ := patsOK_spec hP
  have hσ' := hσ
  simp only [sigOKb, Bool.and_eq_true, beq_iff_eq] at hσ'
  obtain ⟨hfwg, hc⟩ := hσ'
  unfold Rrow sigVal
  rw [list_eq_map_getD pats patD, hlen, List.map_map]
  congr 1
  apply List.map_congr_left
  intro P hPm
  have hP' : P < 38 := List.mem_range.mp hPm
  obtain ⟨hpw, hpf, hpq⟩ := hpat P hP'
  simp only [Function.comp, rowSQ]
  rw [s_eq R M hM σ hfwg P hpf, Q_eq R M hM σ hc P hpq, hpw]

end R45.GK
