import GK.Spec4
import Romanoff.G.S2.Lift

/-!
# k45g, proofs part 5: `T2 = RK` and the key theorem `VfA vt (evalKeyK x) = Vf vt (evalKey x)`

From the data checks (`patsOK`, `fibOK`, `sigOKall`, `wtOK`, `o41OK`) and parts 1-4: the value of the fibered evaluator's tree
for a BASE key equals the value of the native evaluator's accumulator, for every slot function linear in the slot sums.
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

attribute [local irreducible] R45.GK.pats R45.GK.sigs R45.GK.sigF R45.GK.o41r R45.EVG.zOf R45.EVG.tOf
  Romanoff.G.S2.csOf R45.EVG.pqA R45.EVG.pfA R45.EVG.pwA R45.optsP R45.maskP R45.EVG.repB R45.GK.triples
  R45.GK.wtsOf

/-! ## Unpacking the checks -/

theorem fib_of_fibOK (h : fibOK = true) : ∀ mc ∈ optsP 360 19 ++ optsP 360 73 ++ optsP 360 37, Fib mc.1 := by
  unfold fibOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  intro mc hmc x hx
  exact h mc hmc x hx

theorem fib_or {A B : ℕ} (hA : Fib A) (hB : Fib B) : Fib (A ||| B) := by
  intro x hx
  rw [ind_or, ind_or, hA x hx, hB x hx]

theorem fib_triples (h : fibOK = true) : ∀ tw ∈ triples, Fib tw.1 := by
  have hf := fib_of_fibOK h
  intro tw htw
  simp only [triples, List.mem_flatMap, List.mem_map] at htw
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := htw
  exact fib_or (fib_or (hf a (by simp [ha])) (hf b (by simp [hb]))) (hf c (by simp [hc]))

theorem sigOKall_spec (h : sigOKall = true) : triples.length = sigF.length ∧ (∀ s ∈ sigF, s < sigs.length) ∧
    ∀ ts ∈ triples.zip sigF, sigOKb ts.1.1 (sigs.getD ts.2 sigD) = true := by
  unfold sigOKall at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## Sums over flattened option lists -/

theorem sum_map_flatMap {α β : Type*} (f : α → List β) (g : β → ℚ) :
    ∀ L : List α, ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum
  | [] => by simp
  | a :: L => by rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap f g L, List.map_cons,
      List.sum_cons]

theorem T2_eq_triples (vt : ℕ → ℕ → ℕ → ℚ) (X : ℕ) :
    T2 vt X = (triples.map fun tw => (tw.2 : ℚ) * Rrow vt (X ||| tw.1)).sum := by
  unfold triples
  rw [sum_map_flatMap]
  unfold T2
  congr 1
  apply List.map_congr_left
  intro a _
  rw [sum_map_flatMap]
  unfold T3
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b _
  unfold T4
  rw [List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, Nat.lor_assoc]
  push_cast; ring

/-! ## Regrouping by signature -/

theorem getD_modify_nat (acc : List ℕ) (i j w : ℕ) (hi : i < acc.length) :
    (acc.modify i (· + w)).getD j 0 = if j = i then acc.getD j 0 + w else acc.getD j 0 := by
  by_cases hj : j < acc.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_modify, List.getD_eq_getElem _ _ hj]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Ne.symm hji, hji]
  · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by simpa using hj)]
    have : j ≠ i := fun h => hj (h ▸ hi)
    simp [this]

theorem foldl_weights (G : ℕ → ℚ) (n : ℕ) : ∀ (L : List ((ℕ × ℕ) × ℕ)) (acc : List ℕ), acc.length = n →
    (∀ ts ∈ L, ts.2 < n) →
      ∑ s ∈ range n, ((L.foldl (fun acc ts => acc.modify ts.2 (· + ts.1.2)) acc).getD s 0 : ℚ) * G s =
        ∑ s ∈ range n, (acc.getD s 0 : ℚ) * G s + (L.map fun ts => (ts.1.2 : ℚ) * G ts.2).sum
  | [], acc, _, _ => by simp
  | ts :: L, acc, hacc, hL => by
    rw [List.foldl_cons, foldl_weights G n L _ (by simp [hacc]) (fun ts' h => hL ts' (by simp [h]))]
    have hs := hL ts (by simp)
    have e : ∀ s ∈ range n, ((acc.modify ts.2 (· + ts.1.2)).getD s 0 : ℚ) * G s =
        (acc.getD s 0 : ℚ) * G s + if s = ts.2 then (ts.1.2 : ℚ) * G ts.2 else 0 := by
      intro s _
      rw [getD_modify_nat acc ts.2 s ts.1.2 (by omega)]
      by_cases h : s = ts.2
      · subst h; simp; ring
      · simp [h]
    rw [sum_congr rfl e, sum_add_distrib, sum_ite_eq' (range n) ts.2, if_pos (mem_range.mpr hs), List.map_cons,
      List.sum_cons]
    ring

theorem sum_map_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ range n, g i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range g n, sum_range_succ]; simp

theorem sum_sigs (F : Sig → ℚ) : (sigs.map F).sum = ∑ s ∈ range sigs.length, F (sigs.getD s sigD) := by
  conv_lhs => rw [list_eq_map_getD sigs sigD]
  rw [List.map_map, sum_map_range]
  rfl

theorem map_zip_fst {α β γ : Type*} (f : α → γ) : ∀ (L : List α) (M : List β), L.length ≤ M.length →
    (L.zip M).map (fun p => f p.1) = L.map f
  | [], _, _ => by simp
  | a :: L, [], h => by simp at h
  | a :: L, b :: M, h => by simp [map_zip_fst f L M (by simpa using h)]

theorem T2_eq_RK (vt : ℕ → ℕ → ℕ → ℚ) (R : ℕ) (hP : patsOK = true) (hF : fibOK = true) (hS : sigOKall = true)
    (hW : wtOK = true) : T2 vt (repB 120 360 R) = RK vt R := by
  obtain ⟨hlen, hlt, hok⟩ := sigOKall_spec hS
  have hfib := fib_triples hF
  rw [T2_eq_triples]
  -- pair each triple with its signature index
  have e1 : (triples.map fun tw => (tw.2 : ℚ) * Rrow vt (repB 120 360 R ||| tw.1)).sum =
      ((triples.zip sigF).map fun ts => (ts.1.2 : ℚ) * sigVal vt (nRg R) (zrRow R) (sigs.getD ts.2 sigD)).sum := by
    have hz : triples.map (fun tw => (tw.2 : ℚ) * Rrow vt (repB 120 360 R ||| tw.1)) =
        (triples.zip sigF).map (fun ts => (ts.1.2 : ℚ) * Rrow vt (repB 120 360 R ||| ts.1.1)) :=
      (map_zip_fst (fun tw : ℕ × ℕ => (tw.2 : ℚ) * Rrow vt (repB 120 360 R ||| tw.1)) triples sigF (by omega)).symm
    rw [hz]
    congr 1
    apply List.map_congr_left
    intro ts hts
    have hmem : ts.1 ∈ triples := (List.of_mem_zip hts).1
    rw [Rrow_eq_sigVal vt R ts.1.1 (hfib ts.1 hmem) _ (hok ts hts) hP]
  rw [e1]
  -- regroup by the signature index
  have hlt' : ∀ ts ∈ triples.zip sigF, ts.2 < sigs.length := fun ts hts => hlt ts.2 (List.of_mem_zip hts).2
  have hw := foldl_weights (fun s => sigVal vt (nRg R) (zrRow R) (sigs.getD s sigD)) sigs.length (triples.zip sigF)
    (List.replicate sigs.length 0) (by simp) hlt'
  have hz0 : ∑ s ∈ range sigs.length, (((List.replicate sigs.length 0).getD s 0 : ℕ) : ℚ) *
      sigVal vt (nRg R) (zrRow R) (sigs.getD s sigD) = 0 := by
    refine sum_eq_zero fun s hs => ?_
    rw [List.getD_eq_getElem _ _ (by simpa using mem_range.mp hs), List.getElem_replicate]; simp
  rw [hz0, zero_add] at hw
  rw [← hw]
  have hW' : wtsOf = sigs.map (·.wt) := by unfold wtOK at hW; exact beq_iff_eq.mp hW
  unfold RK
  rw [sum_sigs]
  refine sum_congr rfl fun s hs => ?_
  have hs' := mem_range.mp hs
  have : wtsOf.getD s 0 = (sigs.getD s sigD).wt := by
    rw [hW', List.getD_eq_getElem _ _ (by simpa using hs'), List.getElem_map, List.getD_eq_getElem _ _ hs']
  unfold wtsOf at this
  rw [this]

/-! ## The key theorem -/

theorem o41OK_spec (h : o41OK = true) : optsP 360 41 = o41r.map fun mc => (repB 120 360 mc.1, mc.2) := by
  unfold o41OK at h; exact beq_iff_eq.mp h

theorem T1_eq (vt : ℕ → ℕ → ℕ → ℚ) (x : ℕ) (hO : o41OK = true) (hP : patsOK = true) (hF : fibOK = true)
    (hS : sigOKall = true) (hW : wtOK = true) :
    T1 vt (repB 120 360 x) = (o41r.map fun mc => (mc.2 : ℚ) * RK vt (x ||| mc.1)).sum := by
  unfold T1
  rw [o41OK_spec hO, List.map_map]
  congr 1
  apply List.map_congr_left
  intro mc _
  simp only [Function.comp]
  rw [← repB_or, T2_eq_RK vt _ hP hF hS hW]

theorem key_eq {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) (x : ℕ) (hO : o41OK = true) (hP : patsOK = true)
    (hF : fibOK = true) (hS : sigOKall = true) (hW : wtOK = true) : VfA vt (evalKeyK x) = Vf vt (evalKey x) := by
  rw [(VfA_evalKeyK hvt x).2, (Vf_evalKey hvt x).2, T1_eq vt x hO hP hF hS hW]

end R45.GK
