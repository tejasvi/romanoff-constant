import Romanoff.M3.Fs

/-!
# M3 soundness, part 3: the DP tables

A table is read through linear functionals `wS sel H tab = Σ_{x ∈ tab} sel(x) H(x.L)` (`sel = a` or `b`).  Merging,
sorting and splitting into runs preserve them.  With `Hf ps ψ L = Fs ps (ψ ∘ lcm L)`:

* `step_up`: `wB (Hf (group ++ ps) ψ) tab ≤ wB (Hf ps ψ) (stepM tab g)`, and `step_lo` the reverse for `wA`,
  for `ψ ≥ 0` vanishing at `0` and above `LMAX` (pruned entries carry no mass of such `ψ`);
* `T_bound`: `SC · Fs (flatG gs) φ ≤ Σ b φ χ + B (piUp - Σ a χ)` for `φ ≥ 0` bounded by `B` at `0` and above `LMAX`,
  `χ = [1 ≤ L ≤ LMAX]` (split `φ = φ χ + φ (1 - χ)`, `Fs (1 - χ) = Fs 1 - Fs χ`);
* `lo_bound`: `Σ a ψ χ ≤ SC · Fs (flatG gs) ψ`.
-/

namespace Romanoff.M3

open R45.M3

/-! ## Fixed point -/

theorem SC_pos : (0 : ℝ) < (SC : ℝ) := by unfold SC; positivity

theorem cdiv_ge (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ (((n + d - 1) / d : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have h4 : n + d - 1 < (n + d - 1) / d * d + d := Nat.lt_div_mul_add hd
  have h1 : n ≤ (n + d - 1) / d * d := by
    generalize (n + d - 1) / d * d = k at h4 ⊢
    omega
  exact_mod_cast h1

theorem floor_le (n d : ℕ) : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le

theorem mulUp_ge (x y : ℕ) : (x : ℝ) * y / SC ≤ (mulUp x y : ℝ) := by
  unfold mulUp
  have := cdiv_ge (x * y) SC (by unfold SC; positivity)
  push_cast at this
  exact this

theorem mulLo_le (x y : ℕ) : (mulLo x y : ℝ) ≤ (x : ℝ) * y / SC := by
  unfold mulLo
  have := floor_le (x * y) SC
  push_cast at this
  exact this

theorem fUp_ge (p : ℕ) (hp : 3 ≤ p) : (SC : ℝ) * fp p ≤ (fUp p : ℝ) := by
  unfold fUp fp
  have h := cdiv_ge SC (p - 2) (by omega)
  have he : SC + (p - 2) - 1 = SC + p - 3 := by omega
  rw [he] at h
  have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hp2] at h
  calc (SC : ℝ) * (1 / ((p : ℝ) - 2)) = (SC : ℝ) / ((p : ℝ) - 2) := by ring
    _ ≤ _ := h

theorem fLo_le (p : ℕ) (hp : 3 ≤ p) : (fLo p : ℝ) ≤ (SC : ℝ) * fp p := by
  unfold fLo fp
  have h := floor_le SC (p - 2)
  have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hp2] at h
  calc (fLo p : ℝ) ≤ (SC : ℝ) / ((p : ℝ) - 2) := h
    _ = (SC : ℝ) * (1 / ((p : ℝ) - 2)) := by ring

theorem prod_one_add_nonneg : ∀ (ps : List ℕ), (∀ p ∈ ps, 3 ≤ p) → 1 ≤ (ps.map fun p => 1 + fp p).prod
  | [], _ => by simp
  | p :: ps, h => by
    have h1 := prod_one_add_nonneg ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h2 := fp_nonneg (h p (by simp))
    simp only [List.map_cons, List.prod_cons]
    nlinarith

theorem foldl_up : ∀ (ps : List ℕ) (acc : ℕ), (∀ p ∈ ps, 3 ≤ p) →
    (acc : ℝ) * (ps.map fun p => 1 + fp p).prod ≤ (ps.foldl (fun acc p => mulUp acc (SC + fUp p)) acc : ℕ) ∧
      acc ≤ ps.foldl (fun acc p => mulUp acc (SC + fUp p)) acc
  | [], acc, _ => by simp
  | p :: ps, acc, h => by
    have hp := h p (by simp)
    have hps : ∀ q ∈ ps, 3 ≤ q := fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨ih1, ih2⟩ := foldl_up ps (mulUp acc (SC + fUp p)) hps
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have hstep : (acc : ℝ) * (1 + fp p) ≤ (mulUp acc (SC + fUp p) : ℝ) := by
      have h1 := mulUp_ge acc (SC + fUp p)
      have h2 := fUp_ge p hp
      have hacc : (0 : ℝ) ≤ acc := Nat.cast_nonneg _
      push_cast at h1
      calc (acc : ℝ) * (1 + fp p) = (acc : ℝ) * ((SC : ℝ) + (SC : ℝ) * fp p) / SC := by
            field_simp [SC_pos.ne']
        _ ≤ (acc : ℝ) * ((SC : ℝ) + (fUp p : ℝ)) / SC := by
            apply div_le_div_of_nonneg_right _ SC_pos.le
            exact mul_le_mul_of_nonneg_left (by linarith) hacc
        _ ≤ _ := h1
    have hle : acc ≤ mulUp acc (SC + fUp p) := by
      unfold mulUp
      have hSC : 1 ≤ SC := Nat.one_le_two_pow
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      have h1 : acc * SC ≤ acc * (SC + fUp p) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      generalize acc * (SC + fUp p) = X at h1 ⊢
      generalize acc * SC = Y at h1 ⊢
      omega
    refine ⟨?_, le_trans hle ih2⟩
    have hprod := le_trans zero_le_one (prod_one_add_nonneg ps hps)
    calc (acc : ℝ) * ((1 + fp p) * (ps.map fun p => 1 + fp p).prod)
        = (acc : ℝ) * (1 + fp p) * (ps.map fun p => 1 + fp p).prod := by ring
      _ ≤ (mulUp acc (SC + fUp p) : ℝ) * (ps.map fun p => 1 + fp p).prod :=
          mul_le_mul_of_nonneg_right hstep hprod
      _ ≤ _ := ih1

theorem foldl_lo : ∀ (ps : List ℕ) (acc : ℕ), (∀ p ∈ ps, 3 ≤ p) →
    ((ps.foldl (fun acc p => mulLo acc (SC + fLo p)) acc : ℕ) : ℝ) ≤ (acc : ℝ) * (ps.map fun p => 1 + fp p).prod ∧
      acc ≤ ps.foldl (fun acc p => mulLo acc (SC + fLo p)) acc
  | [], acc, _ => by simp
  | p :: ps, acc, h => by
    have hp := h p (by simp)
    have hps : ∀ q ∈ ps, 3 ≤ q := fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨ih1, ih2⟩ := foldl_lo ps (mulLo acc (SC + fLo p)) hps
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have hstep : (mulLo acc (SC + fLo p) : ℝ) ≤ (acc : ℝ) * (1 + fp p) := by
      have h1 := mulLo_le acc (SC + fLo p)
      have h2 := fLo_le p hp
      have hacc : (0 : ℝ) ≤ acc := Nat.cast_nonneg _
      push_cast at h1
      calc (mulLo acc (SC + fLo p) : ℝ) ≤ (acc : ℝ) * ((SC : ℝ) + (fLo p : ℝ)) / SC := h1
        _ ≤ (acc : ℝ) * ((SC : ℝ) + (SC : ℝ) * fp p) / SC := by
            apply div_le_div_of_nonneg_right _ SC_pos.le
            exact mul_le_mul_of_nonneg_left (by linarith) hacc
        _ = (acc : ℝ) * (1 + fp p) := by field_simp [SC_pos.ne']
    have hle : acc ≤ mulLo acc (SC + fLo p) := by
      unfold mulLo
      apply (Nat.le_div_iff_mul_le (by unfold SC; positivity)).mpr
      exact Nat.mul_le_mul_left _ (by omega)
    refine ⟨?_, le_trans hle ih2⟩
    have hprod := le_trans zero_le_one (prod_one_add_nonneg ps hps)
    calc _ ≤ (mulLo acc (SC + fLo p) : ℝ) * (ps.map fun p => 1 + fp p).prod := ih1
      _ ≤ (acc : ℝ) * (1 + fp p) * (ps.map fun p => 1 + fp p).prod := mul_le_mul_of_nonneg_right hstep hprod
      _ = _ := by ring

theorem eUp_ge (ps : List ℕ) (h : ∀ p ∈ ps, 3 ≤ p) : (SC : ℝ) * eG ps ≤ (eUp ps : ℝ) := by
  obtain ⟨h1, h2⟩ := foldl_up ps SC h
  unfold eUp eG
  rw [Nat.cast_sub h2]
  linarith

theorem eLo_le (ps : List ℕ) (h : ∀ p ∈ ps, 3 ≤ p) : (eLo ps : ℝ) ≤ (SC : ℝ) * eG ps := by
  obtain ⟨h1, h2⟩ := foldl_lo ps SC h
  unfold eLo eG
  rw [Nat.cast_sub h2]
  linarith

theorem piUp_ge_aux : ∀ (gs : List Grp) (acc : ℕ), (∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) →
    (acc : ℝ) * (gs.map fun g => 1 + eG g.ps).prod ≤ (gs.foldl (fun acc g => mulUp acc (SC + eUp g.ps)) acc : ℕ)
  | [], acc, _ => by simp
  | g :: gs, acc, h => by
    have hg := h g (by simp)
    have hgs : ∀ g' ∈ gs, ∀ p ∈ g'.ps, 3 ≤ p := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have ih := piUp_ge_aux gs (mulUp acc (SC + eUp g.ps)) hgs
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have hstep : (acc : ℝ) * (1 + eG g.ps) ≤ (mulUp acc (SC + eUp g.ps) : ℝ) := by
      have h1 := mulUp_ge acc (SC + eUp g.ps)
      have h2 := eUp_ge g.ps hg
      have hacc : (0 : ℝ) ≤ acc := Nat.cast_nonneg _
      push_cast at h1
      calc (acc : ℝ) * (1 + eG g.ps) = (acc : ℝ) * ((SC : ℝ) + (SC : ℝ) * eG g.ps) / SC := by
            field_simp [SC_pos.ne']
        _ ≤ (acc : ℝ) * ((SC : ℝ) + (eUp g.ps : ℝ)) / SC := by
            apply div_le_div_of_nonneg_right _ SC_pos.le
            exact mul_le_mul_of_nonneg_left (by linarith) hacc
        _ ≤ _ := h1
    have hprod : 0 ≤ (gs.map fun g => 1 + eG g.ps).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hx
      linarith [eG_nonneg g'.ps (hgs g' hg')]
    calc (acc : ℝ) * ((1 + eG g.ps) * (gs.map fun g => 1 + eG g.ps).prod)
        = (acc : ℝ) * (1 + eG g.ps) * (gs.map fun g => 1 + eG g.ps).prod := by ring
      _ ≤ (mulUp acc (SC + eUp g.ps) : ℝ) * (gs.map fun g => 1 + eG g.ps).prod :=
          mul_le_mul_of_nonneg_right hstep hprod
      _ ≤ _ := ih

theorem piUp_ge (gs : List Grp) (h : ∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) :
    (SC : ℝ) * Fs (flatG gs) (fun _ => 1) ≤ (piUp gs : ℝ) := by
  rw [Fs_one_flatG]
  exact piUp_ge_aux gs SC h

/-! ## Linear functionals on tables -/

/-- `Σ_{x ∈ tab} sel(x) H(x.L)`. -/
noncomputable def wS (sel : Ent → ℕ) (H : ℕ → ℝ) (tab : List Ent) : ℝ :=
  (tab.map fun x => (sel x : ℝ) * H x.L).sum

/-- The selectors used: additive under combining entries of equal key. -/
def SelAdd (sel : Ent → ℕ) : Prop := ∀ (x y : Ent), sel ⟨x.L, x.a + y.a, x.b + y.b⟩ = sel x + sel y

theorem selAdd_a : SelAdd Ent.a := fun _ _ => rfl
theorem selAdd_b : SelAdd Ent.b := fun _ _ => rfl

theorem wS_nil (sel : Ent → ℕ) (H : ℕ → ℝ) : wS sel H [] = 0 := by simp [wS]

theorem wS_cons (sel : Ent → ℕ) (H : ℕ → ℝ) (x : Ent) (tab : List Ent) :
    wS sel H (x :: tab) = (sel x : ℝ) * H x.L + wS sel H tab := by simp [wS]

theorem wS_append (sel : Ent → ℕ) (H : ℕ → ℝ) (t1 t2 : List Ent) :
    wS sel H (t1 ++ t2) = wS sel H t1 + wS sel H t2 := by simp [wS]

theorem wS_reverse (sel : Ent → ℕ) (H : ℕ → ℝ) (t : List Ent) : wS sel H t.reverse = wS sel H t := by
  simp [wS, List.map_reverse, List.sum_reverse]

theorem wS_mergeE (sel : Ent → ℕ) (hsel : SelAdd sel) (H : ℕ → ℝ) :
    ∀ (xs ys : List Ent), wS sel H (mergeE xs ys) = wS sel H xs + wS sel H ys
  | [], ys => by simp [mergeE, wS_nil]
  | x :: xs, ys => by
    simp only [mergeE]
    induction ys with
    | nil => simp [mergeE.mergeEIns, wS_cons, wS_mergeE sel hsel H xs [], wS_nil]
    | cons y ys ih =>
      unfold mergeE.mergeEIns
      split_ifs with h1 h2
      · simp only [wS_cons, wS_mergeE sel hsel H xs (y :: ys)]; ring
      · rw [wS_cons, ih]; simp only [wS_cons]; ring
      · have hL : x.L = y.L := by omega
        rw [wS_cons, wS_mergeE sel hsel H xs ys, wS_cons, wS_cons, hsel x y]
        push_cast
        rw [hL]; ring

theorem wS_mergePairsE (sel : Ent → ℕ) (hsel : SelAdd sel) (H : ℕ → ℝ) :
    ∀ (ls : List (List Ent)), ((mergePairsE ls).map (wS sel H)).sum = (ls.map (wS sel H)).sum
  | l1 :: l2 :: ls => by
    simp only [mergePairsE, List.map_cons, List.sum_cons, wS_mergeE sel hsel H, wS_mergePairsE sel hsel H ls]
    ring
  | [] => by simp [mergePairsE]
  | [l] => by simp [mergePairsE]

theorem wS_foldl_mergeE (sel : Ent → ℕ) (hsel : SelAdd sel) (H : ℕ → ℝ) :
    ∀ (ls : List (List Ent)) (acc : List Ent), wS sel H (ls.foldl mergeE acc) = wS sel H acc + (ls.map (wS sel H)).sum
  | [], acc => by simp
  | l :: ls, acc => by
    simp only [List.foldl_cons, wS_foldl_mergeE sel hsel H ls, wS_mergeE sel hsel H, List.map_cons, List.sum_cons]
    ring

theorem wS_mergeAllE (sel : Ent → ℕ) (hsel : SelAdd sel) (H : ℕ → ℝ) :
    ∀ (fuel : ℕ) (ls : List (List Ent)), wS sel H (mergeAllE fuel ls) = (ls.map (wS sel H)).sum
  | _, [] => by simp [mergeAllE, wS_nil]
  | _, [l] => by simp [mergeAllE]
  | 0, l1 :: l2 :: ls => by
    simp only [mergeAllE]
    rw [wS_foldl_mergeE sel hsel H, wS_nil, zero_add]
  | fuel + 1, l1 :: l2 :: ls => by
    simp only [mergeAllE]
    rw [wS_mergeAllE sel hsel H fuel, wS_mergePairsE sel hsel H]

theorem wS_runsAux (sel : Ent → ℕ) (H : ℕ → ℝ) :
    ∀ (l cur : List Ent) (last : ℕ), ((runsE.runsAux cur last l).map (wS sel H)).sum = wS sel H cur + wS sel H l
  | [], cur, last => by simp [runsE.runsAux, wS_reverse, wS_nil]
  | y :: ys, cur, last => by
    unfold runsE.runsAux
    split_ifs
    · rw [wS_runsAux sel H ys (y :: cur) y.L, wS_cons, wS_cons]; ring
    · simp only [List.map_cons, List.sum_cons]
      rw [wS_runsAux sel H ys [y] y.L, wS_reverse, wS_cons, wS_cons, wS_nil]; ring

theorem wS_sortE (sel : Ent → ℕ) (hsel : SelAdd sel) (H : ℕ → ℝ) (l : List Ent) :
    wS sel H (sortE l) = wS sel H l := by
  unfold sortE
  rw [wS_mergeAllE sel hsel H]
  cases l with
  | nil => simp [runsE, wS_nil]
  | cons x xs =>
    simp only [runsE]
    rw [wS_runsAux sel H xs [x] x.L, wS_cons, wS_cons, wS_nil]; ring

/-! ## One DP step -/

/-- `Hf ps ψ L = Fs ps (ψ ∘ lcm L)`. -/
noncomputable def Hf (ps : List (ℕ × ℕ)) (ψ : ℕ → ℝ) (L : ℕ) : ℝ := Fs ps (fun L' => ψ (Nat.lcm L L'))

/-- `ψ ≥ 0`, vanishing at `0` and above `LMAX`. -/
def Vanish (ψ : ℕ → ℝ) : Prop := (∀ L, 0 ≤ ψ L) ∧ ∀ L, (L = 0 ∨ LMAX < L) → ψ L = 0

theorem Hf_nonneg (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ) (hψ : ∀ L, 0 ≤ ψ L) (L : ℕ) :
    0 ≤ Hf ps ψ L := Fs_nonneg ps hps _ (fun _ => hψ _)

theorem Hf_big (ps : List (ℕ × ℕ)) (ψ : ℕ → ℝ) (hψ : Vanish ψ) (L : ℕ) (hL : LMAX < L) : Hf ps ψ L = 0 :=
  Fs_lcm_big ps ψ hψ.2 L hL

theorem Hf_group (g : Grp) (ps : List (ℕ × ℕ)) (ψ : ℕ → ℝ) (L : ℕ) :
    Hf (g.ps.map (fun p => (p, g.t)) ++ ps) ψ L = Hf ps ψ L + eG g.ps * Hf ps ψ (Nat.lcm L g.t) := by
  unfold Hf
  rw [Fs_group]
  congr 2
  exact Fs_congr ps _ _ (fun L' => by rw [Nat.lcm_assoc])

theorem pushE_cons_le (t ea eb : ℕ) (x : Ent) (tab : List Ent) (hle : Nat.lcm x.L t ≤ LMAX) :
    pushE t ea eb (x :: tab) = ⟨Nat.lcm x.L t, mulLo x.a ea, mulUp x.b eb⟩ :: pushE t ea eb tab := by
  simp [pushE, List.filterMap_cons, hle]

theorem pushE_cons_gt (t ea eb : ℕ) (x : Ent) (tab : List Ent) (hle : ¬ Nat.lcm x.L t ≤ LMAX) :
    pushE t ea eb (x :: tab) = pushE t ea eb tab := by
  simp [pushE, List.filterMap_cons, hle]

theorem push_up (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ) (hψ : Vanish ψ) (t ea eb : ℕ)
    (e : ℝ) (he : (SC : ℝ) * e ≤ eb) (he0 : 0 ≤ e) :
    ∀ (tab : List Ent), (tab.map fun x => (x.b : ℝ) * (e * Hf ps ψ (Nat.lcm x.L t))).sum ≤
      wS Ent.b (Hf ps ψ) (pushE t ea eb tab)
  | [] => by simp [pushE, wS_nil]
  | x :: tab => by
    have ih := push_up ps hps ψ hψ t ea eb e he he0 tab
    have hH := Hf_nonneg ps hps ψ hψ.1 (Nat.lcm x.L t)
    simp only [List.map_cons, List.sum_cons]
    by_cases hle : Nat.lcm x.L t ≤ LMAX
    · rw [pushE_cons_le t ea eb x tab hle, wS_cons]
      have hb : (x.b : ℝ) * e ≤ (mulUp x.b eb : ℝ) := by
        have h1 := mulUp_ge x.b eb
        have hx : (0 : ℝ) ≤ x.b := Nat.cast_nonneg _
        calc (x.b : ℝ) * e = (x.b : ℝ) * ((SC : ℝ) * e) / SC := by field_simp [SC_pos.ne']
          _ ≤ (x.b : ℝ) * eb / SC := by
              apply div_le_div_of_nonneg_right _ SC_pos.le
              exact mul_le_mul_of_nonneg_left he hx
          _ ≤ _ := h1
      have := mul_le_mul_of_nonneg_right hb hH
      simp only at this ⊢
      linarith
    · rw [pushE_cons_gt t ea eb x tab hle, Hf_big ps ψ hψ _ (by omega)]
      simpa using ih

theorem push_lo (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ) (hψ : Vanish ψ) (t ea eb : ℕ)
    (e : ℝ) (he : (ea : ℝ) ≤ (SC : ℝ) * e) :
    ∀ (tab : List Ent), wS Ent.a (Hf ps ψ) (pushE t ea eb tab) ≤
      (tab.map fun x => (x.a : ℝ) * (e * Hf ps ψ (Nat.lcm x.L t))).sum
  | [] => by simp [pushE, wS_nil]
  | x :: tab => by
    have ih := push_lo ps hps ψ hψ t ea eb e he tab
    have hH := Hf_nonneg ps hps ψ hψ.1 (Nat.lcm x.L t)
    have he0 : 0 ≤ e := by
      have : (0 : ℝ) ≤ ea := Nat.cast_nonneg _
      nlinarith [SC_pos]
    simp only [List.map_cons, List.sum_cons]
    by_cases hle : Nat.lcm x.L t ≤ LMAX
    · rw [pushE_cons_le t ea eb x tab hle, wS_cons]
      have ha : (mulLo x.a ea : ℝ) ≤ (x.a : ℝ) * e := by
        have h1 := mulLo_le x.a ea
        have hx : (0 : ℝ) ≤ x.a := Nat.cast_nonneg _
        calc (mulLo x.a ea : ℝ) ≤ (x.a : ℝ) * ea / SC := h1
          _ ≤ (x.a : ℝ) * ((SC : ℝ) * e) / SC := by
              apply div_le_div_of_nonneg_right _ SC_pos.le
              exact mul_le_mul_of_nonneg_left he hx
          _ = (x.a : ℝ) * e := by field_simp [SC_pos.ne']
      have := mul_le_mul_of_nonneg_right ha hH
      simp only at this ⊢
      linarith
    · rw [pushE_cons_gt t ea eb x tab hle]
      have hx : (0 : ℝ) ≤ (x.a : ℝ) * (e * Hf ps ψ (Nat.lcm x.L t)) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg he0 hH)
      linarith

theorem wS_group (sel : Ent → ℕ) (g : Grp) (ps : List (ℕ × ℕ)) (ψ : ℕ → ℝ) (tab : List Ent) :
    wS sel (Hf (g.ps.map (fun p => (p, g.t)) ++ ps) ψ) tab =
      wS sel (Hf ps ψ) tab + (tab.map fun x => (sel x : ℝ) * (eG g.ps * Hf ps ψ (Nat.lcm x.L g.t))).sum := by
  unfold wS
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [Hf_group]; ring

theorem step_up (g : Grp) (hg : ∀ p ∈ g.ps, 3 ≤ p) (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ)
    (hψ : Vanish ψ) (tab : List Ent) :
    wS Ent.b (Hf (g.ps.map (fun p => (p, g.t)) ++ ps) ψ) tab ≤ wS Ent.b (Hf ps ψ) (stepM tab g) := by
  rw [wS_group, stepM, wS_mergeE _ selAdd_b, wS_sortE _ selAdd_b]
  have := push_up ps hps ψ hψ g.t (eLo g.ps) (eUp g.ps) (eG g.ps) (eUp_ge g.ps hg) (eG_nonneg g.ps hg) tab
  linarith

theorem step_lo (g : Grp) (hg : ∀ p ∈ g.ps, 3 ≤ p) (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ)
    (hψ : Vanish ψ) (tab : List Ent) :
    wS Ent.a (Hf ps ψ) (stepM tab g) ≤ wS Ent.a (Hf (g.ps.map (fun p => (p, g.t)) ++ ps) ψ) tab := by
  rw [wS_group, stepM, wS_mergeE _ selAdd_a, wS_sortE _ selAdd_a]
  have := push_lo ps hps ψ hψ g.t (eLo g.ps) (eUp g.ps) (eG g.ps) (eLo_le g.ps hg) tab
  linarith

theorem flatG_three (gs : List Grp) (h : ∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) : ∀ x ∈ flatG gs, 3 ≤ x.1 := by
  intro x hx
  simp only [flatG, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨g, hg, p, hp, rfl⟩ := hx
  exact h g hg p hp

/-! ## Dropping entries of small weight -/

/-- `ψ L ≤ K / L` for `L ≥ 1`. -/
def Decay (ψ : ℕ → ℝ) (K : ℝ) : Prop := ∀ L, 1 ≤ L → ψ L ≤ K / (L : ℝ)

theorem wS_filter (sel : Ent → ℕ) (H : ℕ → ℝ) (p : Ent → Bool) :
    ∀ (tab : List Ent), wS sel H tab = wS sel H (tab.filter p) + wS sel H (tab.filter fun x => !p x)
  | [] => by simp [wS_nil]
  | x :: tab => by
    rw [wS_cons, wS_filter sel H p tab]
    cases hpx : p x <;> simp [List.filter_cons, hpx, wS_cons] <;> ring

theorem wS_filter_le (sel : Ent → ℕ) (H : ℕ → ℝ) (hH : ∀ L, 0 ≤ H L) (p : Ent → Bool) (tab : List Ent) :
    wS sel H (tab.filter p) ≤ wS sel H tab := by
  rw [wS_filter sel H p tab]
  have : 0 ≤ wS sel H (tab.filter fun x => !p x) :=
    List.sum_nonneg (fun y hy => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact mul_nonneg (Nat.cast_nonneg _) (hH _))
  linarith

theorem Fs_one_nonneg (xs : List (ℕ × ℕ)) (h : ∀ x ∈ xs, 3 ≤ x.1) : 0 ≤ Fs xs (fun _ => 1) :=
  Fs_nonneg xs h _ (fun _ => zero_le_one)

theorem Hf_decay (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ) (hψ : Vanish ψ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : Decay ψ K) (L : ℕ) (hL : 1 ≤ L) : Hf ps ψ L ≤ K / (L : ℝ) * Fs ps (fun _ => 1) := by
  unfold Hf
  rw [← Fs_smul]
  apply Fs_mono ps hps
  intro L'
  have hKL : 0 ≤ K / (L : ℝ) := div_nonneg hK0 (Nat.cast_nonneg _)
  by_cases h0 : L' = 0
  · rw [h0, Nat.lcm_zero_right, hψ.2 0 (Or.inl rfl)]; linarith
  · have hpos : 0 < Nat.lcm L L' := Nat.lcm_pos (by omega) (Nat.pos_of_ne_zero h0)
    have hle : (L : ℝ) ≤ (Nat.lcm L L' : ℝ) := by exact_mod_cast Nat.le_of_dvd hpos (Nat.dvd_lcm_left L L')
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    calc ψ (Nat.lcm L L') ≤ K / (Nat.lcm L L' : ℝ) := hK _ hpos
      _ ≤ K / (L : ℝ) := div_le_div_of_nonneg_left hK0 hLpos hle
      _ = K / (L : ℝ) * 1 := by ring

theorem wS_drop_le (H : ℕ → ℝ) (C : ℝ) :
    ∀ (l : List Ent), (∀ x ∈ l, (x.b : ℝ) * H x.L ≤ C * (cdiv x.b x.L : ℝ)) →
      wS Ent.b H l ≤ C * ((l.map fun x => cdiv x.b x.L).sum : ℕ)
  | [], _ => by simp [wS_nil]
  | x :: l, h => by
    rw [wS_cons]
    have h1 := h x (by simp)
    have h2 := wS_drop_le H C l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons]
    push_cast at h2 ⊢
    linarith

theorem keep_up (ps : List (ℕ × ℕ)) (hps : ∀ x ∈ ps, 3 ≤ x.1) (ψ : ℕ → ℝ) (hψ : Vanish ψ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : Decay ψ K) (m : List Ent) :
    wS Ent.b (Hf ps ψ) m ≤ wS Ent.b (Hf ps ψ) (keepE m) + K * Fs ps (fun _ => 1) * (dropM m : ℝ) := by
  have hF := Fs_one_nonneg ps hps
  rw [wS_filter Ent.b (Hf ps ψ) (fun x => decide (KAPPA * x.L ≤ x.b)) m]
  unfold keepE dropM
  have := wS_drop_le (Hf ps ψ) (K * Fs ps (fun _ => 1)) (m.filter fun x => !decide (KAPPA * x.L ≤ x.b)) (by
    intro x _
    rcases Nat.eq_zero_or_pos x.L with h0 | hpos
    · have : Hf ps ψ x.L = 0 := by
        unfold Hf; rw [h0]
        rw [Fs_congr ps _ (fun _ => 0) (fun L' => by rw [Nat.lcm_zero_left]; exact hψ.2 0 (Or.inl rfl)), Fs_zero]
      rw [this, mul_zero]
      exact mul_nonneg (mul_nonneg hK0 hF) (Nat.cast_nonneg _)
    · have h1 := Hf_decay ps hps ψ hψ K hK0 hK x.L hpos
      have h2 := cdiv_ge x.b x.L hpos
      unfold cdiv
      have hb : (0 : ℝ) ≤ x.b := Nat.cast_nonneg _
      calc (x.b : ℝ) * Hf ps ψ x.L ≤ (x.b : ℝ) * (K / (x.L : ℝ) * Fs ps (fun _ => 1)) :=
            mul_le_mul_of_nonneg_left h1 hb
        _ = K * Fs ps (fun _ => 1) * ((x.b : ℝ) / (x.L : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 hF))
  linarith

theorem Fs_one_group_ge (g : Grp) (hg : ∀ p ∈ g.ps, 3 ≤ p) (rest : List (ℕ × ℕ)) (hr : ∀ x ∈ rest, 3 ≤ x.1) :
    Fs rest (fun _ => 1) ≤ Fs (g.ps.map (fun p => (p, g.t)) ++ rest) (fun _ => 1) := by
  rw [Fs_group]
  have := eG_nonneg g.ps hg
  have := Fs_one_nonneg rest hr
  have : Fs rest (fun L => (fun _ => (1 : ℝ)) (Nat.lcm g.t L)) = Fs rest (fun _ => 1) := rfl
  nlinarith

theorem runDP_up : ∀ (gs : List Grp), (∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) → ∀ (ps : List (ℕ × ℕ)), (∀ x ∈ ps, 3 ≤ x.1) →
    ∀ (ψ : ℕ → ℝ), Vanish ψ → ∀ (K : ℝ), 0 ≤ K → Decay ψ K → ∀ (C : ℝ), Fs (flatG gs ++ ps) (fun _ => 1) ≤ C →
    ∀ (tab : List Ent),
      wS Ent.b (Hf (flatG gs ++ ps) ψ) tab ≤ wS Ent.b (Hf ps ψ) (runDP tab gs) + K * C * (runDrop tab gs : ℝ)
  | [], _, ps, _, ψ, _, K, _, _, C, _, tab => by simp [flatG, runDP, runDrop]
  | g :: gs, h, ps, hps, ψ, hψ, K, hK0, hK, C, hC, tab => by
    have hg := h g (by simp)
    have hgs : ∀ g' ∈ gs, ∀ p ∈ g'.ps, 3 ≤ p := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have hrest : ∀ x ∈ flatG gs ++ ps, 3 ≤ x.1 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact flatG_three gs hgs x hx
      · exact hps x hx
    rw [flatG_cons, List.append_assoc] at hC ⊢
    have hC' : Fs (flatG gs ++ ps) (fun _ => 1) ≤ C := le_trans (Fs_one_group_ge g hg _ hrest) hC
    have h1 := step_up g hg _ hrest ψ hψ tab
    have h2 := keep_up _ hrest ψ hψ K hK0 hK (stepM tab g)
    have h3 := runDP_up gs hgs ps hps ψ hψ K hK0 hK C hC' (stepE tab g)
    have h4 : K * Fs (flatG gs ++ ps) (fun _ => 1) * (dropM (stepM tab g) : ℝ) ≤ K * C * (dropM (stepM tab g) : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC' hK0) (Nat.cast_nonneg _)
    simp only [runDP, runDrop]
    simp only [stepE] at h3 ⊢
    push_cast
    linarith

theorem runDP_lo : ∀ (gs : List Grp), (∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) → ∀ (ps : List (ℕ × ℕ)), (∀ x ∈ ps, 3 ≤ x.1) →
    ∀ (ψ : ℕ → ℝ), Vanish ψ → ∀ (tab : List Ent),
      wS Ent.a (Hf ps ψ) (runDP tab gs) ≤ wS Ent.a (Hf (flatG gs ++ ps) ψ) tab
  | [], _, ps, _, ψ, _, tab => by simp [flatG, runDP]
  | g :: gs, h, ps, hps, ψ, hψ, tab => by
    have hg := h g (by simp)
    have hgs : ∀ g' ∈ gs, ∀ p ∈ g'.ps, 3 ≤ p := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have hrest : ∀ x ∈ flatG gs ++ ps, 3 ≤ x.1 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact flatG_three gs hgs x hx
      · exact hps x hx
    rw [flatG_cons, List.append_assoc, runDP]
    have hkeep : wS Ent.a (Hf (flatG gs ++ ps) ψ) (stepE tab g) ≤ wS Ent.a (Hf (flatG gs ++ ps) ψ) (stepM tab g) :=
      wS_filter_le _ _ (Hf_nonneg _ hrest ψ hψ.1) _ _
    exact le_trans (runDP_lo gs hgs ps hps ψ hψ (stepE tab g)) (le_trans hkeep (step_lo g hg _ hrest ψ hψ tab))

theorem runDPD_eq : ∀ (gs : List Grp) (tab : List Ent) (d : ℕ), runDPD tab d gs = (runDP tab gs, d + runDrop tab gs)
  | [], tab, d => by simp [runDPD, runDP, runDrop]
  | g :: gs, tab, d => by
    simp only [runDPD, runDP, runDrop]
    rw [runDPD_eq gs]
    simp only [stepE, Prod.mk.injEq, true_and]
    ring

theorem runDP_append : ∀ (gs1 gs2 : List Grp) (tab : List Ent), runDP tab (gs1 ++ gs2) = runDP (runDP tab gs1) gs2
  | [], gs2, tab => rfl
  | g :: gs1, gs2, tab => by simp only [List.cons_append, runDP]; exact runDP_append gs1 gs2 (stepE tab g)

theorem flatG_append (gs1 gs2 : List Grp) : flatG (gs1 ++ gs2) = flatG gs1 ++ flatG gs2 := by
  simp [flatG]

/-! ## The bounds from the final tables -/

/-- `χ = [1 ≤ L ≤ LMAX]`. -/
noncomputable def chi (L : ℕ) : ℝ := if 1 ≤ L ∧ L ≤ LMAX then 1 else 0

theorem chi_nonneg (L : ℕ) : 0 ≤ chi L := by unfold chi; split_ifs <;> norm_num
theorem chi_le_one (L : ℕ) : chi L ≤ 1 := by unfold chi; split_ifs <;> norm_num

theorem vanish_mul_chi (φ : ℕ → ℝ) (hφ : ∀ L, 0 ≤ φ L) : Vanish (fun L => φ L * chi L) := by
  refine ⟨fun L => mul_nonneg (hφ L) (chi_nonneg L), fun L hL => ?_⟩
  have : chi L = 0 := by unfold chi; rw [if_neg]; omega
  simp [this]

theorem wS_Hf_nil (sel : Ent → ℕ) (ψ : ℕ → ℝ) (tab : List Ent) :
    wS sel (Hf [] ψ) tab = wS sel ψ tab := by
  unfold wS Hf
  congr 1
  apply List.map_congr_left
  intro x _
  simp [Fs]

theorem wS_tab0 (sel : Ent → ℕ) (hs : sel ⟨1, SC, SC⟩ = SC) (ps : List (ℕ × ℕ)) (ψ : ℕ → ℝ) :
    wS sel (Hf ps ψ) tab0 = (SC : ℝ) * Fs ps ψ := by
  simp [wS, tab0, Hf, hs]

/-- The upper bound for `Fs (flatG gs) φ` from the final table (pruned mass, dropped mass). -/
theorem T_bound (gs : List Grp) (hgs : ∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) (φ : ℕ → ℝ) (hφ0 : ∀ L, 0 ≤ φ L) (B : ℝ)
    (hB : ∀ L, (L = 0 ∨ LMAX < L) → φ L ≤ B) (K : ℝ) (hK0 : 0 ≤ K) (hK : Decay φ K) :
    (SC : ℝ) * Fs (flatG gs) φ ≤
      wS Ent.b (fun L => φ L * chi L) (runDP tab0 gs) + K * ((piUp gs : ℝ) / SC) * (runDrop tab0 gs : ℝ) +
        B * ((piUp gs : ℝ) - wS Ent.a chi (runDP tab0 gs)) := by
  have h3 := flatG_three gs hgs
  have hB0 : 0 ≤ B := le_trans (hφ0 0) (hB 0 (Or.inl rfl))
  -- split φ = φ χ + φ (1 - χ)
  have hsplit : Fs (flatG gs) φ = Fs (flatG gs) (fun L => φ L * chi L) + Fs (flatG gs) (fun L => φ L * (1 - chi L)) := by
    rw [← Fs_add]; congr 1; funext L; ring
  have hpi := piUp_ge gs hgs
  have hC : Fs (flatG gs ++ []) (fun _ => 1) ≤ (piUp gs : ℝ) / SC := by
    rw [List.append_nil, le_div_iff₀ SC_pos]; linarith
  have hdec : Decay (fun L => φ L * chi L) K := by
    intro L hL
    have := hK L hL
    have := chi_le_one L
    have := chi_nonneg L
    have := hφ0 L
    nlinarith
  have hup := runDP_up gs hgs [] (by simp) _ (vanish_mul_chi φ hφ0) K hK0 hdec _ hC tab0
  rw [List.append_nil, wS_tab0 _ rfl, wS_Hf_nil] at hup
  have hlo := runDP_lo gs hgs [] (by simp) chi (by simpa using vanish_mul_chi (fun _ => 1) (fun _ => zero_le_one)) tab0
  rw [List.append_nil, wS_tab0 _ rfl, wS_Hf_nil] at hlo
  have hrest : Fs (flatG gs) (fun L => φ L * (1 - chi L)) ≤ B * (Fs (flatG gs) (fun _ => 1) - Fs (flatG gs) chi) := by
    rw [← Fs_sub, ← Fs_smul]
    apply Fs_mono _ h3
    intro L
    unfold chi
    split_ifs with hL
    · simp
    · have : L = 0 ∨ LMAX < L := by omega
      have := hB L this
      simp; linarith
  rw [hsplit, mul_add]
  have : (SC : ℝ) * Fs (flatG gs) (fun L => φ L * (1 - chi L)) ≤
      B * ((piUp gs : ℝ) - wS Ent.a chi (runDP tab0 gs)) := by
    calc (SC : ℝ) * Fs (flatG gs) (fun L => φ L * (1 - chi L))
        ≤ (SC : ℝ) * (B * (Fs (flatG gs) (fun _ => 1) - Fs (flatG gs) chi)) :=
          mul_le_mul_of_nonneg_left hrest SC_pos.le
      _ = B * ((SC : ℝ) * Fs (flatG gs) (fun _ => 1) - (SC : ℝ) * Fs (flatG gs) chi) := by ring
      _ ≤ B * ((piUp gs : ℝ) - wS Ent.a chi (runDP tab0 gs)) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          have hlo' : wS Ent.a chi (runDP tab0 gs) ≤ (SC : ℝ) * Fs (flatG gs) chi := by
            simpa using hlo
          linarith
  linarith

/-- The lower bound for `Fs (flatG gs) ψ` from the final table. -/
theorem lo_bound (gs : List Grp) (hgs : ∀ g ∈ gs, ∀ p ∈ g.ps, 3 ≤ p) (ψ : ℕ → ℝ) (hψ0 : ∀ L, 0 ≤ ψ L) :
    wS Ent.a (fun L => ψ L * chi L) (runDP tab0 gs) ≤ (SC : ℝ) * Fs (flatG gs) ψ := by
  have h3 := flatG_three gs hgs
  have hlo := runDP_lo gs hgs [] (by simp) _ (vanish_mul_chi ψ hψ0) tab0
  rw [List.append_nil, wS_tab0 _ rfl, wS_Hf_nil] at hlo
  refine le_trans hlo (mul_le_mul_of_nonneg_left (Fs_mono _ h3 _ _ fun L => ?_) SC_pos.le)
  have := chi_le_one L
  have := hψ0 L
  nlinarith

end Romanoff.M3
