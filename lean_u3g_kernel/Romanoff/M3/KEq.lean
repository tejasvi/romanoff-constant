import Romanoff.M3.Sound
import RCert.M3.KFun

/-!
# M3, K version: the kernel functions equal the checker functions
-/

namespace Romanoff.M3

open R45.M3

theorem cond_blt (a b : ℕ) {α : Type*} (x y : α) : cond (Nat.blt a b) x y = if a < b then x else y := by
  by_cases h : a < b
  · rw [if_pos h, show Nat.blt a b = true from Nat.blt_eq.mpr h]; rfl
  · rw [if_neg h, show Nat.blt a b = false from Bool.eq_false_iff.mpr (fun h' => h (Nat.blt_eq.mp h'))]; rfl

theorem cond_ble (a b : ℕ) {α : Type*} (x y : α) : cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · rw [if_pos h, show Nat.ble a b = true from Nat.ble_eq.mpr h]; rfl
  · rw [if_neg h, show Nat.ble a b = false from Bool.eq_false_iff.mpr (fun h' => h (Nat.ble_eq.mp h'))]; rfl

theorem entsEqK_eq : ∀ (xs ys : List Ent), entsEqK xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [entsEqK] at h
  | _ :: _, [], h => by simp [entsEqK] at h
  | x :: xs, y :: ys, h => by
    simp only [entsEqK, Bool.and_eq_true, Nat.beq_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hxy : x = y := by cases x; cases y; simp_all
    rw [hxy, entsEqK_eq xs ys h4]

theorem mergeK_eq : ∀ (xs ys : List Ent), mergeK xs ys = mergeE xs ys
  | [], ys => by simp [mergeK, mergeE]
  | x :: xs, ys => by
    induction ys with
    | nil => simp only [mergeK, mergeE, mergeE.mergeEIns]; rw [← mergeK_eq xs []]; rfl
    | cons y ys ih =>
      show (cond (Nat.blt x.L y.L) (x :: mergeK xs (y :: ys))
        (cond (Nat.blt y.L x.L) (y :: mergeK (x :: xs) ys) (⟨x.L, x.a + y.a, x.b + y.b⟩ :: mergeK xs ys))) = _
      rw [ih, mergeK_eq xs (y :: ys), mergeK_eq xs ys, cond_blt, cond_blt]
      simp only [mergeE, mergeE.mergeEIns]

/-- The helper of `mergePairsK`. -/
noncomputable def mpAux (ls : List (List Ent)) : Option (List Ent) → List (List Ent) :=
  List.rec (motive := fun _ => Option (List Ent) → List (List Ent))
    (fun o => Option.rec [] (fun l => [l]) o)
    (fun l _ ih o => Option.rec (ih (some l)) (fun l0 => mergeK l0 l :: ih none) o) ls

theorem mpAux_eq : ∀ (ls : List (List Ent)),
    mpAux ls none = mergePairsE ls ∧ ∀ l0, mpAux ls (some l0) = mergePairsE (l0 :: ls)
  | [] => ⟨rfl, fun _ => rfl⟩
  | l :: ls => by
    obtain ⟨h1, h2⟩ := mpAux_eq ls
    refine ⟨?_, fun l0 => ?_⟩
    · show mpAux ls (some l) = _
      rw [h2]
    · show mergeK l0 l :: mpAux ls none = _
      rw [h1, mergeK_eq]
      rfl

theorem mergePairsK_eq (ls : List (List Ent)) : mergePairsK ls = mergePairsE ls := (mpAux_eq ls).1

theorem foldl_mergeK (ls : List (List Ent)) : ∀ (acc : List Ent),
    (List.rec (motive := fun _ => List Ent → List Ent) (fun acc => acc) (fun l _ ih acc => ih (mergeK acc l)) ls) acc =
      ls.foldl mergeE acc := by
  induction ls with
  | nil => intro acc; rfl
  | cons l ls ih => intro acc; show _ = ls.foldl mergeE (mergeE acc l); rw [← mergeK_eq]; exact ih _

theorem mergeAllK_eq : ∀ (fuel : ℕ) (ls : List (List Ent)), mergeAllK fuel ls = mergeAllE fuel ls
  | 0, [] => rfl
  | 0, [l] => by show mergeK [] l = l; rw [mergeK_eq]; rfl
  | 0, l1 :: l2 :: ls => by
    have h := foldl_mergeK (l1 :: l2 :: ls) []
    exact h.trans (by simp [mergeAllE])
  | fuel + 1, [] => rfl
  | fuel + 1, [l] => rfl
  | fuel + 1, l1 :: l2 :: ls => by
    show mergeAllK fuel (mergePairsK (l1 :: l2 :: ls)) = mergeAllE fuel (mergePairsE (l1 :: l2 :: ls))
    rw [mergePairsK_eq, mergeAllK_eq fuel]

/-- The helper of `runsK`. -/
noncomputable def runsAuxK (l : List Ent) : List Ent → ℕ → List (List Ent) :=
  List.rec (motive := fun _ => List Ent → ℕ → List (List Ent))
    (fun cur _ => List.rec (motive := fun _ => List (List Ent)) [] (fun _ _ _ => [cur.reverse]) cur)
    (fun y _ ih cur last => List.rec (motive := fun _ => List (List Ent)) (ih [y] y.L)
      (fun _ _ _ => cond (Nat.blt last y.L) (ih (y :: cur) y.L) (cur.reverse :: ih [y] y.L)) cur) l

theorem runsAuxK_eq : ∀ (l : List Ent) (c : Ent) (cs : List Ent) (last : ℕ),
    runsAuxK l (c :: cs) last = runsE.runsAux (c :: cs) last l
  | [], c, cs, last => rfl
  | y :: ys, c, cs, last => by
    show cond (Nat.blt last y.L) (runsAuxK ys (y :: c :: cs) y.L) ((c :: cs).reverse :: runsAuxK ys [y] y.L) = _
    rw [runsAuxK_eq ys y (c :: cs), runsAuxK_eq ys y [], cond_blt]
    simp only [runsE.runsAux]

theorem runsK_eq (l : List Ent) : runsK l = runsE l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    show runsAuxK xs [x] x.L = _
    rw [runsAuxK_eq]; rfl

theorem sortK_eq (l : List Ent) : sortK l = sortE l := by
  unfold sortK sortE; rw [runsK_eq, mergeAllK_eq]

theorem pushK_eq (t ea eb : ℕ) : ∀ (tab : List Ent), pushK t ea eb tab = pushE t ea eb tab
  | [] => rfl
  | x :: tab => by
    show cond (Nat.ble (Nat.lcm x.L t) LMAX) (⟨Nat.lcm x.L t, mulLo x.a ea, mulUp x.b eb⟩ :: pushK t ea eb tab)
      (pushK t ea eb tab) = _
    rw [cond_ble, pushK_eq t ea eb tab]
    split_ifs with h
    · rw [pushE_cons_le t ea eb x tab h]
    · rw [pushE_cons_gt t ea eb x tab h]

theorem keepK_eq : ∀ (tab : List Ent), keepK tab = keepE tab
  | [] => rfl
  | x :: tab => by
    show cond (Nat.ble (KAPPA * x.L) x.b) (x :: keepK tab) (keepK tab) = _
    rw [cond_ble, keepK_eq tab]
    unfold keepE
    split_ifs with h <;> simp [List.filter_cons, h]

theorem dropMK_eq : ∀ (tab : List Ent), dropMK tab = dropM tab
  | [] => rfl
  | x :: tab => by
    show cond (Nat.ble (KAPPA * x.L) x.b) (dropMK tab) (cdiv x.b x.L + dropMK tab) = _
    rw [cond_ble, dropMK_eq tab]
    unfold dropM
    split_ifs with h <;> simp [List.filter_cons, h]

theorem stepMK_eq (tab : List Ent) (g : Grp) : stepMK tab g = stepM tab g := by
  unfold stepMK stepM; rw [pushK_eq, sortK_eq, mergeK_eq]

theorem runDPK_eq : ∀ (gs : List Grp) (tab : List Ent), runDPK tab gs = runDP tab gs
  | [], tab => rfl
  | g :: gs, tab => by
    show runDPK (keepK (stepMK tab g)) gs = _
    rw [runDPK_eq gs, keepK_eq, stepMK_eq]; rfl

theorem runDPDK_eq : ∀ (gs : List Grp) (tab : List Ent) (d : ℕ), runDPDK tab d gs = runDPD tab d gs
  | [], tab, d => rfl
  | g :: gs, tab, d => by
    show runDPDK (keepK (stepMK tab g)) (d + dropMK (stepMK tab g)) gs = _
    rw [runDPDK_eq gs, keepK_eq, dropMK_eq, stepMK_eq]; rfl

theorem segOK_sound (tab : List Ent) (da : ℕ) (gs : List Grp) (lb : List ℕ) (db : ℕ)
    (h : segOK tab da gs lb db = true) : runDPD tab da gs = (decTabK lb, db) := by
  unfold segOK at h
  simp only [Bool.and_eq_true] at h
  rw [← runDPDK_eq]
  exact Prod.ext (entsEqK_eq _ _ h.1) (Nat.eq_of_beq_eq_true h.2)

theorem segROK_sound (tab : List Ent) (gs : List Grp) (lb : List ℕ) (h : segROK tab gs lb = true) :
    runDP tab gs = decTabK lb := by
  rw [← runDPK_eq]; exact entsEqK_eq _ _ h

theorem cond_chi (L : ℕ) {α : Type*} (x y : α) :
    cond (Nat.ble 1 L && Nat.ble L LMAX) x y = if 1 ≤ L ∧ L ≤ LMAX then x else y := by
  have e1 : Nat.ble 1 L = decide (1 ≤ L) := by
    by_cases h : 1 ≤ L
    · rw [decide_eq_true h]; exact Nat.ble_eq.mpr h
    · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr (fun h' => h (Nat.ble_eq.mp h'))
  have e2 : Nat.ble L LMAX = decide (L ≤ LMAX) := by
    by_cases h : L ≤ LMAX
    · rw [decide_eq_true h]; exact Nat.ble_eq.mpr h
    · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr (fun h' => h (Nat.ble_eq.mp h'))
  rw [e1, e2]
  by_cases h1 : 1 ≤ L <;> by_cases h2 : L ≤ LMAX <;> simp [h1, h2]

theorem sumRK_eq (u : ℕ) (tab : List Ent) : sumRK u tab = sumR u tab := by
  unfold sumRK sumR
  generalize 0 = acc
  induction tab generalizing acc with
  | nil => rfl
  | cons x tab ih => simp only [List.foldl_cons]; rw [← ih, cond_chi]

theorem sumAK_eq (tab : List Ent) : sumAK tab = sumA tab := by
  unfold sumAK sumA
  generalize 0 = acc
  induction tab generalizing acc with
  | nil => rfl
  | cons x tab ih => simp only [List.foldl_cons]; rw [← ih, cond_chi]

theorem sumBK_eq (tab : List Ent) : sumBK tab = sumB tab := by
  unfold sumBK sumB
  generalize 0 = acc
  induction tab generalizing acc with
  | nil => rfl
  | cons x tab ih => simp only [List.foldl_cons]; rw [← ih, cond_chi]

end Romanoff.M3
