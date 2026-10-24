import Romanoff.M3.KEq

/-!
# M3, K version: `accG` from subtables by `gcd(L, 120)`

`accG s tab = div120.map (bsum s · tab)` (bucket sums); the buckets split over the subtables `gcd(L, 120) = h`, and on a
subtable whose entries all have `gcd(lcm(L, s), 120) = G` (checked by `passK`) only the bucket `G` is nonzero.
-/

namespace Romanoff.M3

open R45.M3

/-- The value and the bucket of an entry in `accG s`. -/
def vS (s : ℕ) (x : Ent) : ℕ := (x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s
def gS (s : ℕ) (x : Ent) : ℕ := Nat.gcd (Nat.lcm x.L s) PER
def chiB (x : Ent) : Bool := decide (1 ≤ x.L ∧ x.L ≤ LMAX)

/-- The bucket sum. -/
def bsum (s d : ℕ) (tab : List Ent) : ℕ := ((tab.filter fun x => chiB x && gS s x == d).map (vS s)).sum

theorem div120_nodup : div120.Nodup := by decide

theorem gS_mem (s : ℕ) (x : Ent) : gS s x ∈ div120 := mem_div120 _ (Nat.gcd_dvd_right _ _)

theorem addAt_map (g v : ℕ) (F : ℕ → ℕ) : ∀ (ds : List ℕ), ds.Nodup →
    addAt g v ds (ds.map F) = ds.map (fun d => F d + if d = g then v else 0)
  | [], _ => rfl
  | d :: ds, hnd => by
    have hd : d ∉ ds := (List.nodup_cons.mp hnd).1
    simp only [List.map_cons, addAt]
    by_cases h : d = g
    · rw [if_pos h, if_pos h, List.cons.injEq]
      refine ⟨rfl, ?_⟩
      apply List.map_congr_left
      intro d' hd'
      have : ¬ d' = g := fun e => hd (h ▸ e ▸ hd')
      rw [if_neg this, add_zero]
    · rw [if_neg h, if_neg h, add_zero, addAt_map g v F ds (List.nodup_cons.mp hnd).2]

theorem accG_bucket (s : ℕ) : ∀ (tab : List Ent) (F : ℕ → ℕ),
    tab.foldl (fun acc x =>
      if 1 ≤ x.L ∧ x.L ≤ LMAX then
        addAt (Nat.gcd (Nat.lcm x.L s) PER) ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s)
          div120 acc
      else acc) (div120.map F) = div120.map (fun d => F d + bsum s d tab)
  | [], F => by simp [bsum]
  | x :: tab, F => by
    simp only [List.foldl_cons]
    split_ifs with hx
    · rw [addAt_map _ _ F div120 div120_nodup, accG_bucket s tab]
      apply List.map_congr_left
      intro d _
      have hchi : chiB x = true := by simp [chiB, hx]
      by_cases hd : gS s x = d
      · have hp : (chiB x && gS s x == d) = true := by simp [hchi, hd]
        simp only [bsum, List.filter_cons, hp, if_true, List.map_cons, List.sum_cons]
        rw [if_pos (show d = Nat.gcd (Nat.lcm x.L s) PER from hd.symm)]
        simp only [vS]; ring
      · have hp : (chiB x && gS s x == d) = false := by simp [hchi, hd]
        simp only [bsum, List.filter_cons, hp, Bool.false_eq_true, if_false]
        rw [if_neg (show ¬ d = Nat.gcd (Nat.lcm x.L s) PER from fun e => hd (by simp only [gS]; exact e.symm))]
        ring
    · rw [accG_bucket s tab]
      apply List.map_congr_left
      intro d _
      simp [bsum, List.filter_cons, chiB, hx]

theorem accG_eq_bucket (s : ℕ) (tab : List Ent) : accG s tab = div120.map (fun d => bsum s d tab) := by
  unfold accG
  have h := accG_bucket s tab (fun _ => 0)
  simp only [zero_add] at h
  rw [← h]
  rfl

end Romanoff.M3

namespace Romanoff.M3

open R45.M3

/-- The key of the subtables. -/
def keyH (x : Ent) : ℕ := Nat.gcd x.L PER

theorem keyH_mem (x : Ent) : keyH x ∈ div120 := mem_div120 _ (Nat.gcd_dvd_right _ _)

theorem sum_ite_eq_mem (a c : ℕ) : ∀ (ks : List ℕ), ks.Nodup → a ∈ ks → (ks.map fun h => if a = h then c else 0).sum = c
  | [], _, h => by simp at h
  | k :: ks, hnd, h => by
    simp only [List.map_cons, List.sum_cons]
    by_cases hk : a = k
    · subst hk
      have : (ks.map fun h => if a = h then c else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hy
        have : a ≠ h' := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hh')
        simp [this]
      simp [this]
    · rw [if_neg hk, zero_add]
      exact sum_ite_eq_mem a c ks (List.nodup_cons.mp hnd).2 (by simpa [hk] using h)

theorem sum_partition (f : Ent → ℕ) (k : Ent → ℕ) (ks : List ℕ) (hnd : ks.Nodup) :
    ∀ (l : List Ent), (∀ x ∈ l, k x ∈ ks) →
      (l.map f).sum = (ks.map fun h => ((l.filter fun x => k x == h).map f).sum).sum
  | [], _ => by simp
  | x :: l, hl => by
    have ih := sum_partition f k ks hnd l (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rw [ih]
    have : (ks.map fun h => ((if (k x == h) = true then x :: l.filter (fun x => k x == h) else
        l.filter (fun x => k x == h)).map f).sum) =
        (ks.map fun h => (if k x = h then f x else 0) + ((l.filter fun x => k x == h).map f).sum) := by
      apply List.map_congr_left
      intro h _
      by_cases hh : k x = h <;> simp [hh]
    rw [this, List.sum_map_add, sum_ite_eq_mem (k x) (f x) ks hnd (hl x (by simp))]

theorem bsum_split (s d : ℕ) (tab : List Ent) :
    bsum s d tab = (div120.map fun h => bsum s d (tab.filter fun x => keyH x == h)).sum := by
  unfold bsum
  rw [sum_partition (vS s) keyH div120 div120_nodup _ (fun x _ => keyH_mem x)]
  congr 1
  apply List.map_congr_left
  intro h _
  rw [List.filter_filter, List.filter_filter]
  rw [List.filter_congr (fun x _ => Bool.and_comm (keyH x == h) (chiB x && gS s x == d))]

/-- The helper of `passK`. -/
noncomputable def passAux (s G : ℕ) (tab : List Ent) : ℕ → Bool → ℕ × Bool :=
  List.rec (motive := fun _ => ℕ → Bool → ℕ × Bool) (fun acc ok => (acc, ok))
    (fun x _ ih acc ok => cond (Nat.ble 1 x.L && Nat.ble x.L LMAX)
      (cond (Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G)
        (ih (acc + (x.b * G + Nat.lcm x.L s - 1) / Nat.lcm x.L s) ok) (ih acc false))
      (ih acc ok)) tab

theorem passAux_ok (s G : ℕ) : ∀ (tab : List Ent) (acc : ℕ) (ok : Bool), (passAux s G tab acc ok).2 = true →
    ok = true ∧ ∀ x ∈ tab, chiB x = true → gS s x = G
  | [], acc, ok, h => ⟨h, fun x hx => by simp at hx⟩
  | x :: tab, acc, ok, h => by
    change (cond (Nat.ble 1 x.L && Nat.ble x.L LMAX) (cond (Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G)
      (passAux s G tab (acc + (x.b * G + Nat.lcm x.L s - 1) / Nat.lcm x.L s) ok) (passAux s G tab acc false))
      (passAux s G tab acc ok)).2 = true at h
    rw [cond_chi] at h
    split_ifs at h with hx
    · by_cases hg : Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G = true
      · rw [hg] at h
        obtain ⟨h1, h2⟩ := passAux_ok s G tab _ ok h
        refine ⟨h1, fun y hy hcy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.eq_of_beq_eq_true hg
        · exact h2 y hy hcy
      · rw [Bool.eq_false_iff.mpr hg] at h
        exact absurd (passAux_ok s G tab _ false h).1 (by simp)
    · obtain ⟨h1, h2⟩ := passAux_ok s G tab acc ok h
      refine ⟨h1, fun y hy hcy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd (by simpa [chiB] using hcy) hx
      · exact h2 y hy hcy

theorem passAux_sum (s G : ℕ) : ∀ (tab : List Ent) (acc : ℕ) (ok : Bool),
    (∀ x ∈ tab, chiB x = true → gS s x = G) → (passAux s G tab acc ok).1 = acc + bsum s G tab
  | [], acc, ok, _ => by simp [passAux, bsum]
  | x :: tab, acc, ok, h => by
    change (cond (Nat.ble 1 x.L && Nat.ble x.L LMAX) (cond (Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G)
      (passAux s G tab (acc + (x.b * G + Nat.lcm x.L s - 1) / Nat.lcm x.L s) ok) (passAux s G tab acc false))
      (passAux s G tab acc ok)).1 = _
    have h' : ∀ y ∈ tab, chiB y = true → gS s y = G := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [cond_chi]
    split_ifs with hx
    · have hc : chiB x = true := by simp [chiB, hx]
      have hgx : gS s x = G := h x (by simp) hc
      have hb : Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G = true := Nat.beq_eq_true_eq _ _ ▸ hgx
      rw [hb]
      simp only [cond_true]
      rw [passAux_sum s G tab _ ok h']
      simp only [bsum, List.filter_cons, hc, Bool.true_and, beq_iff_eq, hgx, if_true, List.map_cons, List.sum_cons]
      simp only [vS]
      rw [show Nat.gcd (Nat.lcm x.L s) PER = G from hgx]
      ring
    · rw [passAux_sum s G tab acc ok h']
      have hc : chiB x = false := by simp [chiB, hx]
      simp [bsum, List.filter_cons, hc]

theorem bsum_other (s G d : ℕ) (tab : List Ent) (h : ∀ x ∈ tab, chiB x = true → gS s x = G) (hd : d ≠ G) :
    bsum s d tab = 0 := by
  unfold bsum
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro x hx
    by_cases hc : chiB x = true
    · have := h x hx hc; simp [hc, this, Ne.symm hd]
    · simp [Bool.eq_false_iff.mpr hc]

theorem lcm_dvd120 (s h : ℕ) (hh : h ∣ 120) : Nat.lcm (Nat.gcd s PER) h ∣ 120 :=
  Nat.lcm_dvd (Nat.gcd_dvd_right _ _) hh

theorem pass_bucket (s G : ℕ) (tab : List Ent) (h : (passK s G tab).2 = true) (d : ℕ) :
    (if d = G then (passK s G tab).1 else 0) = bsum s d tab := by
  have hp := passAux_ok s G tab 0 true h
  by_cases hd : d = G
  · rw [if_pos hd, hd]
    have := passAux_sum s G tab 0 true hp.2
    show (passAux s G tab 0 true).1 = bsum s G tab
    simpa using this
  · rw [if_neg hd, bsum_other s G d tab hp.2 hd]

/-- The helper of `accSplitK`. -/
noncomputable def splitAux (s : ℕ) (subs : List (ℕ × List Ent)) : List ℕ → Bool → List ℕ × Bool :=
  List.rec (motive := fun _ => List ℕ → Bool → List ℕ × Bool) (fun acc ok => (acc, ok))
    (fun ht _ ih acc ok =>
      let G := Nat.lcm (Nat.gcd s PER) ht.1
      let r := passK s G ht.2
      ih (addAt G r.1 div120 acc) (ok && r.2)) subs

theorem splitAux_eq (s : ℕ) : ∀ (subs : List (ℕ × List Ent)) (F : ℕ → ℕ) (ok : Bool),
    (splitAux s subs (div120.map F) ok).2 = true →
      ok = true ∧ (splitAux s subs (div120.map F) ok).1 = div120.map (fun d => F d + (subs.map fun ht => bsum s d ht.2).sum)
  | [], F, ok, h => ⟨h, by simp [splitAux]⟩
  | ht :: subs, F, ok, h => by
    have e : splitAux s (ht :: subs) (div120.map F) ok =
        splitAux s subs (div120.map fun d => F d + if d = Nat.lcm (Nat.gcd s PER) ht.1 then
          (passK s (Nat.lcm (Nat.gcd s PER) ht.1) ht.2).1 else 0)
          (ok && (passK s (Nat.lcm (Nat.gcd s PER) ht.1) ht.2).2) := by
      show splitAux s subs (addAt _ _ div120 (div120.map F)) _ = _
      rw [addAt_map _ _ F div120 div120_nodup]
    rw [e] at h ⊢
    obtain ⟨h1, h2⟩ := splitAux_eq s subs _ _ h
    simp only [Bool.and_eq_true] at h1
    refine ⟨h1.1, ?_⟩
    rw [h2]
    apply List.map_congr_left
    intro d _
    rw [pass_bucket s _ ht.2 h1.2 d]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem accSplitK_sound (s : ℕ) (tab : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = div120.map fun h => (h, tab.filter fun x => keyH x == h)) (acc : List ℕ)
    (h : accSplitK s subs = (acc, true)) : accG s tab = acc := by
  have h' : splitAux s subs (div120.map fun _ => 0) true = (acc, true) := h
  have := splitAux_eq s subs (fun _ => 0) true (by rw [h'])
  rw [h'] at this
  have h2 : acc = div120.map (fun d => 0 + (subs.map fun ht => bsum s d ht.2).sum) := this.2
  rw [accG_eq_bucket, h2]
  apply List.map_congr_left
  intro d _
  rw [zero_add, hsubs, bsum_split s d tab, List.map_map]
  rfl

theorem subK_eq (h : ℕ) : ∀ (tab : List Ent), subK h tab = tab.filter fun x => keyH x == h
  | [] => rfl
  | x :: tab => by
    show cond (Nat.beq (Nat.gcd x.L PER) h) (x :: subK h tab) (subK h tab) = _
    rw [subK_eq h tab, List.filter_cons]
    by_cases hx : Nat.gcd x.L PER = h
    · rw [show Nat.beq (Nat.gcd x.L PER) h = true from Nat.beq_eq_true_eq _ _ ▸ hx]
      simp [keyH, hx]
    · rw [show Nat.beq (Nat.gcd x.L PER) h = false from Bool.eq_false_iff.mpr (fun e => hx (Nat.eq_of_beq_eq_true e))]
      simp [keyH, hx]

theorem bdEq_eq (x y : BD) (h : bdEq x y = true) : x = y := by
  unfold bdEq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  cases x; cases y
  simp only [BD.mk.injEq]
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, h4, h5, Nat.eq_of_beq_eq_true h6⟩

theorem mkBDS_sound (tT tR : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = div120.map fun h => (h, tT.filter fun x => keyH x == h)) (r0a : ℕ) (gx : Grp × Bool) (bd : BD)
    (h : (mkBDS subs tR r0a gx).2 && bdEq (mkBDS subs tR r0a gx).1 bd = true) : mkBD tT tR r0a gx = bd := by
  simp only [Bool.and_eq_true] at h
  rw [← bdEq_eq _ _ h.2]
  unfold mkBD mkBDS at *
  cases hx : gx.2
  · simp [hx]
  · simp only [hx, cond_true, if_true] at h ⊢
    have hacc := accSplitK_sound gx.1.t tT subs hsubs (accSplitK gx.1.t subs).1
      (Prod.ext rfl h.1)
    rw [hacc, sumRK_eq]

theorem bdChunkOK_sound (tT tR : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = div120.map fun h => (h, tT.filter fun x => keyH x == h)) (r0a : ℕ) :
    ∀ (gs : List (Grp × Bool)) (bds : List BD), bdChunkOK subs tR r0a gs bds = true → gs.map (mkBD tT tR r0a) = bds
  | [], [], _ => rfl
  | gx :: gs, bd :: bds, h => by
    simp only [bdChunkOK, Bool.and_eq_true] at h
    simp only [List.map_cons]
    rw [mkBDS_sound tT tR subs hsubs r0a gx bd (by simpa using h.1), bdChunkOK_sound tT tR subs hsubs r0a gs bds h.2]
  | [], _ :: _, h => by simp [bdChunkOK] at h
  | _ :: _, [], h => by simp [bdChunkOK] at h

theorem teffOf_eq_V (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) :
    teffOf D tT dT tR bs = teffOfV D (accG 1 tT) (sumA tT) (sumB tT) dT (sumR 1 tR) bs := rfl

end Romanoff.M3
