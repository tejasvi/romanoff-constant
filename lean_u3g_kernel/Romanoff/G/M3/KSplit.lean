import Romanoff.M3.KSplit
import Romanoff.G.M3.Sums
import RCert.M3G.KFun

/-!
# M3 at period 27720, K version: `accG` from subtables by `gcd(L, 27720)`

The period-120 file Romanoff/M3/KSplit.lean with `120 → 27720`, `div120 → divG` (96 divisors) and the passes of
RCert/M3G/KFun.lean: `accG s tab = divG.map (bsum s · tab)` (bucket sums); the buckets split over the subtables
`gcd(L, 27720) = h`, and on a subtable whose entries all have `gcd(lcm(L, s), 27720) = G` (checked by `passKG`) only the
bucket `G` is nonzero. The period-free lemmas (`addAt_map`, `sum_ite_eq_mem`, `sum_partition`, `bdEq_eq`, `chiB`) are
those of Romanoff/M3/KSplit.lean.
-/

namespace Romanoff.G.MK

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD
open R45.M3G
open Romanoff.M3 (chiB addAt_map sum_ite_eq_mem sum_partition bdEq_eq cond_chi sumRK_eq)

/-- The value and the bucket of an entry in `accG s`. -/
def vS (s : ℕ) (x : Ent) : ℕ := (x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s
def gS (s : ℕ) (x : Ent) : ℕ := Nat.gcd (Nat.lcm x.L s) PER

/-- The bucket sum. -/
def bsum (s d : ℕ) (tab : List Ent) : ℕ := ((tab.filter fun x => chiB x && gS s x == d).map (vS s)).sum

theorem divG_nodup : divG.Nodup := by decide +kernel

theorem gS_mem (s : ℕ) (x : Ent) : gS s x ∈ divG := Romanoff.G.M3.mem_divG _ (Nat.gcd_dvd_right _ _)

theorem accG_bucket (s : ℕ) : ∀ (tab : List Ent) (F : ℕ → ℕ),
    tab.foldl (fun acc x =>
      if 1 ≤ x.L ∧ x.L ≤ LMAX then
        addAt (Nat.gcd (Nat.lcm x.L s) PER) ((x.b * Nat.gcd (Nat.lcm x.L s) PER + Nat.lcm x.L s - 1) / Nat.lcm x.L s)
          divG acc
      else acc) (divG.map F) = divG.map (fun d => F d + bsum s d tab)
  | [], F => by simp [bsum]
  | x :: tab, F => by
    simp only [List.foldl_cons]
    split_ifs with hx
    · rw [addAt_map _ _ F divG divG_nodup, accG_bucket s tab]
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

theorem accG_eq_bucket (s : ℕ) (tab : List Ent) : accG s tab = divG.map (fun d => bsum s d tab) := by
  unfold accG
  have h := accG_bucket s tab (fun _ => 0)
  simp only [zero_add] at h
  rw [← h]
  rfl

end Romanoff.G.MK

namespace Romanoff.G.MK

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD
open R45.M3G
open Romanoff.M3 (chiB addAt_map sum_ite_eq_mem sum_partition bdEq_eq cond_chi sumRK_eq)

/-- The key of the subtables. -/
def keyH (x : Ent) : ℕ := Nat.gcd x.L PER

theorem keyH_mem (x : Ent) : keyH x ∈ divG := Romanoff.G.M3.mem_divG _ (Nat.gcd_dvd_right _ _)

theorem bsum_split (s d : ℕ) (tab : List Ent) :
    bsum s d tab = (divG.map fun h => bsum s d (tab.filter fun x => keyH x == h)).sum := by
  unfold bsum
  rw [sum_partition (vS s) keyH divG divG_nodup _ (fun x _ => keyH_mem x)]
  congr 1
  apply List.map_congr_left
  intro h _
  rw [List.filter_filter, List.filter_filter]
  rw [List.filter_congr (fun x _ => Bool.and_comm (keyH x == h) (chiB x && gS s x == d))]

/-- The helper of `passKG`. -/
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

theorem lcm_dvdG (s h : ℕ) (hh : h ∣ 27720) : Nat.lcm (Nat.gcd s PER) h ∣ 27720 :=
  Nat.lcm_dvd (Nat.gcd_dvd_right _ _) hh

theorem pass_bucket (s G : ℕ) (tab : List Ent) (h : (passKG s G tab).2 = true) (d : ℕ) :
    (if d = G then (passKG s G tab).1 else 0) = bsum s d tab := by
  have hp := passAux_ok s G tab 0 true h
  by_cases hd : d = G
  · rw [if_pos hd, hd]
    have := passAux_sum s G tab 0 true hp.2
    show (passAux s G tab 0 true).1 = bsum s G tab
    simpa using this
  · rw [if_neg hd, bsum_other s G d tab hp.2 hd]

/-- The helper of `accSplitKG`. -/
noncomputable def splitAux (s : ℕ) (subs : List (ℕ × List Ent)) : List ℕ → Bool → List ℕ × Bool :=
  List.rec (motive := fun _ => List ℕ → Bool → List ℕ × Bool) (fun acc ok => (acc, ok))
    (fun ht _ ih acc ok =>
      let G := Nat.lcm (Nat.gcd s PER) ht.1
      let r := passKG s G ht.2
      ih (addAt G r.1 divG acc) (ok && r.2)) subs

theorem splitAux_eq (s : ℕ) : ∀ (subs : List (ℕ × List Ent)) (F : ℕ → ℕ) (ok : Bool),
    (splitAux s subs (divG.map F) ok).2 = true →
      ok = true ∧ (splitAux s subs (divG.map F) ok).1 = divG.map (fun d => F d + (subs.map fun ht => bsum s d ht.2).sum)
  | [], F, ok, h => ⟨h, by simp [splitAux]⟩
  | ht :: subs, F, ok, h => by
    have e : splitAux s (ht :: subs) (divG.map F) ok =
        splitAux s subs (divG.map fun d => F d + if d = Nat.lcm (Nat.gcd s PER) ht.1 then
          (passKG s (Nat.lcm (Nat.gcd s PER) ht.1) ht.2).1 else 0)
          (ok && (passKG s (Nat.lcm (Nat.gcd s PER) ht.1) ht.2).2) := by
      show splitAux s subs (addAt _ _ divG (divG.map F)) _ = _
      rw [addAt_map _ _ F divG divG_nodup]
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

theorem accSplitKG_sound (s : ℕ) (tab : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = divG.map fun h => (h, tab.filter fun x => keyH x == h)) (acc : List ℕ)
    (h : accSplitKG s subs = (acc, true)) : accG s tab = acc := by
  have h' : splitAux s subs (divG.map fun _ => 0) true = (acc, true) := h
  have := splitAux_eq s subs (fun _ => 0) true (by rw [h'])
  rw [h'] at this
  have h2 : acc = divG.map (fun d => 0 + (subs.map fun ht => bsum s d ht.2).sum) := this.2
  rw [accG_eq_bucket, h2]
  apply List.map_congr_left
  intro d _
  rw [zero_add, hsubs, bsum_split s d tab, List.map_map]
  rfl

theorem subKG_eq (h : ℕ) : ∀ (tab : List Ent), subKG h tab = tab.filter fun x => keyH x == h
  | [] => rfl
  | x :: tab => by
    show cond (Nat.beq (Nat.gcd x.L PER) h) (x :: subKG h tab) (subKG h tab) = _
    rw [subKG_eq h tab, List.filter_cons]
    by_cases hx : Nat.gcd x.L PER = h
    · rw [show Nat.beq (Nat.gcd x.L PER) h = true from Nat.beq_eq_true_eq _ _ ▸ hx]
      simp [keyH, hx]
    · rw [show Nat.beq (Nat.gcd x.L PER) h = false from Bool.eq_false_iff.mpr (fun e => hx (Nat.eq_of_beq_eq_true e))]
      simp [keyH, hx]

theorem mkBDSG_sound (tT tR : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = divG.map fun h => (h, tT.filter fun x => keyH x == h)) (r0a : ℕ) (gx : Grp × Bool) (bd : BD)
    (h : (mkBDSG subs tR r0a gx).2 && bdEq (mkBDSG subs tR r0a gx).1 bd = true) : mkBD tT tR r0a gx = bd := by
  simp only [Bool.and_eq_true] at h
  rw [← bdEq_eq _ _ h.2]
  unfold mkBD mkBDSG at *
  cases hx : gx.2
  · simp [hx]
  · simp only [hx, cond_true, if_true] at h ⊢
    have hacc := accSplitKG_sound gx.1.t tT subs hsubs (accSplitKG gx.1.t subs).1
      (Prod.ext rfl h.1)
    rw [hacc, sumRK_eq]

theorem bdChunkOKG_sound (tT tR : List Ent) (subs : List (ℕ × List Ent))
    (hsubs : subs = divG.map fun h => (h, tT.filter fun x => keyH x == h)) (r0a : ℕ) :
    ∀ (gs : List (Grp × Bool)) (bds : List BD), bdChunkOKG subs tR r0a gs bds = true → gs.map (mkBD tT tR r0a) = bds
  | [], [], _ => rfl
  | gx :: gs, bd :: bds, h => by
    simp only [bdChunkOKG, Bool.and_eq_true] at h
    simp only [List.map_cons]
    rw [mkBDSG_sound tT tR subs hsubs r0a gx bd (by simpa using h.1), bdChunkOKG_sound tT tR subs hsubs r0a gs bds h.2]
  | [], _ :: _, h => by simp [bdChunkOKG] at h
  | _ :: _, [], h => by simp [bdChunkOKG] at h

end Romanoff.G.MK
