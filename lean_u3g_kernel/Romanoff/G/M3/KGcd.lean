import Romanoff.G.M3.M3A
import Romanoff.G.M3.KSplit
import RCert.G.U3G

/-!
# M3 at period 27720, K version: the alpha-form table depends on `c` only through `gcd(c, 27720)`

For `g ∣ 27720`, `g ∣ c ↔ g ∣ gcd(c, 27720)`. Every term of the class-`c` entry of `tabOf` (Romanoff/G/M3/M3A.lean) is a
divisor sum over `divG` (`sumDvd`) or a function of `gcd(c, 27720)` (`prC`, `drC`, the class-B terms of `tbC`), so the
entry of class `c` is the value at the divisor `gcd(c, 27720)` (`tabOf_getD_gcd`). The same holds for the divisor-form
table `tabB B` (`tabB_getD_gcd`). Hence two checks at the 96 divisors, `valsOK` (the values `tabNumV`) and `tabBOK` (the
divisor sums of `B`), give `tabB B = tabOf` at all 27720 classes (`tabB_getD_eq_tabOf`).
-/

namespace Romanoff.G.MK

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD
open R45.M3G

theorem mod_eq_zero_iff_gcd (c g : ℕ) (hg : g ∣ 27720) : c % g = 0 ↔ Nat.gcd c 27720 % g = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
  exact ⟨fun h => Nat.dvd_gcd h hg, fun h => h.trans (Nat.gcd_dvd_left _ _)⟩

theorem divG_dvd : ∀ d ∈ divG, d ∣ 27720 := by
  have h : (divG.all fun d => 27720 % d == 0) = true := by decide +kernel
  intro d hd
  have h1 := List.all_eq_true.mp h d hd
  exact Nat.dvd_of_mod_eq_zero (by simpa using h1)

theorem sumDvdAux_gcd (c : ℕ) : ∀ (ds acc : List ℕ), (∀ d ∈ ds, d ∣ 27720) →
    sumDvdAux c ds acc = sumDvdAux (Nat.gcd c 27720) ds acc
  | [], _, _ => by simp [sumDvdAux]
  | _ :: _, [], _ => by simp [sumDvdAux]
  | d :: ds, x :: xs, h => by
    simp only [sumDvdAux]
    rw [sumDvdAux_gcd c ds xs (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]
    have hd := mod_eq_zero_iff_gcd c d (h d List.mem_cons_self)
    by_cases h1 : c % d = 0
    · rw [if_pos h1, if_pos (hd.mp h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hd.mpr h2))]

theorem sumDvd_gcd (acc : List ℕ) (c : ℕ) : sumDvd acc c = sumDvd acc (Nat.gcd c 27720) :=
  sumDvdAux_gcd c divG acc divG_dvd

theorem gcd_gcd27720 (c : ℕ) : Nat.gcd (Nat.gcd c 27720) 27720 = Nat.gcd c 27720 :=
  Nat.gcd_eq_left (Nat.gcd_dvd_right c 27720)

theorem prC_gcd (prM c : ℕ) : prC prM c = prC prM (Nat.gcd c 27720) := by
  unfold prC; simp only [PER]; rw [gcd_gcd27720]

theorem drC_gcd (piU dD c : ℕ) : drC piU dD c = drC piU dD (Nat.gcd c 27720) := by
  unfold drC; simp only [PER]; rw [gcd_gcd27720]

theorem tbC_gcd (bs : List BD) (sB prc c : ℕ) : tbC bs sB prc c = tbC bs sB prc (Nat.gcd c 27720) := by
  unfold tbC
  congr 1
  apply List.map_congr_left
  intro d _
  simp only [PER]
  rw [← sumDvd_gcd, gcd_gcd27720]

/-- `tabNumV` at class `c` is its value at `gcd(c, 27720)`. -/
theorem tabNumV_gcd (D : Data) (acc : List ℕ) (sA sB dT : ℕ) (bs : List BD) (c : ℕ) :
    tabNumV D acc sA sB dT bs c = tabNumV D acc sA sB dT bs (Nat.gcd c 27720) := by
  unfold tabNumV
  simp only
  rw [sumDvd_gcd acc c, prC_gcd _ c, drC_gcd _ _ c, tbC_gcd bs sB _ c]

/-- The class-`c` entry of the alpha-form table `tabOf` is the value at the divisor `gcd(c, 27720)`. -/
theorem tabOf_getD_gcd (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) (c : ℕ) (hc : c < 27720) :
    (Romanoff.G.M3.tabOf D tT dT tR bs).getD c 0 =
      (tabNumV D (accG 1 tT) (sumA tT) (sumB tT) dT bs (Nat.gcd c 27720) : ℚ) / (SC : ℚ) := by
  have hc' : c < PER := hc
  rw [← tabNumV_gcd]
  unfold Romanoff.G.M3.tabOf
  rw [Romanoff.M3.getD_map_range _ _ _ hc']
  rfl

/-- The class-`c` entry of the divisor-form table `tabB B` is the divisor sum at `gcd(c, 27720)`. -/
theorem tabB_getD_gcd (B : ℕ → ℚ) (c : ℕ) (hc : c < 27720) :
    (R45.U3G.tabB B).getD c 0 = ((divG.filter fun g => Nat.gcd c 27720 % g == 0).map B).sum := by
  unfold R45.U3G.tabB
  rw [Romanoff.M3.getD_map_range _ _ _ hc]
  congr 2
  apply List.filter_congr
  intro g hg
  have h := mod_eq_zero_iff_gcd c g (divG_dvd g hg)
  by_cases h1 : c % g = 0
  · simp [h1, h.mp h1]
  · have h2 : ¬ Nat.gcd c 27720 % g = 0 := fun e => h1 (h.mpr e)
    simp [h1, h2]

theorem mem_zip_map_self {α β : Type*} (f : α → β) : ∀ (l : List α), ∀ a ∈ l, (a, f a) ∈ l.zip (l.map f)
  | [], _, h => by simp at h
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_zip_map_self f l a h)

/-- The two checks at the 96 divisors give `tabB B = tabOf` at every class. -/
theorem tabB_getD_eq_tabOf (D : Data) (tT : List Ent) (dT : ℕ) (tR : List Ent) (bs : List BD) (B : ℕ → ℚ)
    (vals : List ℕ) (hv : valsOK D (accG 1 tT) (sumA tT) (sumB tT) dT bs vals = true) (hb : tabBOK B vals = true) :
    ∀ c < 27720, (R45.U3G.tabB B).getD c 0 = (Romanoff.G.M3.tabOf D tT dT tR bs).getD c 0 := by
  intro c hc
  rw [tabB_getD_gcd B c hc, tabOf_getD_gcd D tT dT tR bs c hc]
  have hvals : divG.map (tabNumV D (accG 1 tT) (sumA tT) (sumB tT) dT bs) = vals := eq_of_beq hv
  have hd : Nat.gcd c 27720 ∈ divG := Romanoff.G.M3.mem_divG _ (Nat.gcd_dvd_right _ _)
  have hmem := mem_zip_map_self (tabNumV D (accG 1 tT) (sumA tT) (sumB tT) dT bs) divG _ hd
  rw [hvals] at hmem
  have h1 := List.all_eq_true.mp hb _ hmem
  exact eq_of_beq h1

end Romanoff.G.MK
