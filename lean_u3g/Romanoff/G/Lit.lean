import Romanoff.G.Tables
import Romanoff.G.M3.M3A
import Romanoff.G.M3.N
import RCert.G.BCheck

/-!
# U3g/V4g, N version: M3 in alpha form at the literals, with the table in divisor form

`tboundALit : R0Bound → TBoundA (tabB BLit) R0tLit` (period 27720): `tboundA_of` with the native M3 checks at period 27720
(`certOK_data`, `sumsOK_data`, `teffD_eq`, `R0tD_eq`) and the native check `tabB_BLit_eq` (the divisor form of
`teff - gcd(c, 27720) R0t`).
-/

open R45 R45.U3G R45.M3G

namespace Romanoff.G

/-- `TBoundA` only reads the entries below 27720 and is monotone in the tail mass. -/
theorem TBoundA_congr {tab tab' : List ℚ} {R0t R0t' : ℚ} (hT : TBoundA tab R0t) (hlen : tab'.length = 27720)
    (heq : ∀ c < 27720, tab'.getD c 0 = tab.getD c 0) (hR : R0t ≤ R0t') : TBoundA tab' R0t' := by
  obtain ⟨_, α, hα0, hαs, hb⟩ := hT
  refine ⟨hlen, α, hα0, hαs.trans (by exact_mod_cast hR), fun c hc S hS => ?_⟩
  rw [heq c hc]
  exact hb c hc S hS

theorem tabB_BLit_getD (c : ℕ) (hc : c < 27720) :
    (tabB BLit).getD c 0 = teffLit.getD c 0 - ((Nat.gcd c 27720 : ℕ) : ℚ) * R0tLit := by
  rw [tabB_BLit_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

theorem R0tD_eq_R0tOf (D : R45.M3.Data) : R0tD D = M3.R0tOf (R45.M3.runDP (R45.M3.runDP R45.M3.tab0 D.gA) D.gE)
    (bsOf D (R45.M3.runDP R45.M3.tab0 D.gA) (R45.M3.runDP (R45.M3.runDP R45.M3.tab0 D.gA) D.gE)) := by
  simp only [R0tD, M3.R0tOf, R45.M3.tabTD, R45.M3.tabR, Romanoff.M3.runDPD_eq]

theorem R0tOf_eq : M3.R0tOf (R45.M3.runDP (R45.M3.runDP R45.M3.tab0 D.data.gA) D.data.gE)
    (bsOf D.data (R45.M3.runDP R45.M3.tab0 D.data.gA) (R45.M3.runDP (R45.M3.runDP R45.M3.tab0 D.data.gA) D.data.gE)) =
      R0tLit :=
  (R0tD_eq_R0tOf D.data).symm.trans R0tD_eq

/-- M3 in alpha form at the literals (period 27720, U3g/V4g modulus), divisor-form table. -/
theorem tboundALit (h5 : R0Bound) : TBoundA (tabB BLit) R0tLit := by
  have h := M3.tboundA_of D.data certOK_data sumsOK_data h5
  rw [R0tOf_eq] at h
  have hteff : teffOf D.data (R45.M3.runDP R45.M3.tab0 D.data.gA) (R45.M3.runDrop R45.M3.tab0 D.data.gA)
      (R45.M3.runDP (R45.M3.runDP R45.M3.tab0 D.data.gA) D.data.gE)
      (bsOf D.data (R45.M3.runDP R45.M3.tab0 D.data.gA) (R45.M3.runDP (R45.M3.runDP R45.M3.tab0 D.data.gA) D.data.gE)) =
      teffLit := by
    rw [← M3.teffD_eq_teffOf]
    exact teffD_eq
  refine TBoundA_congr h (tabB_length BLit) (fun c hc => ?_) (le_refl _)
  rw [M3.tabOf_getD _ _ _ _ _ c hc, hteff, R0tOf_eq, tabB_BLit_getD c hc]

end Romanoff.G
