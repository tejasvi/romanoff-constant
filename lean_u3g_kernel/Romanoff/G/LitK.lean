import Romanoff.G.Tables
import Romanoff.G.M3.KMain
import RCert.G.BLit
import RCert.M3G.TeffLit

/-!
# U3g/V4g, K version: M3 in alpha form at the literals, with the table in divisor form

`tboundALitK : R0Bound → TBoundA (tabB BLit) R0tLit` (period 27720), the statement of the native `Romanoff.G.tboundALit`
(Romanoff/G/Lit.lean), kernel-only: `tboundA_of` with the kernel checks of M3 at period 27720 (Romanoff/G/M3/KMain.lean:
`certOK_K`, `sumsOK_K`, the table equations), the tail mass `R0tOf_K`, and `tabB BLit = tabOf` at every class from the two
checks at the 96 divisors of 27720 (`valsOK_K`, `R45.M3G.KS.ktb`, Romanoff/G/M3/KGcd.lean).
-/

open R45 R45.U3G R45.M3G R45.M3G.K

namespace Romanoff.G.K

/-- `TBoundA` only reads the entries below 27720 and is monotone in the tail mass (as in Romanoff/G/Lit.lean). -/
theorem TBoundA_congr {tab tab' : List ℚ} {R0t R0t' : ℚ} (hT : TBoundA tab R0t) (hlen : tab'.length = 27720)
    (heq : ∀ c < 27720, tab'.getD c 0 = tab.getD c 0) (hR : R0t ≤ R0t') : TBoundA tab' R0t' := by
  obtain ⟨_, α, hα0, hαs, hb⟩ := hT
  refine ⟨hlen, α, hα0, hαs.trans (by exact_mod_cast hR), fun c hc S hS => ?_⟩
  rw [heq c hc]
  exact hb c hc S hS

/-- The tail mass of the kernel-checked tables is `R0tLit`. -/
theorem R0tOf_K : Romanoff.G.M3.R0tOf (R45.M3.decTabK tabR) bsLit = R0tLit := by
  unfold Romanoff.G.M3.R0tOf
  rw [Romanoff.G.MK.r0a_eq]
  decide +kernel

/-- M3 in alpha form at the literals, period 27720, kernel-only. -/
theorem tboundALitK (h5 : R0Bound) : TBoundA (tabB BLit) R0tLit := by
  have h := Romanoff.G.M3.tboundA_of R45.M3G.D.data Romanoff.G.MK.certOK_K Romanoff.G.MK.sumsOK_K h5
  rw [Romanoff.G.MK.dT_eq, Romanoff.G.MK.tT_eq, Romanoff.G.MK.tR_eq, Romanoff.G.MK.bs_eq, R0tOf_K] at h
  refine TBoundA_congr h (Romanoff.G.tabB_length BLit) (fun c hc => ?_) (le_refl _)
  exact Romanoff.G.MK.tabB_getD_eq_tabOf R45.M3G.D.data _ _ _ _ BLit vals96 Romanoff.G.MK.valsOK_K
    R45.M3G.KS.ktb c hc

end Romanoff.G.K
