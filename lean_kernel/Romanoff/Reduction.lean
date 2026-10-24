import Romanoff.Final
import Romanoff.M4B
import Romanoff.M4C
import Romanoff.M4E

/-!
# The reduction to the evaluator's value (no computation)

`romanoff_U2_of` / `romanoff_v3_of`: for any `T(c)` table with `TBound`, a lower bound for the evaluator's value at that
table is a lower bound for the lower density (from `lagR_le_liminf` with the layers (B), (C)).  Shared by the native
track (`Romanoff/Theorems.lean`) and the kernel-only track (`Romanoff/CertKFinal.lean`).
-/

open Filter Topology R45 R45.P45 R45.D45

namespace Romanoff

/-- U2 for a table `teff` with `TBound teff` and an evaluator value `≥ 0.109406`. -/
theorem romanoff_U2_of (hE : LimitFacts) {teff : List ℚ} (hT : TBound teff)
    (hnum : (109406 / 1000000 : ℚ) ≤ lagBound (parOf teff 8 0) (orbits 120 ellPrimes))
    (hESP : ESP28 ell) (hPNT : PNTAP ell) (hR0 : R0Bound) : U2Statement := by
  have h := lagR_le_liminf xuESP sumXUJT orbSumLink ncQLink lagBoundSplit dataFacts hE hT 8 0 (by norm_num)
    hESP hPNT hR0 (Or.inl rfl)
  have h2 : ((109406 / 1000000 : ℚ) : ℝ) ≤ lagR teff 8 0 := by unfold lagR; exact_mod_cast hnum
  unfold U2Statement
  have e : ((109406 / 1000000 : ℚ) : ℝ) = (109406 / 1000000 : ℝ) := by norm_num
  rw [e] at h2
  exact h2.trans h

/-- v3 for a table `teff` with `TBound teff` and an evaluator value `≥ 0.117953`. -/
theorem romanoff_v3_of (hE : LimitFacts) {teff : List ℚ} (hT : TBound teff)
    (hnum : (117953 / 1000000 : ℚ) ≤ lagBound (parOf teff C1v3 muV3) (orbits 120 ellPrimes))
    (hESP : ESP28 ell) (hJT : JTProp2) (hPNT : PNTAP ell) (hR0 : R0Bound) : V3Statement := by
  have hc1 : ((C1v3 : ℚ) : ℝ) = C1R := by unfold C1v3 C1R; push_cast; norm_num
  have hmu : (0 : ℝ) ≤ ((muV3 : ℚ) : ℝ) := by unfold muV3; push_cast; norm_num
  have h := lagR_le_liminf xuESP sumXUJT orbSumLink ncQLink lagBoundSplit dataFacts hE hT C1v3 muV3 hmu
    hESP hPNT hR0 (Or.inr ⟨hJT, hc1⟩)
  have h2 : ((117953 / 1000000 : ℚ) : ℝ) ≤ lagR teff C1v3 muV3 := by unfold lagR; exact_mod_cast hnum
  unfold V3Statement
  have e : ((117953 / 1000000 : ℚ) : ℝ) = (117953 / 1000000 : ℝ) := by norm_num
  rw [e] at h2
  exact h2.trans h

theorem ellPO_fst : R45.D45.ellPO.map (·.1) = ellPrimes := by decide

end Romanoff
