import Romanoff.Final
import Romanoff.M4B
import Romanoff.M4C
import Romanoff.M3.N
import RCert.Cert45Check
import Romanoff.M4E

/-!
# The 45a theorems (native track: the certificate values by `native_decide`)

`lagR_le_liminf` with the layers (B), (C), the M3 table `teffLit` (`TBound` from `R0Bound`) and the
evaluator's values at the period-120 data (compiled `native_decide` in `RCert/Cert45Check.lean`):
* U2 (unconditional): `0.109406 ≤ liminf dens` from ESP (28), PNT in progressions and the `R0` partial sums, for any
  `T(c)` table with `TBound` whose evaluation clears 0.109406;
* v3: `0.117953 ≤ liminf dens`, adding JT Prop. 2.
The `T(c)` table enters only through `TBound teff` (milestone M3) and the native check of the evaluator at `teff`.
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

/-- The evaluator at the M3 table (`teffLit`, 120 literal rationals = `teffCert`). -/
theorem cert_U2 : (109406 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit 8 0) (orbits 120 ellPrimes) := by
  rw [← ellPO_fst]; exact R45.P45.cert_U2_lit

theorem cert_v3 : (117953 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit C1v3 muV3) (orbits 120 ellPrimes) := by
  rw [← ellPO_fst]; exact R45.P45.cert_v3_lit

/-- **U2** (unconditional), given the limit layer: `0.109406 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}` from ESP (28), the prime
number theorem in progressions mod `ell` and the `R0` partial sums. -/
theorem romanoff_U2_E (hE : LimitFacts) (h1 : ESP28 ell) (h3 : PNTAP ell) (h5 : R0Bound) : U2Statement :=
  romanoff_U2_of hE (Romanoff.M3.tboundLit h5) cert_U2 h1 h3 h5

/-- **v3** (conditional on JT Prop. 2), given the limit layer: `0.117953 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
theorem romanoff_v3_E (hE : LimitFacts) (h1 : ESP28 ell) (h2 : JTProp2) (h3 : PNTAP ell) (h5 : R0Bound) :
    V3Statement :=
  romanoff_v3_of hE (Romanoff.M3.tboundLit h5) cert_v3 h1 h2 h3 h5

/-- **U2** (unconditional): `0.109406 ≤ liminf_{N → ∞} N⁻¹ #{n ≤ N : n = p + 2^a}`, from ESP (28) for the modulus
`ell`, the prime number theorem in progressions mod `ell`, and the bounded partial sums of `R0`. -/
theorem romanoff_U2 (h1 : ESP28 ell) (h3 : PNTAP ell) (h5 : R0Bound) : U2Statement :=
  romanoff_U2_E limitFacts h1 h3 h5

/-- **v3** (conditional on JT Prop. 2): `0.117953 ≤ liminf_{N → ∞} N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
theorem romanoff_v3 (h1 : ESP28 ell) (h2 : JTProp2) (h3 : PNTAP ell) (h5 : R0Bound) : V3Statement :=
  romanoff_v3_E limitFacts h1 h2 h3 h5

end Romanoff
