import Romanoff.CertK
import Romanoff.Reduction
import K45.Lag.All
import K45.Fold
import Romanoff.M3.KMain

/-!
# K track: the certificate values and the theorems, kernel-only

`cert_U2_K`, `cert_v3_K`: the evaluator's bounds at `teffLit` from the kernel-checked fold (`K45.orbits_eq`)
and the 185 kernel-checked chunk bounds (`allChunks_ok`).  With the kernel-only `tboundLitK` (M3 K) they give
`romanoff_U2_K` / `romanoff_v3_K`, the same statements as `romanoff_U2` / `romanoff_v3` without `native_decide`.
-/

open Filter Topology R45 R45.D45 R45.P45 R45.K45L

namespace Romanoff

theorem orbits_eq_flatten : orbits 120 (ellPO.map (·.1)) = K45.Orb.orbChunks.flatten := K45.orbits_eq

theorem cert_U2_K' : (109406 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit 8 0) (orbits 120 (ellPO.map (·.1))) :=
  certK_U2_of K45.Orb.orbChunks lagBounds orbits_eq_flatten (by rfl) allChunks_ok (by decide +kernel)

theorem cert_v3_K' :
    (117953 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit C1v3 muV3) (orbits 120 (ellPO.map (·.1))) :=
  certK_v3_of K45.Orb.orbChunks lagBounds orbits_eq_flatten (by rfl) allChunks_ok (by decide +kernel)

theorem cert_U2_K : (109406 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit 8 0) (orbits 120 ellPrimes) := by
  rw [← ellPO_fst]; exact cert_U2_K'

theorem cert_v3_K : (117953 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit C1v3 muV3) (orbits 120 ellPrimes) := by
  rw [← ellPO_fst]; exact cert_v3_K'

/-- **U2**, kernel-only. -/
theorem romanoff_U2_K (h1 : ESP28 ell) (h3 : PNTAP ell) (h5 : R0Bound) : U2Statement :=
  romanoff_U2_of limitFacts (Romanoff.M3.tboundLitK h5) cert_U2_K h1 h3 h5

/-- **v3**, kernel-only. -/
theorem romanoff_v3_K (h1 : ESP28 ell) (h2 : JTProp2) (h3 : PNTAP ell) (h5 : R0Bound) : V3Statement :=
  romanoff_v3_of limitFacts (Romanoff.M3.tboundLitK h5) cert_v3_K h1 h2 h3 h5

end Romanoff
