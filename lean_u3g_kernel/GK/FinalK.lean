import GK.Final
import Romanoff.G.LitK

/-!
# k45g: U3g and V4g, kernel-only

`romanoff_U3g_K` and `romanoff_V4g_K` have the statements and hypotheses of the native `Romanoff.G.romanoff_U3g` and
`Romanoff.G.romanoff_V4g` (Romanoff/G/U3g.lean, Romanoff/G/V4g.lean). Stage 1 is K3's `Romanoff.G.K.tboundALitK`, stage 2 the
kernel evaluation `R45.GK.values_K` (GK/Final.lean).
-/

namespace Romanoff.G

/-- U3g, kernel-only: `0.110825 ≤ liminf dens` under ESP28, PNTAP for `l_G` and R0Bound. -/
theorem romanoff_U3g_K (h1 : ESP28 G.ell) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.U3gStatement :=
  romanoff_U3g_of_S1 K.tboundALitK h1 h3 h5

/-- V4g, kernel-only: `0.119178 ≤ liminf dens` under ESP28, JTProp2 (I2), PNTAP for `l_G` and R0Bound. -/
theorem romanoff_V4g_K (h1 : ESP28 G.ell) (h2 : JTProp2) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.V4gStatement :=
  romanoff_V4g_of_S1 K.tboundALitK h1 h2 h3 h5

end Romanoff.G
