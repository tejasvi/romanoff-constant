import Romanoff.G.S2.Final
import Romanoff.G.S2.Native

/-!
# V4g: the headline `d ≥ 0.119178` assuming (I2) (native track)

`romanoff_V4g`: under ESP28, JTProp2 (Johnston–Trudgian Prop. 2, budget constant 6.7814) and PNTAP for the modulus
`l_G` and R0Bound, `0.119178 ≤ liminf dens`.  The same evaluation as U3g (`finalOK_true`), with the uniform budget multiplier
`μ = 687217/10^12`.
-/

namespace Romanoff.G

theorem romanoff_V4g (h1 : ESP28 G.ell) (h2 : JTProp2) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.V4gStatement :=
  romanoff_V4g_of S2.finalOK_true h1 h2 h3 h5

end Romanoff.G
