import Romanoff.G.S2.Final
import Romanoff.G.S2.Native

/-!
# U3g: the headline `d ≥ 0.110825` (native track)

`romanoff_U3g`: under ESP28 and PNTAP for the modulus `l_G = 3·5·7·11·13·17·31·241·41·19·73·37·23·43·29` and R0Bound,
`0.110825 ≤ liminf dens`.  Stage 1 (`tboundALit`): the divisor-form tail bound at period 27720; stage 2: the soundness of
the evaluator (`lagBound_ge_Vf`, with the factorization of the rows at 27720 = 360 · 7 · 11) and `finalOK_true`.
-/

namespace Romanoff.G

theorem romanoff_U3g (h1 : ESP28 G.ell) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.U3gStatement :=
  romanoff_U3g_of S2.finalOK_true h1 h3 h5

end Romanoff.G
