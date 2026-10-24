import Romanoff.E.S2.Key
import Romanoff.E.S2.Native
import Romanoff.E.Lit

/-!
# U3e: the headline `d ≥ 0.110449` (native track)

`romanoff_U3e`: under ESP28 and PNTAP for the modulus `l' = 3·5·7·11·13·17·31·241·41·19·73·23·37` and R0Bound,
`0.110449 ≤ liminf dens`.  Stage 1 (`tboundALit`): the divisor-form tail bound `TBoundA (tabB BLit) R0tLit`;
`liminf_ge_of_TBoundA` reduces to the evaluator at every rational `α` of the tail simplex (enlarged by `δ`);
stage 2: `lagBound_ge_V` (the soundness of the evaluator) and `finalOK_true` (the evaluation).
-/

open Filter R45 R45.EV R45.U3E

namespace Romanoff.E

theorem s2_value : claimQ ≤ V (evalPar 88 (foldOrbits 3960 baseP)) := of_decide_eq_true S2.finalOK_true

theorem romanoff_U3e (h1 : ESP28 E.ell) (h3 : PNTAP E.ell) (h5 : R0Bound) : E.U3eStatement := by
  have h := liminf_ge_of_TBoundA (claim := claimQ) (δ := delta) (tboundALit h5) (by norm_num [delta])
    (fun α hα hαs => s2_value.trans (S2.lagBound_ge_V α hα hαs 88)) h1 h3 h5
  have e : ((claimQ : ℚ) : ℝ) = 110449 / 1000000 := by norm_num [claimQ]
  unfold U3eStatement
  rw [← e]
  exact h

end Romanoff.E
