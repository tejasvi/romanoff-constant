import Romanoff.E.U3e

/-! The U3e theorem (native track): statement and axioms (`lake env lean Axioms45U3e.lean` after `lake build Romanoff.E.U3e`;
  output in u3e/runlogs/check_u3e.out). -/

set_option pp.fullNames true in
#check @Romanoff.E.romanoff_U3e

#print Romanoff.E.U3eStatement

#print axioms Romanoff.E.romanoff_U3e
