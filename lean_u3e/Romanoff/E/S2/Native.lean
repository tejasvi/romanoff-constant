import RCert.E.Ev

/-!
# U3e stage 2: the native evaluation (the only `native_decide` of stage 2)

`finalOK baseP 88 = decide (claim ≤ V (evalPar 88 (foldOrbits 3960 baseP)))`: the BASE keys in pieces of 88, one
dedicated task per piece (any piece size gives the same value, `V_evalPar`).  This module imports only the compiled
evaluator; it is elaborated once, on a large machine, and its `.olean` is reused.
-/

namespace Romanoff.E.S2

open R45 R45.EV

theorem finalOK_true : finalOK baseP 88 = true := by native_decide

end Romanoff.E.S2
