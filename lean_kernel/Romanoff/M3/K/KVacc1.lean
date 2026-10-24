import RCert.M3.KFun
import Romanoff.M3.K.Vals

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kvacc1 : (accSplitK 1 subsLit).1 = acc1 ∧ (accSplitK 1 subsLit).2 = true := by decide +kernel
