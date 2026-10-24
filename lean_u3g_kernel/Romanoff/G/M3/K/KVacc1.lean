import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Vals

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kvacc1 : (R45.M3G.accSplitKG 1 subsLit).1 = acc1 ∧ (R45.M3G.accSplitKG 1 subsLit).2 = true := by decide +kernel

end R45.M3G.KS
