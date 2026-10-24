import RCert.M3G.KFun
import RCert.G.BLit
import Romanoff.G.M3.K.Vals

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem ktb : R45.M3G.tabBOK R45.U3G.BLit vals96 = true := by decide +kernel

end R45.M3G.KS
