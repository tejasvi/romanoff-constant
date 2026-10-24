import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab194
import Romanoff.G.M3.K.Tab199

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp16 : segOK (decTabK tab194) drop194 ((R45.M3G.D.data.gA.drop 194).take 5) tab199 drop199 = true := by decide +kernel

end R45.M3G.KS
