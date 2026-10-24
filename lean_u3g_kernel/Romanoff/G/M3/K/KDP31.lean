import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab258
import Romanoff.G.M3.K.Tab262

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp31 : segOK (decTabK tab258) drop258 ((R45.M3G.D.data.gA.drop 258).take 4) tab262 drop262 = true := by decide +kernel

end R45.M3G.KS
