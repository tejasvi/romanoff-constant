import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab254
import Romanoff.G.M3.K.Tab258

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp30 : segOK (decTabK tab254) drop254 ((R45.M3G.D.data.gA.drop 254).take 4) tab258 drop258 = true := by decide +kernel

end R45.M3G.KS
