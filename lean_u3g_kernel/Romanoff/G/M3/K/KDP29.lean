import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab250
import Romanoff.G.M3.K.Tab254

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp29 : segOK (decTabK tab250) drop250 ((R45.M3G.D.data.gA.drop 250).take 4) tab254 drop254 = true := by decide +kernel

end R45.M3G.KS
