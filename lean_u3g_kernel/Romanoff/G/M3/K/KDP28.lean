import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab246
import Romanoff.G.M3.K.Tab250

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp28 : segOK (decTabK tab246) drop246 ((R45.M3G.D.data.gA.drop 246).take 4) tab250 drop250 = true := by decide +kernel

end R45.M3G.KS
