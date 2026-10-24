import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab284
import Romanoff.G.M3.K.Tab286

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp39 : segOK (decTabK tab284) drop284 ((R45.M3G.D.data.gA.drop 284).take 2) tab286 drop286 = true := by decide +kernel

end R45.M3G.KS
