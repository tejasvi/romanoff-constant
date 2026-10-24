import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab238
import Romanoff.G.M3.K.Tab242

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp26 : segOK (decTabK tab238) drop238 ((R45.M3G.D.data.gA.drop 238).take 4) tab242 drop242 = true := by decide +kernel

end R45.M3G.KS
