import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab281
import Romanoff.G.M3.K.Tab284

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp38 : segOK (decTabK tab281) drop281 ((R45.M3G.D.data.gA.drop 281).take 3) tab284 drop284 = true := by decide +kernel

end R45.M3G.KS
