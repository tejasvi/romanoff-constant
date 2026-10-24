import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab230
import Romanoff.G.M3.K.Tab234

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp24 : segOK (decTabK tab230) drop230 ((R45.M3G.D.data.gA.drop 230).take 4) tab234 drop234 = true := by decide +kernel

end R45.M3G.KS
