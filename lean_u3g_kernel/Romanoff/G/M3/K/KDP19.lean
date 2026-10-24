import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab209
import Romanoff.G.M3.K.Tab214

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp19 : segOK (decTabK tab209) drop209 ((R45.M3G.D.data.gA.drop 209).take 5) tab214 drop214 = true := by decide +kernel

end R45.M3G.KS
