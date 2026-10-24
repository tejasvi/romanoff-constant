import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab266
import Romanoff.G.M3.K.Tab269

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp33 : segOK (decTabK tab266) drop266 ((R45.M3G.D.data.gA.drop 266).take 3) tab269 drop269 = true := by decide +kernel

end R45.M3G.KS
