import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab222
import Romanoff.G.M3.K.Tab226

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp22 : segOK (decTabK tab222) drop222 ((R45.M3G.D.data.gA.drop 222).take 4) tab226 drop226 = true := by decide +kernel

end R45.M3G.KS
