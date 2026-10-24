import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab275
import Romanoff.G.M3.K.Tab278

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp36 : segOK (decTabK tab275) drop275 ((R45.M3G.D.data.gA.drop 275).take 3) tab278 drop278 = true := by decide +kernel

end R45.M3G.KS
