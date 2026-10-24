import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab218
import Romanoff.G.M3.K.Tab222

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp21 : segOK (decTabK tab218) drop218 ((R45.M3G.D.data.gA.drop 218).take 4) tab222 drop222 = true := by decide +kernel

end R45.M3G.KS
