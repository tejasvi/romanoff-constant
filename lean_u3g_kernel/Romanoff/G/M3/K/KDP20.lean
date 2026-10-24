import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab214
import Romanoff.G.M3.K.Tab218

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp20 : segOK (decTabK tab214) drop214 ((R45.M3G.D.data.gA.drop 214).take 4) tab218 drop218 = true := by decide +kernel

end R45.M3G.KS
