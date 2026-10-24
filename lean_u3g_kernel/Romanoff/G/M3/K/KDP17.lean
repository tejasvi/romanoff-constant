import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab199
import Romanoff.G.M3.K.Tab204

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp17 : segOK (decTabK tab199) drop199 ((R45.M3G.D.data.gA.drop 199).take 5) tab204 drop204 = true := by decide +kernel

end R45.M3G.KS
