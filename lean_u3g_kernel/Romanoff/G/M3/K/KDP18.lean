import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab204
import Romanoff.G.M3.K.Tab209

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp18 : segOK (decTabK tab204) drop204 ((R45.M3G.D.data.gA.drop 204).take 5) tab209 drop209 = true := by decide +kernel

end R45.M3G.KS
