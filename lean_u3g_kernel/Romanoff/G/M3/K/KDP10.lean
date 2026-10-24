import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab159
import Romanoff.G.M3.K.Tab166

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp10 : segOK (decTabK tab159) drop159 ((R45.M3G.D.data.gA.drop 159).take 7) tab166 drop166 = true := by decide +kernel

end R45.M3G.KS
