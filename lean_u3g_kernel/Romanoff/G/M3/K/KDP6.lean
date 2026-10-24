import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab125
import Romanoff.G.M3.K.Tab134

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp6 : segOK (decTabK tab125) drop125 ((R45.M3G.D.data.gA.drop 125).take 9) tab134 drop134 = true := by decide +kernel

end R45.M3G.KS
