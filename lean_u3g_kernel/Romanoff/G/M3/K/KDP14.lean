import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab184
import Romanoff.G.M3.K.Tab189

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp14 : segOK (decTabK tab184) drop184 ((R45.M3G.D.data.gA.drop 184).take 5) tab189 drop189 = true := by decide +kernel

end R45.M3G.KS
