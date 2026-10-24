import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab178
import Romanoff.G.M3.K.Tab184

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp13 : segOK (decTabK tab178) drop178 ((R45.M3G.D.data.gA.drop 178).take 6) tab184 drop184 = true := by decide +kernel

end R45.M3G.KS
