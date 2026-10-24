import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab143
import Romanoff.G.M3.K.Tab151

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp8 : segOK (decTabK tab143) drop143 ((R45.M3G.D.data.gA.drop 143).take 8) tab151 drop151 = true := by decide +kernel

end R45.M3G.KS
