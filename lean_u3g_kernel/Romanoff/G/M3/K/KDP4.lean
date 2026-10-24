import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab103
import Romanoff.G.M3.K.Tab115

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp4 : segOK (decTabK tab103) drop103 ((R45.M3G.D.data.gA.drop 103).take 12) tab115 drop115 = true := by decide +kernel

end R45.M3G.KS
