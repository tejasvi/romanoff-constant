import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab151
import Romanoff.G.M3.K.Tab159

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp9 : segOK (decTabK tab151) drop151 ((R45.M3G.D.data.gA.drop 151).take 8) tab159 drop159 = true := by decide +kernel

end R45.M3G.KS
