import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab71

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp1 : segOK tab0 0 ((R45.M3G.D.data.gA.drop 0).take 71) tab71 drop71 = true := by decide +kernel

end R45.M3G.KS
