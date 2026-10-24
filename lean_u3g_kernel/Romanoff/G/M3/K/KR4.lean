import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR3
import Romanoff.G.M3.K.TabR4

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kr4 : segROK (decTabK tabR3) ((R45.M3G.D.data.gE.drop 3).take 1) tabR4 = true := by decide +kernel

end R45.M3G.KS
