import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR4
import Romanoff.G.M3.K.TabR5

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kr5 : segROK (decTabK tabR4) ((R45.M3G.D.data.gE.drop 4).take 1) tabR5 = true := by decide +kernel

end R45.M3G.KS
