import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR12
import Romanoff.G.M3.K.TabR13

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kr13 : segROK (decTabK tabR12) ((R45.M3G.D.data.gE.drop 12).take 1) tabR13 = true := by decide +kernel

end R45.M3G.KS
