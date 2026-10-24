import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR14
import Romanoff.G.M3.K.TabR

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kr15 : segROK (decTabK tabR14) ((R45.M3G.D.data.gE.drop 14).take 1) tabR = true := by decide +kernel

end R45.M3G.KS
