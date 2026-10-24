import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR11
import Romanoff.G.M3.K.TabR12

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kr12 : segROK (decTabK tabR11) ((R45.M3G.D.data.gE.drop 11).take 1) tabR12 = true := by decide +kernel

end R45.M3G.KS
