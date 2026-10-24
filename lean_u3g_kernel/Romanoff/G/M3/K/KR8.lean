import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR7
import Romanoff.G.M3.K.TabR8

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kr8 : segROK (decTabK tabR7) ((R45.M3G.D.data.gE.drop 7).take 1) tabR8 = true := by decide +kernel

end R45.M3G.KS
