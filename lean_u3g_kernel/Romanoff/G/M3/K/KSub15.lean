import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab286
import Romanoff.G.M3.K.Sub15

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem ksub15 : entsEqK (R45.M3G.subKG 15 (decTabK tab286)) (decTabK sub15) = true := by decide +kernel

end R45.M3G.KS
