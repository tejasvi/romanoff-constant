import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab71
import Romanoff.G.M3.K.Tab89

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp2 : segOK (decTabK tab71) drop71 ((R45.M3G.D.data.gA.drop 71).take 18) tab89 drop89 = true := by decide +kernel

end R45.M3G.KS
