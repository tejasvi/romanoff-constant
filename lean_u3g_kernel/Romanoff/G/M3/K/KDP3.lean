import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab89
import Romanoff.G.M3.K.Tab103

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp3 : segOK (decTabK tab89) drop89 ((R45.M3G.D.data.gA.drop 89).take 14) tab103 drop103 = true := by decide +kernel

end R45.M3G.KS
