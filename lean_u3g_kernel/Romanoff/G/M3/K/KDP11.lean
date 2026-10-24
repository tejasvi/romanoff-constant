import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Tab166
import Romanoff.G.M3.K.Tab172

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kdp11 : segOK (decTabK tab166) drop166 ((R45.M3G.D.data.gA.drop 166).take 6) tab172 drop172 = true := by decide +kernel

end R45.M3G.KS
