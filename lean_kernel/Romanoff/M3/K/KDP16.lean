import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab189
import Romanoff.M3.K.Tab194

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp16 : segOK (decTabK tab189) drop189 ((D.data.gA.drop 189).take 5) tab194 drop194 = true := by decide +kernel
