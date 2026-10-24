import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab236
import Romanoff.M3.K.Tab240

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp27 : segOK (decTabK tab236) drop236 ((D.data.gA.drop 236).take 4) tab240 drop240 = true := by decide +kernel
