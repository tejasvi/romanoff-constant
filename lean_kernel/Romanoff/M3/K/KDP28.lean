import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab240
import Romanoff.M3.K.Tab244

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp28 : segOK (decTabK tab240) drop240 ((D.data.gA.drop 240).take 4) tab244 drop244 = true := by decide +kernel
