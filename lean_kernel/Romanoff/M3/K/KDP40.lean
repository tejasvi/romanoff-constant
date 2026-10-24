import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab278
import Romanoff.M3.K.Tab281

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp40 : segOK (decTabK tab278) drop278 ((D.data.gA.drop 278).take 3) tab281 drop281 = true := by decide +kernel
