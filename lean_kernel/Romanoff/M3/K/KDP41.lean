import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab281
import Romanoff.M3.K.Tab284

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp41 : segOK (decTabK tab281) drop281 ((D.data.gA.drop 281).take 3) tab284 drop284 = true := by decide +kernel
