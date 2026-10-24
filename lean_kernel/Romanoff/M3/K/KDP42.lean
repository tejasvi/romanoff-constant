import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab284
import Romanoff.M3.K.Tab287

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp42 : segOK (decTabK tab284) drop284 ((D.data.gA.drop 284).take 3) tab287 drop287 = true := by decide +kernel
