import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab269
import Romanoff.M3.K.Tab272

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp37 : segOK (decTabK tab269) drop269 ((D.data.gA.drop 269).take 3) tab272 drop272 = true := by decide +kernel
