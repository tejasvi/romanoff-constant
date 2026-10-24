import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab266
import Romanoff.M3.K.Tab269

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp36 : segOK (decTabK tab266) drop266 ((D.data.gA.drop 266).take 3) tab269 drop269 = true := by decide +kernel
