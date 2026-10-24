import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab251
import Romanoff.M3.K.Tab254

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp31 : segOK (decTabK tab251) drop251 ((D.data.gA.drop 251).take 3) tab254 drop254 = true := by decide +kernel
