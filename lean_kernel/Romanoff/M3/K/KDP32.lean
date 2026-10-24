import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab254
import Romanoff.M3.K.Tab257

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp32 : segOK (decTabK tab254) drop254 ((D.data.gA.drop 254).take 3) tab257 drop257 = true := by decide +kernel
