import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab263
import Romanoff.M3.K.Tab266

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp35 : segOK (decTabK tab263) drop263 ((D.data.gA.drop 263).take 3) tab266 drop266 = true := by decide +kernel
