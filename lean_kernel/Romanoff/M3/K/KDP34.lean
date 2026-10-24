import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab260
import Romanoff.M3.K.Tab263

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp34 : segOK (decTabK tab260) drop260 ((D.data.gA.drop 260).take 3) tab263 drop263 = true := by decide +kernel
