import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab153
import Romanoff.M3.K.Tab160

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp10 : segOK (decTabK tab153) drop153 ((D.data.gA.drop 153).take 7) tab160 drop160 = true := by decide +kernel
