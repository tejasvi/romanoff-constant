import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab194
import Romanoff.M3.K.Tab199

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp17 : segOK (decTabK tab194) drop194 ((D.data.gA.drop 194).take 5) tab199 drop199 = true := by decide +kernel
