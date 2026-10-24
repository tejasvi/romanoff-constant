import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab248
import Romanoff.M3.K.Tab251

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp30 : segOK (decTabK tab248) drop248 ((D.data.gA.drop 248).take 3) tab251 drop251 = true := by decide +kernel
