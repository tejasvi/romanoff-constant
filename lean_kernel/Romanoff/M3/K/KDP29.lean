import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab244
import Romanoff.M3.K.Tab248

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp29 : segOK (decTabK tab244) drop244 ((D.data.gA.drop 244).take 4) tab248 drop248 = true := by decide +kernel
