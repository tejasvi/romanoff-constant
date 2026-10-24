import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab287
import Romanoff.M3.K.Tab289

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp43 : segOK (decTabK tab287) drop287 ((D.data.gA.drop 287).take 2) tab289 drop289 = true := by decide +kernel
