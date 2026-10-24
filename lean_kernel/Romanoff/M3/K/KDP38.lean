import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab272
import Romanoff.M3.K.Tab275

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp38 : segOK (decTabK tab272) drop272 ((D.data.gA.drop 272).take 3) tab275 drop275 = true := by decide +kernel
