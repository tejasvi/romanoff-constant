import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab184
import Romanoff.M3.K.Tab189

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp15 : segOK (decTabK tab184) drop184 ((D.data.gA.drop 184).take 5) tab189 drop189 = true := by decide +kernel
