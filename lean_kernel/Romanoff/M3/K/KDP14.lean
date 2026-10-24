import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab179
import Romanoff.M3.K.Tab184

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp14 : segOK (decTabK tab179) drop179 ((D.data.gA.drop 179).take 5) tab184 drop184 = true := by decide +kernel
