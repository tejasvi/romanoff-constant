import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab173
import Romanoff.M3.K.Tab179

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp13 : segOK (decTabK tab173) drop173 ((D.data.gA.drop 173).take 6) tab179 drop179 = true := by decide +kernel
