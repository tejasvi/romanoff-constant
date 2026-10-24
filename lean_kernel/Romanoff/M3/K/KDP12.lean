import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab167
import Romanoff.M3.K.Tab173

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp12 : segOK (decTabK tab167) drop167 ((D.data.gA.drop 167).take 6) tab173 drop173 = true := by decide +kernel
