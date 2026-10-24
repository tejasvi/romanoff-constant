import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab220
import Romanoff.M3.K.Tab224

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp23 : segOK (decTabK tab220) drop220 ((D.data.gA.drop 220).take 4) tab224 drop224 = true := by decide +kernel
