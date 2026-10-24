import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab224
import Romanoff.M3.K.Tab228

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp24 : segOK (decTabK tab224) drop224 ((D.data.gA.drop 224).take 4) tab228 drop228 = true := by decide +kernel
