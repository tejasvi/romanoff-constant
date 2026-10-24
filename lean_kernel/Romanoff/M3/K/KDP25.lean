import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab228
import Romanoff.M3.K.Tab232

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp25 : segOK (decTabK tab228) drop228 ((D.data.gA.drop 228).take 4) tab232 drop232 = true := by decide +kernel
