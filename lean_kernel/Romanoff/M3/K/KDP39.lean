import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab275
import Romanoff.M3.K.Tab278

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp39 : segOK (decTabK tab275) drop275 ((D.data.gA.drop 275).take 3) tab278 drop278 = true := by decide +kernel
