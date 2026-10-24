import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab208
import Romanoff.M3.K.Tab212

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp20 : segOK (decTabK tab208) drop208 ((D.data.gA.drop 208).take 4) tab212 drop212 = true := by decide +kernel
