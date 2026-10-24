import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab204
import Romanoff.M3.K.Tab208

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp19 : segOK (decTabK tab204) drop204 ((D.data.gA.drop 204).take 4) tab208 drop208 = true := by decide +kernel
