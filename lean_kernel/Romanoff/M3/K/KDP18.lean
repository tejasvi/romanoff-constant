import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab199
import Romanoff.M3.K.Tab204

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp18 : segOK (decTabK tab199) drop199 ((D.data.gA.drop 199).take 5) tab204 drop204 = true := by decide +kernel
