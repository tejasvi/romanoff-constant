import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab257
import Romanoff.M3.K.Tab260

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp33 : segOK (decTabK tab257) drop257 ((D.data.gA.drop 257).take 3) tab260 drop260 = true := by decide +kernel
