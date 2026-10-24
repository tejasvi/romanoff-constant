import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab232
import Romanoff.M3.K.Tab236

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp26 : segOK (decTabK tab232) drop232 ((D.data.gA.drop 232).take 4) tab236 drop236 = true := by decide +kernel
