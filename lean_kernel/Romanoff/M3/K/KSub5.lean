import RCert.M3.KFun
import Romanoff.M3.K.Tab289
import Romanoff.M3.K.Sub5

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem ksub5 : entsEqK (subK 5 (decTabK tab289)) (decTabK sub5) = true := by decide +kernel
