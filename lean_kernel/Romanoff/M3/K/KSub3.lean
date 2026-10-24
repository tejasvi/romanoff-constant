import RCert.M3.KFun
import Romanoff.M3.K.Tab289
import Romanoff.M3.K.Sub3

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem ksub3 : entsEqK (subK 3 (decTabK tab289)) (decTabK sub3) = true := by decide +kernel
