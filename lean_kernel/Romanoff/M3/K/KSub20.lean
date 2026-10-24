import RCert.M3.KFun
import Romanoff.M3.K.Tab289
import Romanoff.M3.K.Sub20

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem ksub20 : entsEqK (subK 20 (decTabK tab289)) (decTabK sub20) = true := by decide +kernel
