import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab289
import Romanoff.M3.K.TabR1

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr1 : segROK (decTabK tab289) ((D.data.gE.drop 0).take 1) tabR1 = true := by decide +kernel
