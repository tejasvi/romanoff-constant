import RCert.M3.KFun
import Romanoff.M3.K.Tab289
import Romanoff.M3.K.Vals

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kvsA : Nat.beq (sumAK (decTabK tab289)) sA = true := by decide +kernel
