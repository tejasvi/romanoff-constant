import RCert.M3.KFun
import Romanoff.M3.K.TabR
import Romanoff.M3.K.Vals

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kvr0a : Nat.beq (sumRK 1 (decTabK tabR)) r0a = true := by decide +kernel
