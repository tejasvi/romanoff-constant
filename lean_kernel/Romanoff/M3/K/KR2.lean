import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR1
import Romanoff.M3.K.TabR2

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr2 : segROK (decTabK tabR1) ((D.data.gE.drop 1).take 1) tabR2 = true := by decide +kernel
