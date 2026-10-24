import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR2
import Romanoff.M3.K.TabR3

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr3 : segROK (decTabK tabR2) ((D.data.gE.drop 2).take 1) tabR3 = true := by decide +kernel
