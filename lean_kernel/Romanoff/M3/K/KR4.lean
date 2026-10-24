import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR3
import Romanoff.M3.K.TabR4

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr4 : segROK (decTabK tabR3) ((D.data.gE.drop 3).take 1) tabR4 = true := by decide +kernel
