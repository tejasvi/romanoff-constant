import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR4
import Romanoff.M3.K.TabR5

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr5 : segROK (decTabK tabR4) ((D.data.gE.drop 4).take 1) tabR5 = true := by decide +kernel
