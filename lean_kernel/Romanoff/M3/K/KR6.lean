import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR5
import Romanoff.M3.K.TabR6

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr6 : segROK (decTabK tabR5) ((D.data.gE.drop 5).take 1) tabR6 = true := by decide +kernel
