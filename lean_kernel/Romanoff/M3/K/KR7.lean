import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR6
import Romanoff.M3.K.TabR7

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr7 : segROK (decTabK tabR6) ((D.data.gE.drop 6).take 1) tabR7 = true := by decide +kernel
