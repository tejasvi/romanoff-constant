import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR8
import Romanoff.M3.K.TabR

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr9 : segROK (decTabK tabR8) ((D.data.gE.drop 8).take 1) tabR = true := by decide +kernel
