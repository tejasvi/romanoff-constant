import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR7
import Romanoff.M3.K.TabR8

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kr8 : segROK (decTabK tabR7) ((D.data.gE.drop 7).take 1) tabR8 = true := by decide +kernel
