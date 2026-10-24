import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab121
import Romanoff.M3.K.Tab130

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp6 : segOK (decTabK tab121) drop121 ((D.data.gA.drop 121).take 9) tab130 drop130 = true := by decide +kernel
