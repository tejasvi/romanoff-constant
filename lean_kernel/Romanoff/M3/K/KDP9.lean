import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab146
import Romanoff.M3.K.Tab153

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp9 : segOK (decTabK tab146) drop146 ((D.data.gA.drop 146).take 7) tab153 drop153 = true := by decide +kernel
