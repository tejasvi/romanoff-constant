import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab138
import Romanoff.M3.K.Tab146

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp8 : segOK (decTabK tab138) drop138 ((D.data.gA.drop 138).take 8) tab146 drop146 = true := by decide +kernel
