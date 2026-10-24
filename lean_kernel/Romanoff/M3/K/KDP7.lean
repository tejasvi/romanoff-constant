import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab130
import Romanoff.M3.K.Tab138

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp7 : segOK (decTabK tab130) drop130 ((D.data.gA.drop 130).take 8) tab138 drop138 = true := by decide +kernel
