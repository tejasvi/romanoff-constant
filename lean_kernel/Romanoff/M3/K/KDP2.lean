import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab69
import Romanoff.M3.K.Tab86

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp2 : segOK (decTabK tab69) drop69 ((D.data.gA.drop 69).take 17) tab86 drop86 = true := by decide +kernel
