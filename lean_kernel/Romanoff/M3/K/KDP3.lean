import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab86
import Romanoff.M3.K.Tab99

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp3 : segOK (decTabK tab86) drop86 ((D.data.gA.drop 86).take 13) tab99 drop99 = true := by decide +kernel
