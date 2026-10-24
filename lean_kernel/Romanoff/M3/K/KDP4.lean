import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab99
import Romanoff.M3.K.Tab111

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp4 : segOK (decTabK tab99) drop99 ((D.data.gA.drop 99).take 12) tab111 drop111 = true := by decide +kernel
