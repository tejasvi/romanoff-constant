import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab69

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp1 : segOK tab0 0 ((D.data.gA.drop 0).take 69) tab69 drop69 = true := by decide +kernel
