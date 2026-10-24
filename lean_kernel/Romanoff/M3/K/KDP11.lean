import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab160
import Romanoff.M3.K.Tab167

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp11 : segOK (decTabK tab160) drop160 ((D.data.gA.drop 160).take 7) tab167 drop167 = true := by decide +kernel
