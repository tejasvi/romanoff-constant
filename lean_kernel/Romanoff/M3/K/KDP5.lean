import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab111
import Romanoff.M3.K.Tab121

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp5 : segOK (decTabK tab111) drop111 ((D.data.gA.drop 111).take 10) tab121 drop121 = true := by decide +kernel
