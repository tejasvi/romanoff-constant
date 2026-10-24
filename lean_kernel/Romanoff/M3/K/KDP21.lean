import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab212
import Romanoff.M3.K.Tab216

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp21 : segOK (decTabK tab212) drop212 ((D.data.gA.drop 212).take 4) tab216 drop216 = true := by decide +kernel
