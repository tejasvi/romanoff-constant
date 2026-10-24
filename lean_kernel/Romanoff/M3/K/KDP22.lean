import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.Tab216
import Romanoff.M3.K.Tab220

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kdp22 : segOK (decTabK tab216) drop216 ((D.data.gA.drop 216).take 4) tab220 drop220 = true := by decide +kernel
