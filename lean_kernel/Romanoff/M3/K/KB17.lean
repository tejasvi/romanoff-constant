import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR
import Romanoff.M3.K.Vals
import Romanoff.M3.K.BDs

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kb17 : bdChunkOK subsLit (decTabK tabR) r0a ((D.data.gB.drop 129).take 8) bd17 = true := by
  decide +kernel
