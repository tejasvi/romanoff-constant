import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR
import Romanoff.M3.K.Vals
import Romanoff.M3.K.BDs

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kb105 : bdChunkOK subsLit (decTabK tabR) r0a ((D.data.gB.drop 806).take 10) bd105 = true := by
  decide +kernel
