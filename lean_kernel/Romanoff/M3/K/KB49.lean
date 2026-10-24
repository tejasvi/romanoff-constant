import RCert.M3.KFun
import RCert.M3.Data
import Romanoff.M3.K.TabR
import Romanoff.M3.K.Vals
import Romanoff.M3.K.BDs

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kb49 : bdChunkOK subsLit (decTabK tabR) r0a ((D.data.gB.drop 372).take 7) bd49 = true := by
  decide +kernel
