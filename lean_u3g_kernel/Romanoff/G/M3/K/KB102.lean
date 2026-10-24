import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.TabR
import Romanoff.G.M3.K.Vals
import Romanoff.G.M3.K.BDs

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kb102 : R45.M3G.bdChunkOKG subsLit (decTabK tabR) r0a ((R45.M3G.D.data.gB.drop 785).take 6) bd102 = true := by
  decide +kernel

end R45.M3G.KS
