import RCert.M3.KFun
import RCert.M3G.KFun
import RCert.M3G.Data
import Romanoff.G.M3.K.Vals
import Romanoff.G.M3.K.BDs

open R45.M3 R45.M3G.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kv96 : (R45.M3G.valsOK R45.M3G.D.data acc1 sA sB dT bsLit vals96 && Nat.ble sA (piUp R45.M3G.D.data.gA)) = true := by
  decide +kernel

end R45.M3G.KS
