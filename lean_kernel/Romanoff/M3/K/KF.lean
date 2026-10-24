import RCert.M3.KFun
import RCert.M3.Data
import RCert.M3.TeffLit
import Romanoff.M3.K.Vals
import Romanoff.M3.K.BDs

open R45.M3 R45.M3.K

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kf : (teffOfV D.data acc1 sA sB dT r0a bsLit == teffLit) && Nat.ble sA (piUp D.data.gA) = true := by
  decide +kernel
