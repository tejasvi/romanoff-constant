import RCert.M3G.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kcr14 : R45.M3G.D.recs14.all recOK = true := by decide +kernel

end R45.M3G.KS
