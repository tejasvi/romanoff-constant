import RCert.M3G.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kcs : sortedLT (R45.M3G.D.data.recs.map (·.n)) = true := by decide +kernel

end R45.M3G.KS
