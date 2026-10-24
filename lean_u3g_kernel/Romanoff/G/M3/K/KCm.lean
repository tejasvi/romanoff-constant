import RCert.M3G.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R45.M3G.KS

theorem kcm : (sortedLT (R45.M3G.D.data.gA.map (·.t)) && sortedLT (R45.M3G.D.data.gE.map (·.t)) && sortedLT (R45.M3G.D.data.gB.map (·.1.t)) &&
    R45.M3G.D.data.gA.all (fun g => g.ps.all fun p => !R45.M3G.ellPs.contains p) &&
    R45.M3G.D.data.gE.all (fun g => g.ps.all fun p => R45.M3G.ellPs.contains p) &&
    (R45.M3G.D.data.gA ++ R45.M3G.D.data.gE).all (fun g => g.t ≤ 300) && R45.M3G.D.data.gB.all (fun g => 300 < g.1.t && g.1.t ≤ 1200)) = true := by
  decide +kernel

end R45.M3G.KS
