import RCert.M3.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kcm : (sortedLT (D.data.gA.map (·.t)) && sortedLT (D.data.gE.map (·.t)) && sortedLT (D.data.gB.map (·.1.t)) &&
    D.data.gE.all (fun g => !(D.data.gA.map (·.t)).contains g.t) &&
    D.data.gE.all (fun g => g.ps.all fun p => ellPs.contains p) &&
    (D.data.gA ++ D.data.gE).all (fun g => g.t ≤ 300) && D.data.gB.all (fun g => 300 < g.1.t && g.1.t ≤ 1200)) = true := by
  decide +kernel
