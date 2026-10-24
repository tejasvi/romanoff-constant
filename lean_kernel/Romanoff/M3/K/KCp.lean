import RCert.M3.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kcp : primeOK (D.data.recs.map (·.n)) (D.data.groups.flatMap (·.ps)) = true := by decide +kernel
