import RCert.M3.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kcb : subSorted (sortNat (bigOnly (D.data.recs.flatMap fun r => r.fs.map (·.1)))) (D.data.recs.map (·.n))
    = true := by decide +kernel
