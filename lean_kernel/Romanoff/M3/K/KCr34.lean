import RCert.M3.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kcr34 : R45.M3.D.recs34.all recOK = true := by decide +kernel
