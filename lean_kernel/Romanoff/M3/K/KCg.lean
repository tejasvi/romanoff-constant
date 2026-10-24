import RCert.M3.Data

open R45.M3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kcg : D.data.groups.all grpOK = true := by decide +kernel
