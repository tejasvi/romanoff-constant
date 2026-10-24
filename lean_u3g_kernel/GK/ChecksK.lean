import GK.Checks

/-! k45g: the data checks, evaluated by the kernel. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R45.GK

theorem patsOK_true : patsOK = true := by decide +kernel

theorem o41OK_true : o41OK = true := by decide +kernel

theorem fibOK_true : fibOK = true := by decide +kernel

theorem sigOKall_true : sigOKall = true := by decide +kernel

theorem wtOK_true : wtOK = true := by decide +kernel

end R45.GK
