import RCert.M3.Data
import RCert.M3.TeffLit

/-!
# M3, N version: the native checks (precompiled library, so `native_decide` runs compiled code)
-/

namespace R45.M3

theorem certOK_data : certOK D.data = true := by native_decide

theorem sumsOK_data : sumsOK D.data (runDP tab0 D.data.gA) = true := by native_decide

theorem teffD_eq : teffD D.data = teffLit := by native_decide

end R45.M3
