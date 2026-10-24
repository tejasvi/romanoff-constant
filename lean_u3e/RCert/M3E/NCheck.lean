import RCert.M3E.Data
import RCert.M3E.TeffLit

/-!
# M3 at period 3960 (U3e modulus), N version: the native checks (precompiled library, compiled `native_decide`)
-/

namespace R45.M3E

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD

theorem certOK_data : certOK D.data = true := by native_decide

theorem sumsOK_data : sumsOK D.data (runDP tab0 D.data.gA) = true := by native_decide

theorem teffD_eq : teffD D.data = teffLit := by native_decide

theorem R0tD_eq : R0tD D.data = R0tLit := by native_decide

end R45.M3E
