import RCert.E.BLit
import RCert.M3E.TeffLit

/-! U3e, N version: the divisor form of the M3 table (native check, precompiled library). -/

namespace R45.U3E

theorem tabB_BLit_eq : tabB BLit = (List.range 3960).map fun c =>
    R45.M3E.teffLit.getD c 0 - ((Nat.gcd c 3960 : Nat) : Rat) * R45.M3E.R0tLit := by
  native_decide

end R45.U3E
