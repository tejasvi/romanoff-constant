import RCert.G.BLit
import RCert.M3G.TeffLit

/-! U3g/V4g, N version: the divisor form of the M3 table (native check, precompiled library). -/

namespace R45.U3G

theorem tabB_BLit_eq : tabB BLit = (List.range 27720).map fun c =>
    R45.M3G.teffLit.getD c 0 - ((Nat.gcd c 27720 : Nat) : Rat) * R45.M3G.R0tLit := by
  native_decide

end R45.U3G
