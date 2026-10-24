import Romanoff.M3.Sound
import RCert.M3.NCheck

/-!
# M3, N version: `teffCert` and `tboundCert`

The three checks `certOK_data`, `sumsOK_data`, `teffD_eq` are `native_decide` proofs in `RCert/M3/NCheck.lean`.
-/

namespace Romanoff.M3

open R45.M3

/-- The certified `T(c)` bounds: `T_a(c) + prune(c) + T_b(c) + gcd(c, 120) · R0tail`. -/
def teffCert : List ℚ := teffD D.data

theorem teffD_eq_teffOf (D : Data) : teffD D = teffOf D (runDP tab0 D.gA) (runDrop tab0 D.gA)
    (runDP (runDP tab0 D.gA) D.gE) (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)) := by
  unfold teffD tabTD tabR
  rw [runDPD_eq]
  simp only [Nat.zero_add]

theorem tboundCert (h5 : R0Bound) : TBound teffCert := by
  rw [teffCert, teffD_eq_teffOf]
  exact tbound_of D.data certOK_data sumsOK_data h5

/-- The same values as literals (`RCert/M3/TeffLit.lean`). -/
theorem teffCert_eq : teffCert = teffLit := teffD_eq

theorem tboundLit (h5 : R0Bound) : TBound teffLit := teffCert_eq ▸ tboundCert h5

end Romanoff.M3
