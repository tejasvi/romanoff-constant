import Romanoff.E.M3.Sound
import RCert.M3E.NCheck

/-!
# M3 at period 3960 (U3e modulus), N version: `TBound teffLit`

The checks `certOK_data`, `sumsOK_data`, `teffD_eq` are `native_decide` proofs in RCert/M3E/NCheck.lean.
-/

namespace Romanoff.E.M3

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD
open R45.M3E

/-- The certified `T(c)` bounds at period 3960. -/
def teffCert : List ℚ := teffD D.data

theorem teffD_eq_teffOf (D : Data) : teffD D = teffOf D (runDP tab0 D.gA) (runDrop tab0 D.gA)
    (runDP (runDP tab0 D.gA) D.gE) (bsOf D (runDP tab0 D.gA) (runDP (runDP tab0 D.gA) D.gE)) := by
  unfold teffD tabTD tabR
  rw [Romanoff.M3.runDPD_eq]
  simp only [Nat.zero_add]

theorem tboundCert (h5 : R0Bound) : TBound teffCert := by
  rw [teffCert, teffD_eq_teffOf]
  exact tbound_of D.data certOK_data sumsOK_data h5

theorem teffCert_eq : teffCert = teffLit := teffD_eq

theorem tboundLit (h5 : R0Bound) : TBound teffLit := teffCert_eq ▸ tboundCert h5

end Romanoff.E.M3
