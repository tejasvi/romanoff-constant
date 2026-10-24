import Romanoff.SingSeries
import Romanoff.ETail

/-!
# M4 interface, part 2: the limits used by the final assembly (frozen as a `Prop`)

`L = ⌊log₂ N⌋`: `120/L → 0`, `L²/N → 0`, and (from `R0Bound`, via `E(L) = o(L)`) `(L/120 + 1) E(L)/log² N → 0`.
-/

open Filter Topology

namespace Romanoff

/-- (E) The three limits of the assembly. -/
def LimitFacts : Prop :=
  Tendsto (fun N : ℕ => (120 : ℝ) / (Nat.log 2 N : ℝ)) atTop (𝓝 0) ∧
  Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) ^ 2 / N) atTop (𝓝 0) ∧
  (R0Bound → Tendsto (fun N : ℕ => ((Nat.log 2 N : ℝ) / 120 + 1) * EL ell (Nat.log 2 N) / Real.log N ^ 2)
    atTop (𝓝 0))

end Romanoff
