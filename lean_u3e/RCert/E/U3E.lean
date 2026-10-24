import RCert.E.Params
import RCert.M3E.Defs

/-!
# U3e: tables at period 3960 (core Lean)

* `tailA α c = Σ_{g ∈ divE, g ∣ c} g α_g`, `teffA tab α = tab + tailA α` (3960 entries): the class-(c) tail in alpha form;
* `tabB B c = Σ_{g ∈ divE, g ∣ c} B_g`: a table in divisor form;
* `ngOf n g = Σ_{c, g ∣ c} n(c)` (one pass).
-/

open R45

namespace R45.U3E

/-- `Σ_{g ∈ divE, g ∣ c} g α_g`. -/
def tailA (α : Nat → Rat) (c : Nat) : Rat :=
  ((R45.M3E.divE.filter fun g => c % g == 0).map fun (g : Nat) => (g : Rat) * α g).sum

/-- The table `tab(c) + Σ_{g ∣ c} g α_g` (`c < 3960`). -/
def teffA (tab : List Rat) (α : Nat → Rat) : List Rat :=
  (List.range 3960).map fun c => tab.getD c 0 + tailA α c

/-- The table in divisor form: `Σ_{g ∈ divE, g ∣ c} B_g` (`c < 3960`). -/
def tabB (B : Nat → Rat) : List Rat :=
  (List.range 3960).map fun c => ((R45.M3E.divE.filter fun g => c % g == 0).map B).sum

/-- `Σ_i [g ∣ k + i] n(i)` in one pass. -/
def ngAux (g : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | k, x :: xs => (if k % g == 0 then x else 0) + ngAux g (k + 1) xs

/-- `N_g = Σ_{c, g ∣ c} n(c)`. -/
def ngOf (n : List Nat) (g : Nat) : Nat := ngAux g 0 n

end R45.U3E
