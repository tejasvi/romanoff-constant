import RCert.Params45

/-!
# U3a: the evaluation with the class-(c) tail in alpha form (core Lean only)

The class-(c) part of `T(c)` is `Σ_{g ∣ 120, g ∣ c} g α_g` with `α_g ≥ 0`, `Σ_g α_g ≤ R0t` (unknown `α`).
For a table `tab` (the classes (a), (b) and the computed remainders) the box of an orbit is
`Ymax(α) = 8 κ (D + Σ_g α_g g N_g)`, `D = Σ_c n(c) tab(c)`, `N_g = Σ_{c < 120, g ∣ c} n(c)`.
Pintz's inequality `φ(1 + Y/s) ≥ (2j + 1 - 1 - Y/s)/(j(j+1))` (any integer `j ≥ 1`) makes the orbit's term affine in `α`:
`w (2 j s - Ymax(α)) / (j (j+1))`, `w = cnt · norm / l`.  `vecD` is its constant term followed by the coefficients of
`α_g` (`g ∈ div120`); `j` is the index at `α = R0t e_120`.  The bound is `A0 - (R0t + δ) max(0, max_g A_g)`.
-/

open R45 R45.P45

namespace R45.U3

/-- The divisors of 120. -/
def div120 : List Nat := [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]

/-- `Σ_{g ∈ div120, g ∣ c} g α_g`. -/
def tailA (α : Nat → Rat) (c : Nat) : Rat :=
  ((div120.filter fun g => c % g == 0).map fun (g : Nat) => (g : Rat) * α g).sum

/-- The table `tab(c) + Σ_{g ∣ c} g α_g` (`c < 120`). -/
def teffA (tab : List Rat) (α : Nat → Rat) : List Rat :=
  (List.range 120).map fun c => tab.getD c 0 + tailA α c

/-- `Σ_i [g ∣ k + i] n(i)` in one pass. -/
def ngAux (g : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | k, x :: xs => (if k % g == 0 then x else 0) + ngAux g (k + 1) xs

/-- `N_g = Σ_{c, g ∣ c} n(c)`. -/
def ngOf (n : List Nat) (g : Nat) : Nat := ngAux g 0 n

/-- The Pintz index of an orbit at `α = R0t e_120` (only `c = 0` is a multiple of 120), from `D = Σ_c n(c) tab(c)`. -/
def jOf (R0t : Rat) (o : Orb) (D : Rat) : Nat :=
  max 1 ((1 + 8 * kap * (D + 120 * R0t * ((o.n.getD 0 0 : Nat) : Rat)) / (o.s : Rat)).floor.toNat)

/-- The affine minorant of one orbit: constant term, then the coefficients of `α_g`, `g ∈ div120`. -/
def vecD (R0t : Rat) (o : Orb) (D : Rat) : List Rat :=
  let w : Rat := (o.cnt : Rat) * (norm * (1 / (ellN : Rat)))
  let j : Rat := (jOf R0t o D : Rat)
  (w * (2 * j * (o.s : Rat) - 8 * kap * D) / (j * (j + 1))) ::
    div120.map fun (g : Nat) => w * (8 * kap * ((g : Rat) * (ngOf o.n g : Rat))) / (j * (j + 1))

/-- Entrywise sum. -/
def addV (a b : List Rat) : List Rat := List.zipWith (· + ·) a b

/-- The zero vector (17 entries). -/
def zeroV : List Rat := List.replicate 17 0

/-- `(A0, A_g)` summed over an orbit list. -/
def valU3 (tab : List Rat) (R0t : Rat) (os : List Orb) : List Rat :=
  os.foldl (fun acc o => addV acc (vecD R0t o (dotNQ o.n tab))) zeroV

/-- `A0 - (R0t + δ) max(0, max_g A_g)`. -/
def boundU3 (R0t δ : Rat) (v : List Rat) : Rat :=
  v.headD 0 - (R0t + δ) * v.tail.foldl max 0

end R45.U3
