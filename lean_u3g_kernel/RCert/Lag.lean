import RCert.Patt

/-!
# The Lagrangian bound with a uniform budget multiplier (core Lean, exact rationals)

For an orbit `u` of classes (weight `d_u = #classes / l`, `s_u = |U|`, `n_u(c)`):
`min_{0 ≤ Y ≤ Ymax_u} [w_u φ(1 + Y/s_u) + d_u μ Y]`, `w_u = norm d_u s_u`, `Ymax_u = Σ_c CAP κ n_u(c) Teff(c)`,
with `φ` the piecewise-linear interpolation of `1/x` at the integers; the minimum of this convex piecewise-linear function
is attained at `0`, `Ymax_u` or a breakpoint `s_u (j - 1)`.  Bound `= Σ_u min_u - μ C1 κ Σ_c N(c) Teff(c)`.
-/

namespace R45

/-- `φ(D)`, `D ≥ 1`: `1/j` at `D = j`, `(2j + 1 - D)/(j(j+1))` for `j < D < j + 1`. -/
def phiQ (D : Rat) : Rat :=
  let j : Nat := D.floor.toNat
  if (j : Rat) = D then 1 / (j : Rat) else (2 * (j : Rat) + 1 - D) / ((j : Rat) * ((j : Rat) + 1))

/-- The data of one orbit: `(count, s, n(0..per-1))`. -/
structure Orb where
  cnt : Nat
  s : Nat
  n : List Nat

/-- The orbits with nonempty `U` from the fold. -/
def orbits (per : Nat) (ps : List Nat) : List Orb :=
  (foldOrbits per ps).filterMap fun xc =>
    let u := full per ^^^ xc.1
    if u = 0 then none else some ⟨xc.2, popcount per u, nShift per u⟩

/-- Parameters of the evaluation. -/
structure Par where
  per : Nat
  ell : Nat
  phil : Nat
  cap : Rat
  c1 : Rat
  kap : Rat
  norm : Rat
  teff : List Rat
  mu : Rat

/-- `Σ_c n(c) t(c)`. -/
def dotNQ (n : List Nat) (t : List Rat) : Rat := (n.zip t).foldl (fun acc nt => acc + (nt.1 : Rat) * nt.2) 0

/-- The box of one class: `Ymax = CAP κ Σ_c n(c) Teff(c)`. -/
def ymaxQ (P : Par) (n : List Nat) : Rat := P.cap * P.kap * dotNQ n P.teff

/-- One class (weight `1/l`): `g(Y) = w φ(1 + Y/s) + μ Y / l`, `w = norm s / l`. -/
def gQ (P : Par) (s : Nat) (Y : Rat) : Rat :=
  P.norm * (1 / (P.ell : Rat)) * (s : Rat) * phiQ (1 + Y / (s : Rat)) + (1 / (P.ell : Rat)) * P.mu * Y

/-- The candidates `0`, `Ymax`, `s j ≤ Ymax` (`j ≤ ⌊Ymax/s⌋ + 1`). -/
def candsQ (s : Nat) (ymax : Rat) : List Rat :=
  0 :: ymax :: ((List.range ((ymax / (s : Rat)).floor.toNat + 2)).filterMap fun (j : Nat) =>
    if (s : Rat) * (j : Rat) ≤ ymax then some ((s : Rat) * (j : Rat)) else none)

/-- The minimum of `gQ` over the candidates (one class). -/
def minQ (P : Par) (s : Nat) (ymax : Rat) : Rat := (candsQ s ymax).foldl (fun best y => min best (gQ P s y)) (gQ P s 0)

/-- `N(c) = Σ_u (cnt_u / l) n_u(c)`. -/
def ncQ (P : Par) (os : List Orb) (c : Nat) : Rat :=
  os.foldl (fun acc o => acc + (o.cnt : Rat) / (P.ell : Rat) * ((o.n.getD c 0 : Nat) : Rat)) 0

/-- The certified bound: `Σ_u cnt_u min_u - μ C1 κ Σ_c N(c) Teff(c)`. -/
def lagBound (P : Par) (os : List Orb) : Rat :=
  os.foldl (fun acc o => acc + (o.cnt : Rat) * minQ P o.s (ymaxQ P o.n)) 0 -
    P.mu * P.c1 * P.kap * ((List.range P.per).zip P.teff).foldl (fun acc ct => acc + ncQ P os ct.1 * ct.2) 0

end R45
