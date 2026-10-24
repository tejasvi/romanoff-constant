import RCert.Cert45
import RCert.M3.TeffLit

/-!
# K track of the certificate value: the per-chunk sums (core Lean, evaluated by the kernel)

For a chunk of orbits (`List Orb`, with `s` and `n` precomputed), one pass computes
`(Σ cnt·gQ_U2(s, Ymax), Σ cnt·minQ_v3(s, Ymax), Σ cnt·D)` with `D = Σ_c n(c) teff(c)` and `Ymax = 8 κ D` (the same for
U2 and v3).  For U2 (`μ = 0`) the minimum over the box is attained at `Ymax` (`minQ_mu0`, Romanoff/CertKGlue.lean).
-/

namespace R45.K45L

open R45 R45.D45 R45.P45

def PU2 : Par := parOf R45.M3.teffLit 8 0
def PV3 : Par := parOf R45.M3.teffLit C1v3 muV3

/-- One orbit with its `D = dotNQ n teffLit`. -/
def stepD (acc : Rat × Rat × Rat) (o : Orb) (D : Rat) : Rat × Rat × Rat :=
  (acc.1 + (o.cnt : Rat) * gQ PU2 o.s (8 * kap * D),
   acc.2.1 + (o.cnt : Rat) * minQ PV3 o.s (8 * kap * D),
   acc.2.2 + (o.cnt : Rat) * D)

def chunkVals (os : List Orb) : Rat × Rat × Rat :=
  os.foldl (fun acc o => stepD acc o (dotNQ o.n R45.M3.teffLit)) (0, 0, 0)

/-- Compare a triple of sums with literal bounds. -/
def tripleOK (r : Rat × Rat × Rat) (loU loV hiD : Rat) : Bool :=
  decide (loU ≤ r.1) && decide (loV ≤ r.2.1) && decide (r.2.2 ≤ hiD)

/-- The kernel check of one chunk against rounded literal bounds. -/
def chunkOK (os : List Orb) (loU loV hiD : Rat) : Bool := tripleOK (chunkVals os) loU loV hiD

end R45.K45L
