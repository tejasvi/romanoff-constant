import RCert.Lag

/-!
# Kernel-reducible computations for the fold and the orbit list (core Lean only)

Structural merge sort with fuel and structural combine (`normK`, `mergeRuns`), the products of a fold step (`prodK`),
the fast `nShift` (`nFast`: base-256 digits of `spread u * rspread u`), the orbit map `orbF` and the stored-orbit
decoder `orbOf`, and the literal check `strictPos`.  The lemmas are in `K45.Norm`, `K45.NFast`, `K45.Exact`, `K45.OrbF`.
-/

namespace K45

open R45

deriving instance DecidableEq for R45.Orb

/-- Merge two lists by key (fuel at least the total length). -/
def mergeF : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, as, bs => as ++ bs
  | _ + 1, [], bs => bs
  | _ + 1, a :: as, [] => a :: as
  | n + 1, a :: as, b :: bs => if a.1 ≤ b.1 then a :: mergeF n as (b :: bs) else b :: mergeF n (a :: as) bs

/-- Merge adjacent runs pairwise. -/
def mergePairs : List (List (Nat × Nat)) → List (List (Nat × Nat))
  | a :: b :: rest => mergeF (a.length + b.length) a b :: mergePairs rest
  | l => l

/-- Bottom-up merge sort of a list of runs (fuel = number of rounds). -/
def msortK : Nat → List (List (Nat × Nat)) → List (Nat × Nat)
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [l] => l
  | n + 1, a :: b :: rest => msortK n (mergePairs (a :: b :: rest))

/-- Merge equal adjacent keys (summing the counts), after `a`. -/
def combineS : Nat × Nat → List (Nat × Nat) → List (Nat × Nat)
  | a, [] => [a]
  | a, b :: L => if a.1 = b.1 then combineS (a.1, a.2 + b.2) L else a :: combineS b L

def combineAll : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | a :: L => combineS a L

/-- Sort the runs together and merge equal keys. -/
def mergeRuns (ls : List (List (Nat × Nat))) : List (Nat × Nat) := combineAll (msortK 40 ls)

/-- Sort and merge equal keys. -/
def normK (L : List (Nat × Nat)) : List (Nat × Nat) := mergeRuns (L.map fun x => [x])

/-- The products of one fold step (as in `foldStep`, before normalizing). -/
def prodK (per : Nat) (L opts : List (Nat × Nat)) : List (Nat × Nat) :=
  L.flatMap fun xc => opts.map fun mc => (canon per (xc.1 ||| mc.1), xc.2 * mc.2)

/-- Consecutive keys increase strictly and every count is positive. -/
def strictPos : List (Nat × Nat) → Bool
  | [] => true
  | [a] => decide (0 < a.2)
  | a :: b :: L => decide (0 < a.2) && decide (a.1 < b.1) && strictPos (b :: L)

def spread (per u : Nat) : Nat := (List.range per).foldl (fun acc e => if u.testBit e then acc + 256 ^ e else acc) 0

def rspread (per u : Nat) : Nat :=
  (List.range per).foldl (fun acc e => if u.testBit e then acc + 256 ^ (per - 1 - e) else acc) 0

/-- Base-256 digit `j`. -/
def dig (p j : Nat) : Nat := (p >>> (8 * j)) &&& 255

def nFromProd (per p : Nat) : List Nat := (List.range per).map fun c => dig p (per - 1 - c) + dig p (2 * per - 1 - c)

def nFast (per u : Nat) : List Nat := nFromProd per (spread per u * rspread per u)

/-- Decode one stored orbit `z = cnt·2^847 + s·2^840 + Σ_c n(c)·2^(7c)`. -/
def orbOf (z : Nat) : Orb := ⟨z >>> 847, (z >>> 840) &&& 127, (List.range 120).map fun c => (z >>> (7 * c)) &&& 127⟩

/-- `orbits`' map at `per = 120` with `nFast`. -/
def orbF (xc : Nat × Nat) : Option Orb :=
  if full 120 ^^^ xc.1 = 0 then none
  else some ⟨xc.2, (nFast 120 (full 120 ^^^ xc.1)).headD 0, nFast 120 (full 120 ^^^ xc.1)⟩

end K45
