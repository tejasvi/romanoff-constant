/-!
# Residue patterns of the classes `k mod l` modulo rotation (core Lean, list based)

For a prime `p ∣ l` and a residue `r mod p`, `maskP per p r` is the set of exponents `e < per` with `2^e ≡ r (mod p)`
(a bit mask).  The exclusion mask of a class `k mod l` is the union over `p ∣ l` of the masks of `k mod p`; `U_k` is its
complement (the exponents `e` with `k - 2^e` a unit mod `l`).  `k ↦ 2k` rotates the masks by one and every option table
is rotation invariant, so the distribution of the exclusion masks can be folded over the primes modulo rotation
(`foldOrbits`), as sorted association lists.
-/

namespace R45

/-- Bits `0 … per-1` set. -/
def full (per : Nat) : Nat := 2 ^ per - 1

/-- Rotate a `per`-bit mask by one (bit `e` moves to `e + 1 mod per`). -/
def rot1 (per x : Nat) : Nat := ((x <<< 1) ||| (x >>> (per - 1))) &&& full per

/-- The smallest of `x` and its rotations `rot1^[t] x`, `t ≤ per`. -/
def canon (per x : Nat) : Nat :=
  ((List.range per).foldl (fun (bc : Nat × Nat) _ => let y := rot1 per bc.2; (min bc.1 y, y)) (x, x)).1

/-- The exponents `e < per` with `2^e ≡ r (mod p)`, as a bit mask. -/
def maskP (per p r : Nat) : Nat :=
  (List.range per).foldl (fun acc e => if 2 ^ e % p = r then acc ||| (1 <<< e) else acc) 0

/-- `(mask, count)` for the residues `r < p`: each nonzero mask once, and the zero mask with its multiplicity. -/
def optsP (per p : Nat) : List (Nat × Nat) :=
  ((List.range p).filter fun r => maskP per p r != 0).map (fun r => (maskP per p r, 1)) ++
    [(0, ((List.range p).filter fun r => maskP per p r == 0).length)]

/-- Merge adjacent entries with equal keys (summing the counts). -/
def combine : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | [a] => [a]
  | a :: b :: L => if a.1 == b.1 then combine ((a.1, a.2 + b.2) :: L) else a :: combine (b :: L)
termination_by L => L.length

/-- Sort by key and merge equal keys. -/
def normalize (L : List (Nat × Nat)) : List (Nat × Nat) := combine (L.mergeSort fun a b => a.1 ≤ b.1)

/-- One step of the fold modulo rotation. -/
def foldStep (per : Nat) (L : List (Nat × Nat)) (opts : List (Nat × Nat)) : List (Nat × Nat) :=
  normalize (L.flatMap fun xc => opts.map fun mc => (canon per (xc.1 ||| mc.1), xc.2 * mc.2))

/-- The distribution of the exclusion masks modulo rotation over the primes `ps`. -/
def foldOrbits (per : Nat) (ps : List Nat) : List (Nat × Nat) :=
  ps.foldl (fun L p => foldStep per L (optsP per p)) [(0, 1)]

/-- Number of set bits among `0 … per-1`. -/
def popcount (per x : Nat) : Nat := (List.range per).foldl (fun acc e => if x.testBit e then acc + 1 else acc) 0

/-- `n(c) = #{e < per : e ∈ U, (e + c) mod per ∈ U}` for `c < per`. -/
def nShift (per u : Nat) : List Nat :=
  (List.range per).map fun c =>
    (List.range per).foldl (fun acc e => if u.testBit e && u.testBit ((e + c) % per) then acc + 1 else acc) 0

end R45
