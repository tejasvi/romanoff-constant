/-!
# M3 checker: certified primes, exact orders, the lcm DP and the class sums (core Lean, natural numbers only)

All weights are fixed-point numerators over `SC = 2^64`.  A DP table is a list of entries `(L, a, b)`: `a` is a lower and
`b` an upper bound for `SC ·` the total weight of the subsets with lcm `L ≤ LMAX`.  Lower values round down, upper values
round up.  Soundness never depends on the order of the entries; sorting only keeps the tables small.
-/

namespace R45.M3

/-- The fixed-point scale. -/
def SC : Nat := 2 ^ 64
/-- The DP cut-off: subsets with lcm above `LMAX` are dropped (their mass is bounded separately). -/
def LMAX : Nat := 3000000
/-- The period. -/
def PER : Nat := 120
/-- Primes below `SMALL` are certified by trial division. -/
def SMALL : Nat := 65536

/-! ## Modular powers and trial division -/

/-- `acc * b ^ e % m` by binary powering, `fuel ≥` the bit length of `e`. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e = 0 then acc else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

/-- `b ^ e % m`. -/
def powMod (b e m : Nat) : Nat := powModAux m (Nat.log2 e + 1) (b % m) e (1 % m)

/-- Trial division by `d, d + 1, …` while `d * d ≤ n`. -/
def tdLoop (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else tdLoop n fuel (d + 1)

/-- `n` is prime, by trial division (used for `n < SMALL`). -/
def tdPrime (n : Nat) : Bool := 2 ≤ n && tdLoop n n 2

/-- `∏ q ^ e` over a factor list. -/
def prodPow : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: fs => q ^ e * prodPow fs

/-! ## Pratt certificates -/

/-- A Pratt record: `n - 1 = ∏ q ^ e`, witness `a`. -/
structure PRec where
  n : Nat
  a : Nat
  fs : List (Nat × Nat)

/-- The local checks of one record (the factors `q ≥ SMALL` must be records themselves, checked globally). -/
def recOK (r : PRec) : Bool :=
  3 ≤ r.n && prodPow r.fs == r.n - 1 && powMod r.a (r.n - 1) r.n == 1 &&
    r.fs.all (fun qe => 1 ≤ qe.2 && powMod r.a ((r.n - 1) / qe.1) r.n != 1 &&
      (if qe.1 < SMALL then tdPrime qe.1 else true))

/-- Strictly increasing. -/
def sortedLT : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: l => x < y && sortedLT (y :: l)

/-- Merge two strictly increasing lists into one, dropping duplicates. -/
def mergeNat : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => mergeNatIns x (mergeNat xs) ys
where
  mergeNatIns (x : Nat) (rec : List Nat → List Nat) : List Nat → List Nat
    | [] => x :: rec []
    | y :: ys => if x < y then x :: rec (y :: ys) else if y < x then y :: mergeNatIns x rec ys else x :: rec ys

/-- Bottom-up merge of a list of sorted lists (fuel = number of rounds; leftovers are merged one by one). -/
def mergePairsNat : List (List Nat) → List (List Nat)
  | l1 :: l2 :: ls => mergeNat l1 l2 :: mergePairsNat ls
  | ls => ls

def mergeAllNat : Nat → List (List Nat) → List Nat
  | _, [] => []
  | _, [l] => l
  | 0, ls => ls.foldl mergeNat []
  | fuel + 1, ls => mergeAllNat fuel (mergePairsNat ls)

/-- Sort and deduplicate. -/
def sortNat (l : List Nat) : List Nat := mergeAllNat 64 (l.map fun x => [x])

/-- Every element of the strictly increasing `xs` occurs in the strictly increasing `ys` (linear scan). -/
def subSorted : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then subSorted xs ys else if y < x then subSorted (x :: xs) ys else false

/-- A prime is certified by trial division (`< SMALL`) or listed among the records (`≥ SMALL`, checked by `subSorted`). -/
def bigOnly (l : List Nat) : List Nat := l.filter fun q => SMALL ≤ q

/-- The global Pratt check: records sorted by `n`, each record locally valid, every big factor is a record. -/
def prattOK (recs : List PRec) : Bool :=
  sortedLT (recs.map (·.n)) && recs.all recOK &&
    subSorted (sortNat (bigOnly (recs.flatMap fun r => r.fs.map (·.1)))) (recs.map (·.n))

/-- A prime of the lists is certified: trial division below `SMALL`, else it is a record. -/
def primeOK (recN : List Nat) (ps : List Nat) : Bool :=
  ps.all (fun p => if p < SMALL then tdPrime p else true) && subSorted (sortNat (bigOnly ps)) recN

/-! ## Groups: primes of one exact order -/

/-- A group: order `t`, the factorization of `t`, the primes of exact order `t`. -/
structure Grp where
  t : Nat
  tfac : List (Nat × Nat)
  ps : List Nat

/-- Exact order `t` of `2` modulo each prime of the group. -/
def grpOK (g : Grp) : Bool :=
  1 ≤ g.t && prodPow g.tfac == g.t && g.tfac.all (fun re => 1 ≤ re.2 && tdPrime re.1) && sortedLT g.ps &&
    g.ps.all (fun p => 3 ≤ p && powMod 2 g.t p == 1 && g.tfac.all fun re => powMod 2 (g.t / re.1) p != 1)

/-! ## Fixed-point weights -/

/-- `⌈SC / (p - 2)⌉` and `⌊SC / (p - 2)⌋`. -/
def fUp (p : Nat) : Nat := (SC + p - 3) / (p - 2)
def fLo (p : Nat) : Nat := SC / (p - 2)

def mulUp (x y : Nat) : Nat := (x * y + SC - 1) / SC
def mulLo (x y : Nat) : Nat := x * y / SC

/-- `SC · (∏ (1 + 1/(p-2)) - 1)`, rounded up / down. -/
def eUp (ps : List Nat) : Nat := ps.foldl (fun acc p => mulUp acc (SC + fUp p)) SC - SC
def eLo (ps : List Nat) : Nat := ps.foldl (fun acc p => mulLo acc (SC + fLo p)) SC - SC

/-! ## The DP -/

/-- A table entry. -/
structure Ent where
  L : Nat
  a : Nat
  b : Nat

/-- Merge two tables (sorted by `L`), adding the weights of equal keys. -/
def mergeE : List Ent → List Ent → List Ent
  | [], ys => ys
  | x :: xs, ys => mergeEIns x (mergeE xs) ys
where
  mergeEIns (x : Ent) (rec : List Ent → List Ent) : List Ent → List Ent
    | [] => x :: rec []
    | y :: ys =>
      if x.L < y.L then x :: rec (y :: ys)
      else if y.L < x.L then y :: mergeEIns x rec ys
      else ⟨x.L, x.a + y.a, x.b + y.b⟩ :: rec ys

def mergePairsE : List (List Ent) → List (List Ent)
  | l1 :: l2 :: ls => mergeE l1 l2 :: mergePairsE ls
  | ls => ls

def mergeAllE : Nat → List (List Ent) → List Ent
  | _, [] => []
  | _, [l] => l
  | 0, ls => ls.foldl mergeE []
  | fuel + 1, ls => mergeAllE fuel (mergePairsE ls)

/-- Split into maximal strictly increasing runs (reversed accumulation). -/
def runsE : List Ent → List (List Ent)
  | [] => []
  | x :: xs => runsAux [x] x.L xs
where
  runsAux (cur : List Ent) (last : Nat) : List Ent → List (List Ent)
    | [] => [cur.reverse]
    | y :: ys => if last < y.L then runsAux (y :: cur) y.L ys else cur.reverse :: runsAux [y] y.L ys

/-- Sort a list of entries, combining equal keys. -/
def sortE (l : List Ent) : List Ent := mergeAllE 64 (runsE l)

/-- The pushed entries of one group step (order `t`, weights `ea ≤ e ≤ eb`). -/
def pushE (t ea eb : Nat) (tab : List Ent) : List Ent :=
  tab.filterMap fun x =>
    let L2 := Nat.lcm x.L t
    if L2 ≤ LMAX then some ⟨L2, mulLo x.a ea, mulUp x.b eb⟩ else none

/-- One DP step before dropping: the subsets without the group, plus those with at least one prime of the group. -/
def stepM (tab : List Ent) (g : Grp) : List Ent := mergeE tab (sortE (pushE g.t (eLo g.ps) (eUp g.ps) tab))

/-- Entries with upper weight `b < KAPPA · L` are dropped; their mass `Σ ⌈b / L⌉` is accounted for separately. -/
def KAPPA : Nat := 16384

/-- `⌈x / y⌉`. -/
def cdiv (x y : Nat) : Nat := (x + y - 1) / y

/-- The kept entries. -/
def keepE (tab : List Ent) : List Ent := tab.filter fun x => KAPPA * x.L ≤ x.b

/-- The dropped mass `Σ ⌈b / L⌉` over the dropped entries. -/
def dropM (tab : List Ent) : Nat := ((tab.filter fun x => !(KAPPA * x.L ≤ x.b)).map fun x => cdiv x.b x.L).sum

/-- One DP step. -/
def stepE (tab : List Ent) (g : Grp) : List Ent := keepE (stepM tab g)

/-- The DP over a list of groups. -/
def runDP (tab : List Ent) : List Grp → List Ent
  | [] => tab
  | g :: gs => runDP (stepE tab g) gs

/-- The total dropped mass of the DP. -/
def runDrop (tab : List Ent) : List Grp → Nat
  | [] => 0
  | g :: gs => dropM (stepM tab g) + runDrop (stepE tab g) gs

/-- The DP with the dropped mass, in one pass: `runDPD tab d gs = (runDP tab gs, d + runDrop tab gs)`. -/
def runDPD (tab : List Ent) (d : Nat) : List Grp → List Ent × Nat
  | [] => (tab, d)
  | g :: gs => let m := stepM tab g; runDPD (keepE m) (d + dropM m) gs

/-- The initial table: the empty subset. -/
def tab0 : List Ent := [⟨1, SC, SC⟩]

/-- `SC · ∏ (1 + e_g)` over the groups, rounded up. -/
def piUp (gs : List Grp) : Nat := gs.foldl (fun acc g => mulUp acc (SC + eUp g.ps)) SC

/-! ## Class sums -/

/-- The divisors of `120`. -/
def div120 : List Nat := [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]

/-- Add `v` at the position of `g` in `div120` (16 accumulators). -/
def addAt (g v : Nat) : List Nat → List Nat → List Nat
  | d :: ds, x :: xs => if d = g then (x + v) :: xs else x :: addAt g v ds xs
  | _, xs => xs

/-- `acc_g += ⌈b g / L'⌉` with `L' = lcm(L, s)`, `g = gcd(L', 120)`, over the entries with `1 ≤ L ≤ LMAX`. -/
def accG (s : Nat) (tab : List Ent) : List Nat :=
  tab.foldl (fun acc x =>
    if 1 ≤ x.L ∧ x.L ≤ LMAX then
      let L2 := Nat.lcm x.L s
      let g := Nat.gcd L2 PER
      addAt g ((x.b * g + L2 - 1) / L2) div120 acc
    else acc) (List.replicate 16 0)

/-- `Σ_{d ∈ ds, d ∣ c} x_d`. -/
def sumDvdAux (c : Nat) : List Nat → List Nat → Nat
  | d :: ds, x :: xs => (if c % d = 0 then x else 0) + sumDvdAux c ds xs
  | _, _ => 0

/-- `Σ_{g ∣ c} acc_g`. -/
def sumDvd (acc : List Nat) (c : Nat) : Nat := sumDvdAux c div120 acc

/-- `Σ a` and `Σ b` over the entries with `1 ≤ L ≤ LMAX`. -/
def sumA (tab : List Ent) : Nat := tab.foldl (fun s x => if 1 ≤ x.L ∧ x.L ≤ LMAX then s + x.a else s) 0
def sumB (tab : List Ent) : Nat := tab.foldl (fun s x => if 1 ≤ x.L ∧ x.L ≤ LMAX then s + x.b else s) 0

/-- `Σ ⌊a / lcm(L, s)⌋` over the entries with `1 ≤ L ≤ LMAX`. -/
def sumR (s : Nat) (tab : List Ent) : Nat :=
  tab.foldl (fun acc x => if 1 ≤ x.L ∧ x.L ≤ LMAX then acc + x.a / Nat.lcm x.L s else acc) 0

end R45.M3
