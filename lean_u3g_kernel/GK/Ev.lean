import RCert.G.Ev
import GK.Data

/-!
# k45g: the fibered evaluator of the U3g/V4g minorants (for kernel-only checking)

The same accumulators as `R45.EVG.evalKey` (RCert/G/Ev.lean, run as compiled code by the proofs in lean_u3g/), computed with a fibered
component of the residues: the base-3 digit `w = (x mod 9) / 3` of `x mod 360` is seen only by the core primes 19, 73, 37, so a core row
`Y = repB 120 360 R ∪ m19 ∪ m73 ∪ m37` (R = BASE key ∪ the option of 41, a mask on Z/120) has
`n4[u] = Σ_{i<3} f_w(u + 4 i) n_R(u + 4 i)` and `T_{g_c}(u, v) = Σ_{i,j<3} W_w^{[9 | g_c]}(u + 4 i, v + 4 j) T^R_{gcd(g_c,120)}(..)`,
where `f_w`, `W_w^1` depend on the options of (19, 73, 37) only through their signature (412 signatures, GK/Data.lean).
Per rest row the evaluator computes the class counts `n_R`, the tables `Zr[t][k]` (the `bnC`-weighted sums of `T^R_h`),
then for each signature `σ` the inputs `(ŝ, Y)` of the pattern loop, which are `(n4, Z)` of `evalKey` for every core row of
that signature, and adds `(w s, w Q)` to the slot `jIdx s Q` exactly as `addRow` does.
-/

namespace R45.GK

open R45 R45.EVG

/-- `1` if `ρ` survives (bit `ρ` of the exclusion mask `R` is clear). -/
def sv (R ρ : Nat) : Nat := if R.testBit ρ then 0 else 1

/-- `Σ_{i < n} f i`. -/
def sumN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumN f n + f n

/-- `Σ a_i b_i` over two lists (to the shorter length). -/
def dotL : List Nat → List Nat → Nat
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

/-- `Σ` of a list. -/
def sumL : List Nat → Nat
  | [] => 0
  | a :: as => a + sumL as

/-- `n_R(a) = #{ρ < 120 : ρ ∉ R, ρ ≡ a (mod 12)}` (`ρ = a + 12 i`, `a < 12`). -/
def nR (R a : Nat) : Nat := sumN (fun i => sv R (a + 12 * i)) 10

/-- `N_R(h, c, b) = #{ρ < 120 : ρ ∉ R, ρ ≡ c (mod h), ρ ≡ b (mod 12)}`. -/
def NR (R h c b : Nat) : Nat := sumN (fun j => if (b + 12 * j) % h = c then sv R (b + 12 * j) else 0) 10

/-- `T^R_h(a, b) = #{(ρ1, ρ2) : ρi ∉ R, ρ1 ≡ ρ2 (mod h), ρ1 ≡ a, ρ2 ≡ b (mod 12)}`. -/
def TR (R h a b : Nat) : Nat := sumN (fun i => sv R (a + 12 * i) * NR R h ((a + 12 * i) % h) b) 10

/-- The pairs `(u_k, v_k)`, `u ≤ v < 4` (as `pu`, `pv` of RCert/G/Ev.lean). -/
def puL : List Nat := [0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
def pvL : List Nat := [0, 1, 2, 3, 1, 2, 3, 2, 3, 3]

/-- The 9 pairs `(u + 4 i, v + 4 j)`. -/
def pairs9 (u v : Nat) : List (Nat × Nat) :=
  [(u, v), (u, v + 4), (u, v + 8), (u + 4, v), (u + 4, v + 4), (u + 4, v + 8), (u + 8, v), (u + 8, v + 4), (u + 8, v + 8)]

/-- The 3 pairs `(u + 4 i, v + 4 j)` with `u + 4 i ≡ v + 4 j (mod 3)`, `j = (u + i + 3 - v) mod 3` (`v ≤ 3`). -/
def pairsZ (u v : Nat) : List (Nat × Nat) :=
  [(u, v + 4 * ((u + 3 - v) % 3)), (u + 4, v + 4 * ((u + 4 - v) % 3)), (u + 8, v + 4 * ((u + 5 - v) % 3))]

/-- The list of `T^R_h(a, b)` over `h ∈ Hs`. -/
def trList (R : Nat) (Hs : List Nat) (ab : Nat × Nat) : List Nat := Hs.map fun h => TR R h ab.1 ab.2

/-- `Zr[t][k]` (12 values): `Σ_{h ∈ H0} bn0[t]_h T_h(a, b)` for the 9 pairs, then `Σ_{h ∈ H1} bn1[t]_h T_h(a, b)` for the 3
z-equal pairs of `k`. -/
def zrRow (R : Nat) : List (List (List Nat)) :=
  let tr := (List.zip puL pvL).map fun uv =>
    ((pairs9 uv.1 uv.2).map (trList R H0), (pairsZ uv.1 uv.2).map (trList R H1))
  (List.zip bn0 bn1).map fun bb => tr.map fun p => p.1.map (dotL bb.1) ++ p.2.map (dotL bb.2)

/-- `n_R` grouped by `u`: `[[n_R(u), n_R(u + 4), n_R(u + 8)] | u < 4]`. -/
def nRg (R : Nat) : List (List Nat) := [0, 1, 2, 3].map fun u => [nR R u, nR R (u + 4), nR R (u + 8)]

/-! ## The accumulator: 64 slots `(Σ w s, Σ w Q)` in a complete binary tree of depth 6 -/

inductive Acc where
  | leaf (a q : Nat)
  | node (l r : Acc)

/-- The zero tree of depth `d`. -/
def Acc.zero : Nat → Acc
  | 0 => .leaf 0 0
  | d + 1 => .node (Acc.zero d) (Acc.zero d)

/-- Add `(a, q)` at slot `J < 2^d` (most significant bit first). -/
def Acc.add : Nat → Nat → Nat → Nat → Acc → Acc
  | _, _, a, q, .leaf a' q' => .leaf (a' + a) (q' + q)
  | 0, _, _, _, t => t
  | d + 1, J, a, q, .node l r =>
    if J < 2 ^ d then .node (Acc.add d J a q l) r else .node l (Acc.add d (J - 2 ^ d) a q r)

/-- The slots as a list of 64 pairs (in slot order). -/
def Acc.toList : Acc → List (Nat × Nat)
  | .leaf a q => [(a, q)]
  | .node l r => l.toList ++ r.toList

/-- Boolean equality of trees. -/
def Acc.beq : Acc → Acc → Bool
  | .leaf a q, .leaf a' q' => a == a' && q == q'
  | .node l r, .node l' r' => Acc.beq l l' && Acc.beq r r'
  | _, _ => false

/-! ## The evaluation -/

/-- The rows of one rest row `R` (weight `w`): all signatures of (19, 73, 37) and all patterns of (23, 43, 29). -/
def restStep (acc : Acc) (w R : Nat) : Acc :=
  let n12 := nRg R
  let Z := zrRow R
  sigs.foldl (fun acc σ =>
    let sh := List.zipWith dotL σ.fwg n12
    let Y := Z.map fun Zt => List.zipWith dotL σ.c Zt
    let ws := w * σ.wt
    pats.foldl (fun acc P =>
      let s := dotL P.pf sh
      let Q := sumL (List.zipWith dotL P.pq Y)
      let ww := ws * P.pw
      acc.add 6 (jIdx s Q) (ww * s) (ww * Q)) acc) acc

/-- The accumulators of one BASE key `x` (120 bits): the 21 options of 41 at period 120. -/
def evalKeyK (x : Nat) : Acc := o41r.foldl (fun acc mc => restStep acc mc.2 (x ||| mc.1)) (Acc.zero 6)

/-- One rest row on its own (for pilots and finer shards). -/
def evalRestK (x i : Nat) : Acc :=
  match o41r[i]? with
  | some mc => restStep (Acc.zero 6) mc.2 (x ||| mc.1)
  | none => Acc.zero 6

/-- The 128-slot array of `evalKey` from a tree (`acc[2J] = Σ w s`, `acc[2J+1] = Σ w Q`). -/
def Acc.toArr (t : Acc) : Array Nat := (t.toList.flatMap fun p => [p.1, p.2]).toArray

end R45.GK
