import RCert.E.EvData
import RCert.E.Params
import RCert.M3E.TeffLit
import RCert.Patt

/-!
# U3e stage 2: the evaluator of the minorant at period 3960 (core Lean, compiled for `native_decide`)

The classes `k mod l'` are the BASE orbits (`foldOrbits 3960 [3, 5, 7, 11, 13, 17, 31, 241]`, keys `x`) times the options
of the ADDED primes `41, 19, 73, 23, 37` (`optsP 3960 p`).  A row is the set `U = {e < 3960 : e ∉ x ∪ m_41 ∪ … ∪ m_37}`
(as a 0/1 array).  For each row the evaluator computes `s = |U|` and `Q = Σ_g bn_g S_g(U)`, `S_g(U) = Σ_{a < g} N^g_a(U)^2`,
`N^h_a(U) = #{e ∈ U : e ≡ a (h)}`, and adds `(w s, w Q)` to the slot of its Pintz index `J` (any `J ≥ 1` is valid).
The options of the last prime `37` (the classes `j mod 36`) are evaluated together from the counts of the prefix row
`U'`: `S_g(U' \ C_j) = S_g(U') - 2 Σ_{x < L, x ≡ j (36)} N^g_{x mod g} N^L_x + Σ_{x < L, x ≡ j (36)} (N^L_x)^2`,
`L = lcm(g, 36)`, and `|U' \ C_j| = |U'| - N^36_j`.
-/

namespace R45.EV

open R45

/-- `[e ∉ m]` for `e < 3960`. -/
def mrow (m : Nat) : Array Nat := Array.ofFn (n := 3960) fun e => if m.testBit e.val then 0 else 1

/-- Entrywise product. -/
def zmul (r s : Array Nat) : Array Nat := Array.zipWith (· * ·) r s

/-- `acc + Σ_{t < q} A[a + h t]`. -/
def sumT (A : Array Nat) (a h : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | t + 1, acc => sumT A a h t (acc + A.getD (a + h * t) 0)

/-- The counts modulo `h` from the counts modulo `h q`. -/
def red (A : Array Nat) (h q : Nat) : Array Nat := Array.ofFn (n := h) fun a => sumT A a.val h q 0

/-- The initial count family: the row itself at index 47 (`h = 3960`). -/
def cfam0 (r : Array Nat) : Array (Array Nat) := (Array.replicate 48 (#[] : Array Nat)).setIfInBounds 47 r

/-- One step of the count plan. -/
def cstep (cs : Array (Array Nat)) (s : Nat × Nat × Nat) : Array (Array Nat) :=
  cs.setIfInBounds s.1 (red (cs.getD s.2.1 #[]) (dA.getD s.1 0) s.2.2)

/-- The counts of a row modulo every divisor of 3960 (index of `dA`). -/
def cfam (r : Array Nat) : Array (Array Nat) := plan.foldl cstep (cfam0 r)

/-- `Σ_a A[a]^2`. -/
def sqs (A : Array Nat) : Nat := A.foldl (fun acc v => acc + v * v) 0

/-- `Q = Σ_i bn_i S_{dA[i]}`. -/
def qOf (cs : Array (Array Nat)) : Nat :=
  (List.range 48).foldl (fun acc i => acc + bnA.getD i 0 * sqs (cs.getD i #[])) 0

/-- `acc[x mod 36] += Ng[x mod g] · NL[x]` for `n` consecutive `x`, with the counters `a = x mod g`, `j = x mod 36`. -/
def crossLoop (Ng NL : Array Nat) (g : Nat) : Nat → Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, _, acc => acc
  | n + 1, x, a, j, acc =>
    crossLoop Ng NL g n (x + 1) (if a + 1 = g then 0 else a + 1) (if j + 1 = 36 then 0 else j + 1)
      (acc.modify j (· + Ng.getD a 0 * NL.getD x 0))

/-- 36 zeros. -/
def z36 : Array Nat := Array.replicate 36 0

/-- `cross_i[j] = Σ_{x < L, x ≡ j (36)} N^g[x mod g] N^L[x]`, `g = dA[i]`, `L = lcm(g, 36) = dA[lIdx[i]]`. -/
def crossOf (cs : Array (Array Nat)) (i : Nat) : Array Nat :=
  crossLoop (cs.getD i #[]) (cs.getD (lIdx.getD i 0) #[]) (dA.getD i 0) (dA.getD (lIdx.getD i 0) 0) 0 0 0 z36

/-- `sq_k[j] = Σ_{x < h, x ≡ j (36)} N^h[x]^2`, `h = dA[k]`. -/
def sqOf (cs : Array (Array Nat)) (k : Nat) : Array Nat :=
  crossLoop (cs.getD k #[]) (cs.getD k #[]) (dA.getD k 0) (dA.getD k 0) 0 0 0 z36

/-- `acc + c v` (entrywise). -/
def axpy (c : Nat) (v acc : Array Nat) : Array Nat := Array.zipWith (fun a b => a + c * b) acc v

/-- `X[j] = Σ_i bn_i cross_i[j]`. -/
def xOf (cs : Array (Array Nat)) : Array Nat :=
  (List.range 48).foldl (fun acc i => axpy (bnA.getD i 0) (crossOf cs i) acc) z36

/-- The indices `lcm(g, 36)`. -/
def isL (k : Nat) : Bool := lIdx.toList.contains k

/-- The squares `sq_k` at the indices `k = lcm(g, 36)` (others empty). -/
def sqFam (cs : Array (Array Nat)) : Array (Array Nat) := Array.ofFn (n := 48) fun k => if isL k.val then sqOf cs k.val else #[]

/-- `Z[j] = Σ_i bn_i sq_{lIdx[i]}[j]`. -/
def zOf (cs : Array (Array Nat)) : Array Nat :=
  let sq := sqFam cs
  (List.range 48).foldl (fun acc i => axpy (bnA.getD i 0) (sq.getD (lIdx.getD i 0) #[]) acc) z36

/-- The Pintz index `J ∈ [1, 63]` of a row (`≈ ⌊1 + Y/s⌋` at `α = R0t e_3960`; only the tightness depends on it). -/
def jIdx (s Q : Nat) : Nat := if s = 0 then 1 else min 63 (1 + (Q / (s * 256) * KM + KC) / 2 ^ 56)

/-- Add a row of weight `w`: `acc[2J] += w s`, `acc[2J + 1] += w Q`. -/
def addRow (acc : Array Nat) (w s Q : Nat) : Array Nat :=
  let J := jIdx s Q
  (acc.modify (2 * J) (· + w * s)).modify (2 * J + 1) (· + w * Q)

/-- The 37 rows `U' \ C` of a prefix row `U'` (options of 37: `C = ∅`, weight 1, and `C = C_j`, weight 1 each). -/
def lastStep (acc : Array Nat) (w : Nat) (r : Array Nat) : Array Nat :=
  let cs := cfam r
  let s := (cs.getD 0 #[]).getD 0 0
  let n36 := cs.getD 18 #[]
  let q := qOf cs
  let X := xOf cs
  let Z := zOf cs
  o37.foldl (fun acc j => addRow acc w (s - n36.getD j 0) (q + Z.getD j 0 - 2 * X.getD j 0)) (addRow acc w s q)

/-- The options of an added prime as rows `[e ∉ m]` with their weights. -/
def optRows (p : Nat) : List (Array Nat × Nat) := (optsP 3960 p).map fun mc => (mrow mc.1, mc.2)

def o41 : List (Array Nat × Nat) := optRows 41
def o19 : List (Array Nat × Nat) := optRows 19
def o73 : List (Array Nat × Nat) := optRows 73
def o23 : List (Array Nat × Nat) := optRows 23

/-- 128 zeros (64 Pintz slots `(Σ w s, Σ w Q)`). -/
def z128 : Array Nat := Array.replicate 128 0

/-- The accumulators of one BASE key `x`. -/
def evalKey (x : Nat) : Array Nat :=
  let b := mrow x
  o41.foldl (fun acc mw1 =>
    let r1 := zmul b mw1.1
    o19.foldl (fun acc mw2 =>
      let r2 := zmul r1 mw2.1
      o73.foldl (fun acc mw3 =>
        let r3 := zmul r2 mw3.1
        o23.foldl (fun acc mw4 => lastStep acc (mw1.2 * mw2.2 * mw3.2 * mw4.2) (zmul r3 mw4.1)) acc) acc) acc) z128

/-- `Σ_{(x, c) ∈ L} c · evalKey x`. -/
def evalList (L : List (Nat × Nat)) : Array Nat := L.foldl (fun acc xc => axpy xc.2 (evalKey xc.1) acc) z128

/-- Split a list into pieces of length `k` (`k ≥ 1`). -/
def chunks {α : Type} (k : Nat) (L : List α) : List (List α) :=
  if h : k = 0 ∨ L = [] then [L] else L.take k :: chunks k (L.drop k)
termination_by L.length
decreasing_by
  simp only [not_or] at h
  have : L.length ≠ 0 := fun h0 => h.2 (List.eq_nil_of_length_eq_zero h0)
  simp only [List.length_drop]
  omega

/-- `evalList` in parallel: one dedicated task per piece. -/
def evalPar (k : Nat) (L : List (Nat × Nat)) : Array Nat :=
  let ts := (chunks k L).map fun ch => Task.spawn (fun _ => evalList ch) Task.Priority.dedicated
  ts.foldl (fun acc t => axpy 1 t.get acc) z128

/-- The BASE primes. -/
def baseP : List Nat := [3, 5, 7, 11, 13, 17, 31, 241]

/-- The exponents `e < 3960` with `e ≡ j (mod 36)` (the nonzero options of 37). -/
def cmask36 (j : Nat) : Nat := (List.range 3960).foldl (fun acc e => if e % 36 = j then acc ||| (1 <<< e) else acc) 0

/-- The enlargement of the tail simplex (rounding of the real tail weights). -/
def delta : Rat := 1 / 1000000000000

/-- The claim. -/
def claimQ : Rat := 110449 / 1000000

/-- `K0 = 8 κ 3960 (R0t + δ)`: the tail term per element of `U` (`g S_g ≤ 3960 |U|`). -/
def K0 : Rat := 8 * PE.kap * 3960 * (M3E.R0tLit + delta)

/-- `c_J = norm / (l' J (J + 1))`. -/
def cJ (J : Nat) : Rat := PE.norm / (PE.ellN : Rat) / ((J : Rat) * ((J : Rat) + 1))

/-- The minorant of the rows of slot `J` with `Σ w s = a`, `Σ w Q = q`: `c_J ((2J - K0) a - 8 κ q / 2^36)`. -/
def vt (J a q : Nat) : Rat := cJ J * ((2 * (J : Rat) - K0) * (a : Rat) - 8 * PE.kap * (q : Rat) / 2 ^ 36)

/-- The value of the accumulators. -/
def V (acc : Array Nat) : Rat :=
  ((List.range 64).map fun J => vt J (acc.getD (2 * J) 0) (acc.getD (2 * J + 1) 0)).sum

/-- The final check: `claim ≤ V(Σ_{BASE keys} cnt · evalKey)`, in pieces of `k` keys in parallel. -/
def finalOK (ps : List Nat) (k : Nat) : Bool := decide (claimQ ≤ V (evalPar k (foldOrbits 3960 ps)))

end R45.EV
