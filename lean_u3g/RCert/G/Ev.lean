import RCert.G.EvData
import RCert.G.Params
import RCert.Patt

/-!
# U3g/V4g stage 2: the evaluator of the minorants at period 27720 = 360 · 7 · 11 (core Lean, compiled for `native_decide`)

The classes `k mod l_G` are the BASE orbits (`foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241]`, 120-bit keys `x`, lifted to
360 bits) times the options of the core primes `41, 19, 73, 37` (orders dividing 360, `optsP 360 p`) times the options of
the independent primes `23` (order 11), `43` (order 14 = 2 · 7) and `29` (order 28 = 4 · 7).  A core row is the set
`C = {x < 360 : x ∉ key ∪ m_41 ∪ m_19 ∪ m_73 ∪ m_37}` (a 0/1 array).  By the Chinese remainder theorem
`e ↔ (e mod 360, e mod 7, e mod 11)`, the row at period 27720 of a core row and residues `(r23, r43, r29)` has
`s = Σ_u F(u) n_u` and `S_g = Σ_{u,v < 4} W^τ(u, v) T_{g_c}(u, v)` (`g = g_c τ`, `g_c ∣ 360`, `τ ∣ 77`), with
`n_u = #{x ∈ C : x ≡ u (4)}`, `T_h(u, v) = Σ_{a < h} N^h_a(C_u) N^h_a(C_v)`, `C_u = {x ∈ C : x ≡ u (4)}`, and tables
`F`, `W^τ` that depend on the residues only through their pattern (`sig7`, `sig11`, weights `w7`, `w11`).  For each core
row the evaluator computes `Z^τ(u, v) = Σ_{g_c} ⌈B_{g_c τ} 2^32⌉ T_{g_c}(u, v)` and, for each of the `np7 · np11` patterns,
`s` and `Q = Σ_τ Σ_{u ≤ v} m_{uv} W^τ(u, v) Z^τ(u, v)` (`m = 1` on the diagonal, `2` off it), and adds `(w s, w Q)` to the
slot of the Pintz index `J` (any `J ≥ 1` is valid).  Both minorants (U3g with `μ = 0`, V4g with `μ > 0`) are linear in the
slot sums `(Σ w s, Σ w Q)`, so one pass serves both.
-/

namespace R45.EVG

open R45

/-- `[x ∉ m]` for `x < 360`. -/
def mrow (m : Nat) : Array Nat := Array.ofFn (n := 360) fun x => if m.testBit x.val then 0 else 1

/-- Entrywise product. -/
def zmul (r s : Array Nat) : Array Nat := Array.zipWith (· * ·) r s

/-- `acc + Σ_{t < q} A[a + h t]`. -/
def sumT (A : Array Nat) (a h : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | t + 1, acc => sumT A a h t (acc + A.getD (a + h * t) 0)

/-- The counts modulo `h` from the counts modulo `h q`. -/
def red (A : Array Nat) (h q : Nat) : Array Nat := Array.ofFn (n := h) fun a => sumT A a.val h q 0

/-- The initial count family: the row itself at index 23 (`h = 360`). -/
def cfam0 (r : Array Nat) : Array (Array Nat) := (Array.replicate 24 (#[] : Array Nat)).setIfInBounds 23 r

/-- One step of the count plan. -/
def cstep (cs : Array (Array Nat)) (s : Nat × Nat × Nat) : Array (Array Nat) :=
  cs.setIfInBounds s.1 (red (cs.getD s.2.1 #[]) (dC.getD s.1 0) s.2.2)

/-- The counts of a row modulo every divisor of 360 (index of `dC`). -/
def cfam (r : Array Nat) : Array (Array Nat) := plan.foldl cstep (cfam0 r)

/-- The rows `[x ≡ u (mod 4)]`, `u < 4`. -/
def cls4 (u : Nat) : Array Nat := Array.ofFn (n := 360) fun x => if x.val % 4 = u then 1 else 0

/-- The four class rows. -/
def c4 : Array (Array Nat) := #[cls4 0, cls4 1, cls4 2, cls4 3]

/-- `acc + Σ_{a < n} A[a] B[a]`. -/
def dotL (A B : Array Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => dotL A B n (acc + A.getD n 0 * B.getD n 0)

/-- The pairs `(u, v)`, `u ≤ v < 4`. -/
def pu : Array Nat := #[0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
def pv : Array Nat := #[0, 1, 2, 3, 1, 2, 3, 2, 3, 3]

/-- `T[10 c + k] = Σ_{a < dC[c]} N_{u_k}[c][a] N_{v_k}[c][a]` (`cs[u]` = the count family of `C_u`). -/
def tOf (cs : Array (Array (Array Nat))) : Array Nat :=
  Array.ofFn (n := 240) fun i =>
    dotL ((cs.getD (pu.getD (i.val % 10) 0) #[]).getD (i.val / 10) #[])
      ((cs.getD (pv.getD (i.val % 10) 0) #[]).getD (i.val / 10) #[]) (dC.getD (i.val / 10) 0) 0

/-- `Z[10 t + k] = Σ_{c < 24} bnC[24 t + c] T[10 c + k]`. -/
def zOf (T : Array Nat) : Array Nat :=
  Array.ofFn (n := 40) fun i =>
    (List.range 24).foldl (fun acc c => acc + bnC.getD (24 * (i.val / 10) + c) 0 * T.getD (10 * c + i.val % 10) 0) 0

/-! ## The patterns of the independent residues (pattern `P = np11 a + b`, `a < np7`, `b < np11`) -/

/-- The number of combined patterns. -/
def npC : Nat := np7 * np11

/-- The weight of pattern `P`. -/
def pwt (P : Nat) : Nat := w7.getD (P / np11) 0 * w11.getD (P % np11) 0

/-- `F_P(u) = f7(u) f11(u)`. -/
def pf (P u : Nat) : Nat := f7.getD (4 * (P / np11) + u) 0 * f11.getD (4 * (P % np11) + u) 0

/-- `m_k W^{τ_t}_P(u_k, v_k)`: `W^1 = f7 f7 f11 f11`, `W^7 = q7 f11 f11`, `W^11 = f7 f7 q11`, `W^77 = q7 q11`. -/
def pw (P t k : Nat) : Nat :=
  let a := P / np11
  let b := P % np11
  let u := pu.getD k 0
  let v := pv.getD k 0
  let F7 := f7.getD (4 * a + u) 0 * f7.getD (4 * a + v) 0
  let G7 := q7.getD (16 * a + 4 * u + v) 0
  let F11 := f11.getD (4 * b + u) 0 * f11.getD (4 * b + v) 0
  let G11 := q11.getD (16 * b + 4 * u + v) 0
  (if u = v then 1 else 2) * (if t = 0 then F7 * F11 else if t = 1 then G7 * F11 else if t = 2 then F7 * G11 else G7 * G11)

/-- The tables of all patterns: `pwA[P]`, `pfA[4 P + u]`, `pqA[40 P + 10 t + k]`. -/
def pwA : Array Nat := Array.ofFn (n := npC) fun P => pwt P.val
def pfA : Array Nat := Array.ofFn (n := 4 * npC) fun i => pf (i.val / 4) (i.val % 4)
def pqA : Array Nat := Array.ofFn (n := 40 * npC) fun i => pw (i.val / 40) (i.val % 40 / 10) (i.val % 10)

/-- `s_P = Σ_u F_P(u) n_u`. -/
def sOf (n4 : Array Nat) (P : Nat) : Nat := (List.range 4).foldl (fun acc u => acc + pfA.getD (4 * P + u) 0 * n4.getD u 0) 0

/-- `Q_P = Σ_{t, k} pq[P][t][k] Z[t][k]`. -/
def qOf (Z : Array Nat) (P : Nat) : Nat := (List.range 40).foldl (fun acc i => acc + pqA.getD (40 * P + i) 0 * Z.getD i 0) 0

/-- The Pintz index `J ∈ [1, 63]` of a row (`≈ ⌊1 + 8 κ (Q/(2^32 s) + 27720 R0t)⌋`; only the tightness depends on it). -/
def jIdx (s Q : Nat) : Nat := if s = 0 then 1 else min 63 (1 + (Q / (s * 256) * KM + KC) / 2 ^ 48)

/-- Add a row of weight `w`: `acc[2J] += w s`, `acc[2J + 1] += w Q`. -/
def addRow (acc : Array Nat) (w s Q : Nat) : Array Nat :=
  let J := jIdx s Q
  (acc.modify (2 * J) (· + w * s)).modify (2 * J + 1) (· + w * Q)

/-- The rows of one core row (weight `w`): all patterns of the independent residues. -/
def rowStep (acc : Array Nat) (w : Nat) (r : Array Nat) : Array Nat :=
  let cs := c4.map fun m => cfam (zmul r m)
  let n4 := cs.map fun c => (c.getD 0 #[]).getD 0 0
  let Z := zOf (tOf cs)
  (List.range npC).foldl (fun acc P => addRow acc (w * pwA.getD P 0) (sOf n4 P) (qOf Z P)) acc

/-- The options of a core prime as rows `[x ∉ m]` (period 360) with their weights. -/
def optRows (p : Nat) : List (Array Nat × Nat) := (optsP 360 p).map fun mc => (mrow mc.1, mc.2)

def o41 : List (Array Nat × Nat) := optRows 41
def o19 : List (Array Nat × Nat) := optRows 19
def o73 : List (Array Nat × Nat) := optRows 73
def o37 : List (Array Nat × Nat) := optRows 37

/-- The `n`-bit periodic extension of a `p`-bit mask: bit `e < n` is bit `e mod p` of `x`. -/
def repB (p n x : Nat) : Nat := (List.range n).foldl (fun acc e => if x.testBit (e % p) then acc ||| (1 <<< e) else acc) 0

/-- 128 zeros (64 Pintz slots `(Σ w s, Σ w Q)`). -/
def z128 : Array Nat := Array.replicate 128 0

/-- The accumulators of one BASE key `x` (120 bits). -/
def evalKey (x : Nat) : Array Nat :=
  let b := mrow (repB 120 360 x)
  o41.foldl (fun acc mw1 =>
    let r1 := zmul b mw1.1
    o19.foldl (fun acc mw2 =>
      let r2 := zmul r1 mw2.1
      o73.foldl (fun acc mw3 =>
        let r3 := zmul r2 mw3.1
        o37.foldl (fun acc mw4 => rowStep acc (mw1.2 * mw2.2 * mw3.2 * mw4.2) (zmul r3 mw4.1)) acc) acc) acc) z128

/-- `acc + c v` (entrywise). -/
def axpy (c : Nat) (v acc : Array Nat) : Array Nat := Array.zipWith (fun a b => a + c * b) acc v

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

/-! ## The minorants -/

/-- The enlargement of the tail simplex (rounding of the real tail weights). -/
def delta : Rat := 1 / 1000000000000

/-- The claims. -/
def claimU : Rat := 110825 / 1000000
def claimV : Rat := 119178 / 1000000

/-- V4g: the uniform budget multiplier and the budget constant of (I2). -/
def muV : Rat := 687217 / 1000000000000
def c1V : Rat := 67814 / 10000

/-- `λ_J = max(μ, norm/(J(J+1)))`, `ν_J = λ_J - μ ≥ 0`. -/
def lamJ (mu : Rat) (J : Nat) : Rat := max mu (PG.norm / ((J : Rat) * ((J : Rat) + 1)))

/-- `h = norm/i + λ_J (i - 1)` (`= min_{i' ≥ 1}` at `i = i*(J)`). -/
def hJ (mu : Rat) (i J : Nat) : Rat := PG.norm / (i : Rat) + lamJ mu J * ((i : Rat) - 1)

/-- The coefficient of the box and budget terms, `8 ν_J + μ C1`. -/
def cpJ (mu c1 : Rat) (J : Nat) : Rat := 8 * (lamJ mu J - mu) + mu * c1

/-- The minorant of the rows of slot `J` with `Σ w s = a`, `Σ w Q = q`:
`(1/l) [(h - c κ 27720 (R0t + δ)) a - c κ q / 2^32]`, `c = 8 ν_J + μ C1` (the tail `g S_g ≤ 27720 s`). -/
def vtM (mu c1 : Rat) (i J a q : Nat) : Rat :=
  (1 / (PG.ellN : Rat)) * ((hJ mu i J - cpJ mu c1 J * PG.kap * 27720 * (R0tG + delta)) * (a : Rat) -
    cpJ mu c1 J * PG.kap * (q : Rat) / 2 ^ 32)

/-- U3g (`μ = 0`, `i*(J) = J`). -/
def VU (acc : Array Nat) : Rat :=
  ((List.range 64).map fun J => vtM 0 0 J J (acc.getD (2 * J) 0) (acc.getD (2 * J + 1) 0)).sum

/-- V4g (`μ = muV`, `C1 = c1V`, `i*(J) = istarV[J]`). -/
def VV (acc : Array Nat) : Rat :=
  ((List.range 64).map fun J => vtM muV c1V (istarV.getD J 1) J (acc.getD (2 * J) 0) (acc.getD (2 * J + 1) 0)).sum

/-- The final check: both claims against `Σ_{BASE keys} cnt · evalKey`, in pieces of `k` keys in parallel. -/
def finalOK (k : Nat) : Bool :=
  let acc := evalPar k (foldOrbits 120 baseP)
  decide (claimU ≤ VU acc) && decide (claimV ≤ VV acc)

end R45.EVG
