import RCert.G.Ev

/-!
# U3g/V4g stage 2: timing pilot and row cross-check data (not part of any proof)

`gpilot time N`: evaluates `evalKey` on `N` evenly spaced BASE keys (one thread), prints ms per key.
`gpilot row K R41 R19 R73 R37`: for BASE key number `K` and core residues `r_p < p`, prints the 360-bit core mask
`Y = repB 120 360 x ∪ maskP 360 41 r41 ∪ … ∪ maskP 360 37 r37` and `(s, Q)` of every pattern (for a brute-force check at
period 27720).
-/

open R45 R45.EVG

/-- `(s_P, Q_P)` of every pattern of the core row `r`. -/
def rowData (r : Array Nat) : List (Nat × Nat) :=
  let cs := c4.map fun m => cfam (zmul r m)
  let n4 := cs.map fun c => (c.getD 0 #[]).getD 0 0
  let Z := zOf (tOf cs)
  (List.range npC).map fun P => (sOf n4 P, qOf Z P)

def main (args : List String) : IO Unit := do
  let keys := foldOrbits 120 baseP
  IO.println s!"keys {keys.length} total {(keys.map (·.2)).foldl (· + ·) 0} patterns {npC} weights {pwA.toList}"
  match args with
  | ["time", n] =>
    let n := n.toNat!
    let step := keys.length / n
    for i in [0:n] do
      let xc := keys[i * step]!
      let t0 ← IO.monoMsNow
      let acc := evalKey xc.1
      IO.println s!"key {i * step} cnt {xc.2} sum {(acc.foldl (· + ·) 0) % 1000000007}"
      let t1 ← IO.monoMsNow
      IO.println s!"  ms {t1 - t0}"
  | ["row", k, a, b, c, d] =>
    let x := keys[k.toNat!]!.1
    let Y := repB 120 360 x ||| maskP 360 41 a.toNat! ||| maskP 360 19 b.toNat! ||| maskP 360 73 c.toNat! |||
      maskP 360 37 d.toNat!
    IO.println s!"key {x}"
    IO.println s!"Y {Y}"
    for sq in rowData (mrow Y) do
      IO.println s!"{sq.1} {sq.2}"
  | _ => IO.println "usage: gpilot time N | gpilot row K R41 R19 R73 R37"
