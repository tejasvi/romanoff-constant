import RCert.M3.KFun
import RCert.M3G.Defs

/-!
# M3 at period 27720, K version: the period-dependent passes (core Lean)

The subtable passes of RCert/M3/KFun.lean with `PER = 27720` and the 96 divisors `divG` (`subKG`, `passKG`, `accSplitKG`,
`mkBDSG`, `bdChunkOKG`), and the values of the alpha-form table at the divisors of 27720:
* `tabNumV D acc sA sB dT bs c`: the numerator (over `SC`) of the table entry of class `c`, from the pass values, i.e.
  `sumDvd acc c + prune(c) + drop(c) + T_b(c)` (as `tabOf` in Romanoff/G/M3/M3A.lean);
* `valsOK`: `tabNumV` at the 96 divisors against a literal list;
* `tabBOK`: `Σ_{g ∈ divG, g ∣ d} B_g = v_d / SC` at the 96 divisors `d`.
The period-free functions (packed tables, DP, sums) are those of RCert/M3/KFun.lean.
-/

namespace R45.M3G

open R45.M3 hiding PER accG sumDvd

/-- The subtable of the entries with `gcd(L, 27720) = h`. -/
noncomputable def subKG (h : Nat) (tab : List Ent) : List Ent :=
  List.rec (motive := fun _ => List Ent) [] (fun x _ ih => cond (Nat.beq (Nat.gcd x.L PER) h) (x :: ih) ih) tab

/-- One subtable pass for the order `s`: `Σ ⌈b G / lcm(L, s)⌉` over the entries with `1 ≤ L ≤ LMAX`, and whether all of
them have `gcd(lcm(L, s), 27720) = G`. -/
noncomputable def passKG (s G : Nat) (tab : List Ent) : Nat × Bool :=
  List.rec (motive := fun _ => Nat → Bool → Nat × Bool) (fun acc ok => (acc, ok))
    (fun x _ ih acc ok => cond (Nat.ble 1 x.L && Nat.ble x.L LMAX)
      (cond (Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G)
        (ih (acc + (x.b * G + Nat.lcm x.L s - 1) / Nat.lcm x.L s) ok) (ih acc false))
      (ih acc ok)) tab 0 true

/-- `accG` (period 27720) assembled from subtables `[(h, tab_h)]`: the bucket `lcm(gcd(s, 27720), h)` receives the pass
of `tab_h`. -/
noncomputable def accSplitKG (s : Nat) (subs : List (Nat × List Ent)) : List Nat × Bool :=
  List.rec (motive := fun _ => List Nat → Bool → List Nat × Bool) (fun acc ok => (acc, ok))
    (fun ht _ ih acc ok =>
      let G := Nat.lcm (Nat.gcd s PER) ht.1
      let r := passKG s G ht.2
      ih (addAt G r.1 divG acc) (ok && r.2)) subs (List.replicate 96 0) true

/-- `mkBD` (period 27720) from the subtables of the T table (exact groups by `accSplitKG`), with the check flag. -/
noncomputable def mkBDSG (subs : List (Nat × List Ent)) (tR : List Ent) (r0a : Nat) (gx : Grp × Bool) : BD × Bool :=
  let g := gx.1
  let FU := (g.ps.map fUp).sum
  let FL := (g.ps.map fLo).sum
  cond gx.2 (let r := accSplitKG g.t subs; (⟨FU, FL, g.t, true, r.1, sumRK g.t tR⟩, r.2))
    (⟨FU, FL, g.t, false, [], r0a / g.t⟩, true)

/-- The class-B check (period 27720) for a chunk of groups against literal data. -/
noncomputable def bdChunkOKG (subs : List (Nat × List Ent)) (tR : List Ent) (r0a : Nat) :
    List (Grp × Bool) → List BD → Bool
  | [], [] => true
  | gx :: gs, bd :: bds => (let r := mkBDSG subs tR r0a gx; r.2 && bdEq r.1 bd) && bdChunkOKG subs tR r0a gs bds
  | _, _ => false

/-- The numerator (over `SC`) of the alpha-form table entry of class `c`, from the pass values. -/
def tabNumV (D : Data) (acc : List Nat) (sA sB dT : Nat) (bs : List BD) (c : Nat) : Nat :=
  let prM := piUp D.gA - sA
  let piU := piUp D.gA
  sumDvd acc c + (prC prM c + drC piU dT c) + tbC bs sB (prC prM c + drC piU dT c) c

/-- `tabNumV` at the 96 divisors of 27720 against a literal list. -/
def valsOK (D : Data) (acc : List Nat) (sA sB dT : Nat) (bs : List BD) (vals : List Nat) : Bool :=
  divG.map (tabNumV D acc sA sB dT bs) == vals

/-- `Σ_{g ∈ divG, g ∣ d} B_g = v_d / SC` for the 96 divisors `d` (in the order of `divG`) and the literal values `v`. -/
def tabBOK (B : Nat → Rat) (vals : List Nat) : Bool :=
  (divG.zip vals).all fun dv => ((divG.filter fun g => dv.1 % g == 0).map B).sum == (dv.2 : Rat) / (SC : Rat)

end R45.M3G
