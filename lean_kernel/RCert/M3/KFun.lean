import RCert.M3.Check

/-!
# M3, K version: kernel-friendly functions

The same computations as `RCert/M3/Core.lean`, written with the recursors `Nat.rec`, `List.rec` directly and Boolean
tests (`Nat.blt`, `Nat.ble`, `Nat.beq`, `cond`): the kernel reduces these several times faster than the
structural-recursion (`brecOn`) definitions.  They are `noncomputable` (the code generator does not support recursors)
and are proved equal to the checker functions in `Romanoff/M3/KEq.lean`.
-/

namespace R45.M3

/-! ## Packed tables -/

/-- One entry from its 154-bit code. -/
def decEK (n : Nat) : Ent :=
  ⟨Nat.land n 4194303, Nat.land (Nat.shiftRight n 22) 73786976294838206463,
    Nat.land (Nat.shiftRight n 88) 73786976294838206463⟩

/-- The entries of one chunk, least significant first, stopping at `0`. -/
noncomputable def decChunkK (fuel : Nat) : Nat → List Ent :=
  Nat.rec (motive := fun _ => Nat → List Ent) (fun _ => [])
    (fun _ ih n => cond (Nat.beq n 0) [] (decEK n :: ih (Nat.shiftRight n 154))) fuel

/-- `l1 ++ l2`. -/
noncomputable def appK (l1 l2 : List Ent) : List Ent :=
  List.rec (motive := fun _ => List Ent) l2 (fun e _ ih => e :: ih) l1

/-- A table from its packed chunks (64 entries each). -/
noncomputable def decTabK (cs : List Nat) : List Ent :=
  List.rec (motive := fun _ => List Ent) [] (fun c _ ih => appK (decChunkK 64 c) ih) cs

/-- Entrywise equality. -/
noncomputable def entsEqK (xs : List Ent) : List Ent → Bool :=
  List.rec (motive := fun _ => List Ent → Bool) (fun ys => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun x _ ih ys => List.rec (motive := fun _ => Bool) false
      (fun y ys' _ => Nat.beq x.L y.L && Nat.beq x.a y.a && Nat.beq x.b y.b && ih ys') ys) xs

/-! ## The DP step -/

/-- Merge two sorted tables, adding the weights of equal keys. -/
noncomputable def mergeK (xs : List Ent) : List Ent → List Ent :=
  List.rec (motive := fun _ => List Ent → List Ent) (fun ys => ys)
    (fun x _ ih ys => List.rec (motive := fun _ => List Ent) (x :: ih [])
      (fun y ys' ih2 => cond (Nat.blt x.L y.L) (x :: ih (y :: ys'))
        (cond (Nat.blt y.L x.L) (y :: ih2) (⟨x.L, x.a + y.a, x.b + y.b⟩ :: ih ys'))) ys) xs

/-- Merge adjacent pairs of sorted tables (`o` = the pending table). -/
noncomputable def mergePairsK (ls : List (List Ent)) : List (List Ent) :=
  List.rec (motive := fun _ => Option (List Ent) → List (List Ent))
    (fun o => Option.rec [] (fun l => [l]) o)
    (fun l _ ih o => Option.rec (ih (some l)) (fun l0 => mergeK l0 l :: ih none) o) ls none

/-- Merge a list of sorted tables (rounds of pairwise merges). -/
noncomputable def mergeAllK (fuel : Nat) : List (List Ent) → List Ent :=
  Nat.rec (motive := fun _ => List (List Ent) → List Ent)
    (fun ls => List.rec (motive := fun _ => List Ent → List Ent) (fun acc => acc) (fun l _ ih acc => ih (mergeK acc l)) ls [])
    (fun _ ih ls => List.rec (motive := fun _ => List Ent) []
      (fun l ls' _ => List.rec (motive := fun _ => List Ent) l (fun _ _ _ => ih (mergePairsK ls)) ls') ls) fuel

/-- Maximal strictly increasing runs. -/
noncomputable def runsK (l : List Ent) : List (List Ent) :=
  List.rec (motive := fun _ => List Ent → Nat → List (List Ent))
    (fun cur _ => List.rec (motive := fun _ => List (List Ent)) [] (fun _ _ _ => [cur.reverse]) cur)
    (fun y _ ih cur last => List.rec (motive := fun _ => List (List Ent)) (ih [y] y.L)
      (fun _ _ _ => cond (Nat.blt last y.L) (ih (y :: cur) y.L) (cur.reverse :: ih [y] y.L)) cur) l [] 0

/-- Sort, combining equal keys. -/
noncomputable def sortK (l : List Ent) : List Ent := mergeAllK 64 (runsK l)

/-- The pushed entries of one group step. -/
noncomputable def pushK (t ea eb : Nat) (tab : List Ent) : List Ent :=
  List.rec (motive := fun _ => List Ent) []
    (fun x _ ih => cond (Nat.ble (Nat.lcm x.L t) LMAX) (⟨Nat.lcm x.L t, mulLo x.a ea, mulUp x.b eb⟩ :: ih) ih) tab

/-- One DP step before dropping. -/
noncomputable def stepMK (tab : List Ent) (g : Grp) : List Ent := mergeK tab (sortK (pushK g.t (eLo g.ps) (eUp g.ps) tab))

/-- The kept entries (`KAPPA · L ≤ b`). -/
noncomputable def keepK (tab : List Ent) : List Ent :=
  List.rec (motive := fun _ => List Ent) [] (fun x _ ih => cond (Nat.ble (KAPPA * x.L) x.b) (x :: ih) ih) tab

/-- The dropped mass. -/
noncomputable def dropMK (tab : List Ent) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => cond (Nat.ble (KAPPA * x.L) x.b) ih (cdiv x.b x.L + ih)) tab

/-- One DP step. -/
noncomputable def stepK (tab : List Ent) (g : Grp) : List Ent := keepK (stepMK tab g)

/-- The DP over a list of groups. -/
noncomputable def runDPK (tab : List Ent) (gs : List Grp) : List Ent :=
  List.rec (motive := fun _ => List Ent → List Ent) (fun tab => tab) (fun g _ ih tab => ih (stepK tab g)) gs tab

/-- The DP with the dropped mass. -/
noncomputable def runDPDK (tab : List Ent) (d : Nat) (gs : List Grp) : List Ent × Nat :=
  List.rec (motive := fun _ => List Ent → Nat → List Ent × Nat) (fun tab d => (tab, d))
    (fun g _ ih tab d => ih (keepK (stepMK tab g)) (d + dropMK (stepMK tab g))) gs tab d

/-- A DP segment check: from the table `decTabK la` with dropped mass `da`, the groups `gs` give `decTabK lb`, `db`. -/
noncomputable def segOK (tab : List Ent) (da : Nat) (gs : List Grp) (lb : List Nat) (db : Nat) : Bool :=
  entsEqK (runDPDK tab da gs).1 (decTabK lb) && Nat.beq (runDPDK tab da gs).2 db

/-- A DP check without the dropped mass (the R0 table). -/
noncomputable def segROK (tab : List Ent) (gs : List Grp) (lb : List Nat) : Bool := entsEqK (runDPK tab gs) (decTabK lb)

/-! ## Passes over the tables -/

/-- Force the elements of a list of numbers (`cond` on a test that needs each element as a literal). -/
noncomputable def allLitK (v : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Nat.beq e e && ih) v

/-- `addAt` with Boolean tests. -/
noncomputable def addAtK (g v : Nat) (ds : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun xs => xs)
    (fun d _ ih xs => List.rec (motive := fun _ => List Nat) [] (fun x xs' _ => cond (Nat.beq d g) ((x + v) :: xs') (x :: ih xs')) xs) ds

/-- `accG` with Boolean tests and the accumulator forced at every entry. -/
noncomputable def accGK (s : Nat) (tab : List Ent) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => ih (cond (Nat.ble 1 x.L && Nat.ble x.L LMAX)
      (let L2 := Nat.lcm x.L s; let g := Nat.gcd L2 PER;
        let acc' := addAtK g ((x.b * g + L2 - 1) / L2) div120 acc; cond (allLitK acc') acc' acc') acc)) tab
    (List.replicate 16 0)

/-- `sumR` with Boolean tests. -/
noncomputable def sumRK (u : Nat) (tab : List Ent) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => ih (cond (Nat.ble 1 x.L && Nat.ble x.L LMAX) (acc + x.a / Nat.lcm x.L u) acc)) tab 0

/-- `sumA`, `sumB` with Boolean tests. -/
noncomputable def sumAK (tab : List Ent) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => ih (cond (Nat.ble 1 x.L && Nat.ble x.L LMAX) (acc + x.a) acc)) tab 0
noncomputable def sumBK (tab : List Ent) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => ih (cond (Nat.ble 1 x.L && Nat.ble x.L LMAX) (acc + x.b) acc)) tab 0

/-- `mkBD` with the kernel passes. -/
noncomputable def mkBDK (tT tR : List Ent) (r0a : Nat) (gx : Grp × Bool) : BD :=
  let g := gx.1
  let FU := (g.ps.map fUp).sum
  let FL := (g.ps.map fLo).sum
  cond gx.2 ⟨FU, FL, g.t, true, accGK g.t tT, sumRK g.t tR⟩ ⟨FU, FL, g.t, false, [], r0a / g.t⟩

/-- The subtable of the entries with `gcd(L, 120) = h`. -/
noncomputable def subK (h : Nat) (tab : List Ent) : List Ent :=
  List.rec (motive := fun _ => List Ent) [] (fun x _ ih => cond (Nat.beq (Nat.gcd x.L PER) h) (x :: ih) ih) tab

/-- One subtable pass for the order `s`: `Σ ⌈b G / lcm(L, s)⌉` over the entries with `1 ≤ L ≤ LMAX`, and whether all of
them have `gcd(lcm(L, s), 120) = G`. -/
noncomputable def passK (s G : Nat) (tab : List Ent) : Nat × Bool :=
  List.rec (motive := fun _ => Nat → Bool → Nat × Bool) (fun acc ok => (acc, ok))
    (fun x _ ih acc ok => cond (Nat.ble 1 x.L && Nat.ble x.L LMAX)
      (cond (Nat.beq (Nat.gcd (Nat.lcm x.L s) PER) G)
        (ih (acc + (x.b * G + Nat.lcm x.L s - 1) / Nat.lcm x.L s) ok) (ih acc false))
      (ih acc ok)) tab 0 true

/-- `accG` assembled from subtables `[(h, tab_h)]`: the bucket `lcm(gcd(s, 120), h)` receives the pass of `tab_h`. -/
noncomputable def accSplitK (s : Nat) (subs : List (Nat × List Ent)) : List Nat × Bool :=
  List.rec (motive := fun _ => List Nat → Bool → List Nat × Bool) (fun acc ok => (acc, ok))
    (fun ht _ ih acc ok =>
      let G := Nat.lcm (Nat.gcd s PER) ht.1
      let r := passK s G ht.2
      ih (addAt G r.1 div120 acc) (ok && r.2)) subs (List.replicate 16 0) true

/-- `mkBD` from the subtables of the T table (exact groups by `accSplitK`), with the check flag. -/
noncomputable def mkBDS (subs : List (Nat × List Ent)) (tR : List Ent) (r0a : Nat) (gx : Grp × Bool) : BD × Bool :=
  let g := gx.1
  let FU := (g.ps.map fUp).sum
  let FL := (g.ps.map fLo).sum
  cond gx.2 (let r := accSplitK g.t subs; (⟨FU, FL, g.t, true, r.1, sumRK g.t tR⟩, r.2))
    (⟨FU, FL, g.t, false, [], r0a / g.t⟩, true)

/-- Equality of class-B data. -/
def bdEq (x y : BD) : Bool :=
  Nat.beq x.FU y.FU && Nat.beq x.FL y.FL && Nat.beq x.t y.t && (x.ex == y.ex) && (x.acc == y.acc) && Nat.beq x.r y.r

/-- The class-B check for a chunk of groups against literal data. -/
noncomputable def bdChunkOK (subs : List (Nat × List Ent)) (tR : List Ent) (r0a : Nat) :
    List (Grp × Bool) → List BD → Bool
  | [], [] => true
  | gx :: gs, bd :: bds => (let r := mkBDS subs tR r0a gx; r.2 && bdEq r.1 bd) && bdChunkOK subs tR r0a gs bds
  | _, _ => false

/-- `teff` from the precomputed pass values. -/
def teffOfV (D : Data) (acc : List Nat) (sA sB dT r0a : Nat) (bs : List BD) : List Rat :=
  let prM := piUp D.gA - sA
  let piU := piUp D.gA
  let tail : Rat := R0upQ - ((r0a + r0bOf bs : Nat) : Rat) / (SC : Rat)
  (List.range PER).map fun c =>
    ((sumDvd acc c + (prC prM c + drC piU dT c) + tbC bs sB (prC prM c + drC piU dT c) c : Nat) : Rat) / (SC : Rat) +
      (Nat.gcd c PER : Rat) * tail

end R45.M3
