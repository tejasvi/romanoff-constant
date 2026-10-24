import GK.Spec2

/-!
# k45g, proofs part 3a: the data checks (kernel `decide`)

- `patsOK`: the 38 patterns of GK/Data.lean are the native evaluator's `pwA`, `pfA`, `pqA`.
- `o41OK`: `optsP 360 41` is `o41r` lifted from period 120.
- `fibOK`: every option mask of 19, 73, 37 depends only on `(x mod 12, (x mod 9) / 3)` below 360.
- `sigOKall`: for each option triple of (19, 73, 37), in the order of `T2`/`T3`/`T4`, the signature `sigs[sigF[t]]` has the tables
  `f_w` and `c` of the triple's mask.
- `wtOK`: the signature weights are the sums of the triple weights.
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

/-! ## Explicit forms used by the checks -/

/-- `f_M(a)` with explicit terms. -/
def fwE (M a : ℕ) : ℕ := ind M (xaw a 0) + ind M (xaw a 1) + ind M (xaw a 2)

/-- `W^1_M(a, b)` with explicit terms. -/
def w1E (M a b : ℕ) : ℕ := ind M (xaw a 0) * ind M (xaw b 0) + ind M (xaw a 1) * ind M (xaw b 1) + ind M (xaw a 2) * ind M (xaw b 2)

theorem fwE_eq (M a : ℕ) : fwE M a = fwM M a := by simp [fwE, fwM, sum_range_succ]

theorem w1E_eq (M a b : ℕ) : w1E M a b = w1M M a b := by simp [w1E, w1M, sum_range_succ]

/-- The `f_w` table grouped by `u`, from a table `fw` of the 12 values. -/
def fwgOfT (fw : List ℕ) : List (List ℕ) := [0, 1, 2, 3].map fun u => [fw.getD u 0, fw.getD (u + 4) 0, fw.getD (u + 8) 0]

/-- The coefficient lists `c[k]`, from the `f_w` table and the mask (for `W^1`). -/
def cOfT (M : ℕ) (fw : List ℕ) : List (List ℕ) :=
  (List.zip puL pvL).map fun uv =>
    (pairs9 uv.1 uv.2).map (fun ab => fw.getD ab.1 0 * fw.getD ab.2 0) ++ (pairsZ uv.1 uv.2).map fun ab => w1E M ab.1 ab.2

/-- The signature check of one mask. -/
def sigOKb (M : ℕ) (σ : Sig) : Bool :=
  let fw := (List.range 12).map (fwE M)
  σ.fwg == fwgOfT fw && σ.c == cOfT M fw

/-! ## Patterns -/

def patD : Pat := ⟨0, [], []⟩

def patsOK : Bool :=
  pats.length == 38 && (List.range 38).all fun P =>
    (pats.getD P patD).pw == pwA.getD P 0 &&
    (pats.getD P patD).pf == (List.range 4).map (fun u => pfA.getD (4 * P + u) 0) &&
    (pats.getD P patD).pq == (List.range 4).map (fun t => (List.range 10).map fun k => pqA.getD (40 * P + (10 * t + k)) 0)

/-! ## Options -/

def o41OK : Bool := optsP 360 41 == o41r.map fun mc => (repB 120 360 mc.1, mc.2)

def fibOK : Bool :=
  (optsP 360 19 ++ optsP 360 73 ++ optsP 360 37).all fun mc =>
    (List.range 360).all fun x => ind mc.1 x == ind mc.1 (xaw (x % 12) ((x % 9) / 3))

/-- The option triples of (19, 73, 37) in the order of `T2`, `T3`, `T4` (mask, weight). -/
def triples : List (ℕ × ℕ) :=
  (optsP 360 19).flatMap fun a => (optsP 360 73).flatMap fun b => (optsP 360 37).map fun c =>
    (a.1 ||| b.1 ||| c.1, a.2 * b.2 * c.2)

def sigD : Sig := ⟨0, [], []⟩

def sigOKall : Bool :=
  triples.length == sigF.length && sigF.all (· < sigs.length) &&
    (triples.zip sigF).all fun ts => sigOKb ts.1.1 (sigs.getD ts.2 sigD)

/-- The weights of the signatures accumulated from the triples. -/
def wtsOf : List ℕ := (triples.zip sigF).foldl (fun acc ts => acc.modify ts.2 (· + ts.1.2)) (List.replicate sigs.length 0)

def wtOK : Bool := wtsOf == sigs.map (·.wt)

end R45.GK
