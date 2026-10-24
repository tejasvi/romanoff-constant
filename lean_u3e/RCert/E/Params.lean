import RCert.Cert45

/-! Parameters of the U3e evaluation: the modulus `l' = 3·5·7·11·13·17·31·241·41·19·73·23·37` (with the orders of 2),
period 3960. -/

open R45 R45.D45

namespace R45.PE

/-- The primes of `l'` with `ord_p(2)`. -/
def ellPO : List (Nat × Nat) :=
  [(3, 2), (5, 4), (7, 3), (11, 10), (13, 12), (17, 8), (31, 5), (241, 24), (41, 20), (19, 18), (73, 9), (23, 11), (37, 36)]

def per : Nat := 3960
def ellN : Nat := (ellPO.map (·.1)).foldl (· * ·) 1
def philN : Nat := (ellPO.map (·.1 - 1)).foldl (· * ·) 1
def pell : Rat := (ellPO.map fun po => ((po.1 - 1 : Nat) : Rat) / ((po.1 - 2 : Nat) : Rat)).foldl (· * ·) 1
def kap : Rat := C0up * pell / ((per : Rat) * log2lo)
def norm : Rat := ((ellN : Rat) / (philN : Rat)) / ((per : Rat) * log2hi)

/-- The evaluator parameters for a table `teff` at period 3960. -/
def parOf (teff : List Rat) (c1 mu : Rat) : Par := ⟨per, ellN, philN, 8, c1, kap, norm, teff, mu⟩

end R45.PE
