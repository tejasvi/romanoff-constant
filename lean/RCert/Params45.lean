import RCert.Lag
import RCert.Data45

/-! Parameters of the 45a evaluation (shared by the main run and the sensitivity run). -/

open R45 R45.D45

namespace R45.P45

def per : Nat := 120
def ellN : Nat := (ellPO.map (·.1)).foldl (· * ·) 1
def philN : Nat := (ellPO.map (·.1 - 1)).foldl (· * ·) 1
def pell : Rat := (ellPO.map fun po => ((po.1 - 1 : Nat) : Rat) / ((po.1 - 2 : Nat) : Rat)).foldl (· * ·) 1
def kap : Rat := C0up * pell / ((per : Rat) * log2lo)
def norm : Rat := ((ellN : Rat) / (philN : Rat)) / ((per : Rat) * log2hi)
def teff : List Rat := (List.range per).map fun c => Tup.getD c 0 + ((Nat.gcd c per : Nat) : Rat) * R0tail

end R45.P45
