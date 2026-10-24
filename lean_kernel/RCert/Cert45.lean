import RCert.Params45

/-! The evaluation parameters of the 45a certificate for a `T(c)` table `teff`, a budget constant `c1` and a uniform
multiplier `mu` (U2: `c1 = 8`, `mu = 0`; v3: `c1 = C1v3 = 6.7814`, `mu = muV3`). -/

open R45 R45.D45 R45.P45

namespace R45.P45

def parOf (teff : List Rat) (c1 mu : Rat) : Par := ⟨per, ellN, philN, 8, c1, kap, norm, teff, mu⟩

end R45.P45
