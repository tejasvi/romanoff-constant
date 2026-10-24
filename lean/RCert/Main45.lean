import RCert.Params45

open R45 R45.D45 R45.P45

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let os := orbits per (ellPO.map (·.1))
  let t1 ← IO.monoMsNow
  IO.println s!"orbits {os.length}, total count {(os.map (·.cnt)).foldl (· + ·) 0} (ell {ellN}), {t1 - t0} ms"
  let pU2 : Par := ⟨per, ellN, philN, 8, 8, kap, norm, teff, 0⟩
  let bU2 := lagBound pU2 os
  let t2 ← IO.monoMsNow
  IO.println s!"U2 floor(1e12 x bound) = {(bU2 * 1000000000000).floor}"
  IO.println s!"U2 bound {Float.ofScientific bU2.num.natAbs true 0 / Float.ofNat bU2.den} >= 0.109406: {decide ((109406 : Rat) / 1000000 ≤ bU2)} ({t2 - t1} ms)"
  let pV3 : Par := ⟨per, ellN, philN, 8, C1v3, kap, norm, teff, muV3⟩
  let bV3 := lagBound pV3 os
  let t3 ← IO.monoMsNow
  IO.println s!"v3 floor(1e12 x bound) = {(bV3 * 1000000000000).floor}"
  IO.println s!"v3 bound {Float.ofScientific bV3.num.natAbs true 0 / Float.ofNat bV3.den} >= 0.117953: {decide ((117953 : Rat) / 1000000 ≤ bV3)} ({t3 - t2} ms)"
