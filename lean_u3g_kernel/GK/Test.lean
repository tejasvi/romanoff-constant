import GK.Util

/-! k45g: compiled cross-checks of the fibered evaluator against `evalKey` of RCert/G/Ev.lean (not part of the proof). -/

open R45 R45.EVG R45.GK

def main (args : List String) : IO Unit := do
  let n := (args.getD 0 "5").toNat!
  let step := (args.getD 1 "1").toNat!
  let ks := keysG
  IO.println s!"keys {ks.length}"
  let mut ok := 0
  let mut bad := 0
  for i in List.range n do
    match ks[i * step]? with
    | some xc =>
      let t0 ← IO.monoMsNow
      let a := evalKeyK xc.1
      let t1 ← IO.monoMsNow
      let b := evalKey xc.1
      let t2 ← IO.monoMsNow
      let same := a.toArr == b
      if same then ok := ok + 1 else bad := bad + 1
      IO.println s!"key {i * step} x={xc.1} cnt={xc.2} same={same} fib_ms={t1 - t0} native_ms={t2 - t1}"
    | none => pure ()
  IO.println s!"SUMMARY ok={ok} bad={bad}"
