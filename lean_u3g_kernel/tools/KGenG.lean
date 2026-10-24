import K45.Defs
import K45.G.Lsmall
import K45.G.Opts

/-! Generator for K1 (not part of the libraries; run natively): the BASE fold list of U3g/V4g,
`foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241]`, as one 241 step on K45's checkpoint `L7` (18 chunks), with the literal
chunk outputs, the merged list in chunks of 123, the kernel shards and a JSON copy of the list.
usage: lake env lean --run tools/KGenG.lean OUTDIR (writes OUTDIR/K45G/*.lean and OUTDIR/LG.json) -/

open R45 K45 K45.G

def litL (L : List (Nat × Nat)) : String := "[" ++ ", ".intercalate (L.map fun mc => s!"({mc.1}, {mc.2})") ++ "]"

def chunksF {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, L => L.take k :: chunksF k n (L.drop k)

def chunks {α : Type} (k : Nat) (L : List α) : List (List α) := chunksF k L.length L

def pad3 (n : Nat) : String := let s := toString n; "".pushn '0' (3 - s.length) ++ s

def hdr (imps : List String) (opens : String := "R45 K45 K45.G") : String :=
  "".intercalate (imps.map fun i => s!"import {i}\n") ++ s!"\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace K45G\n\nopen {opens}\n\n"

def ftr : String := "end K45G\n"

def wr (dir name body : String) : IO Unit := IO.FS.writeFile s!"{dir}/K45G/{name}.lean" body

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  IO.FS.createDirAll s!"{dir}/K45G"
  let baseP := [3, 5, 7, 11, 13, 17, 31, 241]
  if L7chunks.length != 18 then throw (IO.userError "L7 chunks")
  -- the 241 step, chunk by chunk
  let BG := L7chunks.map fun c => normK (prodK 120 c opts241)
  let LG := mergeRuns BG
  if LG != foldStep 120 L7 (optsP 120 241) then throw (IO.userError "step mismatch")
  if LG != foldOrbits 120 baseP then throw (IO.userError "foldOrbits mismatch")
  if strictPos LG != true then throw (IO.userError "strictPos")
  -- chunk outputs
  let mut bgBody := ""
  for (b, j) in BG.zipIdx do
    bgBody := bgBody ++ s!"def bg_{pad3 j} : List (Nat × Nat) := {litL b}\n\n"
  bgBody := bgBody ++ "def BGs : List (List (Nat × Nat)) := [" ++
    ", ".intercalate ((List.range BG.length).map fun j => s!"bg_{pad3 j}") ++ "]\n\n"
  wr dir "BG" (hdr ["RCert.Patt"] "R45" ++ bgBody ++ ftr)
  -- the merged list in chunks of 123 (8 chunks per file)
  let CG := chunks 123 LG
  let CGf := chunks 8 CG
  for (grp, f) in CGf.zipIdx do
    let mut body := ""
    for (c, j) in grp.zipIdx do
      body := body ++ s!"def lg_{pad3 (8 * f + j)} : List (Nat × Nat) := {litL c}\n\n"
    wr dir s!"LG_{pad3 f}" (hdr ["RCert.Patt"] "R45" ++ body ++ ftr)
  wr dir "LG" (hdr ((List.range CGf.length).map fun f => s!"K45G.LG_{pad3 f}") "R45" ++
    "/-- The BASE fold list of U3g/V4g in chunks of 123 keys. -/\n" ++
    "def LGchunks : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range CG.length).map fun j => s!"lg_{pad3 j}") ++
    "]\n\n/-- The BASE fold list of U3g/V4g: `foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241]` (`K45G.foldBase_eq`). -/\n" ++
    "def LG : List (Nat × Nat) := LGchunks.flatten\n\n" ++ ftr)
  -- kernel shards: one chunk product per file, then the merge and the strict-positivity check
  for j in List.range BG.length do
    wr dir s!"SG_{pad3 j}" (hdr ["K45.G.Lsmall", "K45.G.Opts", "K45.Defs", "K45G.BG"] ++
      s!"theorem sg_{pad3 j} : normK (prodK 120 c7_{pad3 j} opts241) = bg_{pad3 j} := by\n  decide +kernel\n\n" ++ ftr)
  wr dir "SGM" (hdr ["K45G.BG", "K45G.LG", "K45.Defs"] "R45 K45" ++
    "theorem sgm : mergeRuns BGs = LG := by\n  decide +kernel\n\n" ++
    "theorem pG : strictPos LG = true := by\n  decide +kernel\n\n" ++ ftr)
  -- JSON copy of the list
  IO.FS.writeFile s!"{dir}/LG.json"
    ("[" ++ ",\n".intercalate (LG.map fun mc => s!"[{mc.1}, {mc.2}]") ++ "]\n")
  IO.println s!"L7 {L7.length} in {L7chunks.length} chunks; BG sizes {BG.map (·.length)}; LG {LG.length} in {CG.length} chunks, {CGf.length} files; total count {(LG.map (·.2)).sum}"
