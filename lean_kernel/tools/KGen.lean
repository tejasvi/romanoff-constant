import K45.Defs

/-! Generator (not part of the libraries; run natively): the literal checkpoints, chunk outputs and orbit codes of the 45a fold, and
the Lean modules of the kernel checks.  usage: kgen OUTDIR -/

open R45 K45

def litL (L : List (Nat × Nat)) : String := "[" ++ ", ".intercalate (L.map fun mc => s!"({mc.1}, {mc.2})") ++ "]"

def chunksF {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, L => L.take k :: chunksF k n (L.drop k)

def chunks {α : Type} (k : Nat) (L : List α) : List (List α) := chunksF k L.length L

def pad3 (n : Nat) : String := let s := toString n; "".pushn '0' (3 - s.length) ++ s

def enc (o : Orb) : Nat := (o.cnt <<< 847) ||| (o.s <<< 840) ||| ((List.range 120).foldl (fun acc c => acc ||| ((o.n.getD c 0) <<< (7 * c))) 0)

def hdr (imps : List String) : String :=
  "".intercalate (imps.map fun i => s!"import {i}\n") ++ "\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace K45.G\n\nopen R45 K45\n\n"

def ftr : String := "end K45.G\n"

def wr (dir name body : String) : IO Unit := IO.FS.writeFile s!"{dir}/{name}.lean" body

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let ps := [3, 5, 7, 11, 13, 17, 31, 41, 241]
  -- options
  let mut optsBody := ""
  for p in ps do
    optsBody := optsBody ++ s!"def opts{p} : List (Nat × Nat) := {litL (optsP 120 p)}\n\n"
  wr dir "Opts" (hdr ["RCert.Patt"] ++ optsBody ++ ftr)
  -- steps 1..7 (whole)
  let mut L : List (Nat × Nat) := [(0, 1)]
  let mut small := ""
  for i in [1, 2, 3, 4, 5, 6] do
    let p := ps[i - 1]!
    let L' := normK (prodK 120 L (optsP 120 p))
    if L' != foldStep 120 L (optsP 120 p) then throw (IO.userError s!"step {i} mismatch")
    small := small ++ s!"def L{i} : List (Nat × Nat) := {litL L'}\n\n"
    L := L'
  -- step 7 output L7, chunked for step 8
  let L7 := normK (prodK 120 L (optsP 120 31))
  if L7 != foldStep 120 L (optsP 120 31) then throw (IO.userError "step 7 mismatch")
  let C7 := chunks 46 L7
  let mut l7body := ""
  for (c, j) in C7.zipIdx do
    l7body := l7body ++ s!"def c7_{pad3 j} : List (Nat × Nat) := {litL c}\n\n"
  l7body := l7body ++ "def L7chunks : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range C7.length).map fun j => s!"c7_{pad3 j}") ++ "]\n\ndef L7 : List (Nat × Nat) := L7chunks.flatten\n\n"
  wr dir "Lsmall" (hdr ["RCert.Patt"] ++ small ++ l7body ++ ftr)
  IO.println s!"L7 {L7.length} chunks {C7.length}"
  -- step 8
  let B8 := C7.map fun c => normK (prodK 120 c (optsP 120 41))
  let L8 := mergeRuns B8
  if L8 != foldStep 120 L7 (optsP 120 41) then throw (IO.userError "step 8 mismatch")
  let mut b8body := ""
  for (b, j) in B8.zipIdx do
    b8body := b8body ++ s!"def b8_{pad3 j} : List (Nat × Nat) := {litL b}\n\n"
  b8body := b8body ++ "def B8s : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range B8.length).map fun j => s!"b8_{pad3 j}") ++ "]\n\n"
  wr dir "B8" (hdr ["RCert.Patt"] ++ b8body ++ ftr)
  let C8 := chunks 40 L8
  let C8f := chunks 28 C8
  for (grp, f) in C8f.zipIdx do
    let mut body := ""
    for (c, j) in grp.zipIdx do
      body := body ++ s!"def c8_{pad3 (28 * f + j)} : List (Nat × Nat) := {litL c}\n\n"
    wr dir s!"L8_{pad3 f}" (hdr ["RCert.Patt"] ++ body ++ ftr)
  wr dir "L8" (hdr ((List.range C8f.length).map fun f => s!"K45.G.L8_{pad3 f}") ++
    "def L8chunks : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range C8.length).map fun j => s!"c8_{pad3 j}") ++
    "]\n\ndef L8 : List (Nat × Nat) := L8chunks.flatten\n\n" ++ ftr)
  IO.println s!"L8 {L8.length} chunks {C8.length} files {C8f.length}"
  -- step 9
  let B9 := C8.map fun c => normK (prodK 120 c (optsP 120 241))
  let G9 := chunks 16 B9
  let M9 := G9.map mergeRuns
  let L9 := mergeRuns M9
  if L9 != foldStep 120 L8 (optsP 120 241) then throw (IO.userError "step 9 mismatch")
  for (grp, g) in G9.zipIdx do
    let mut body := ""
    for (b, j) in grp.zipIdx do
      body := body ++ s!"def b9_{pad3 (16 * g + j)} : List (Nat × Nat) := {litL b}\n\n"
    body := body ++ s!"def B9g_{pad3 g} : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range grp.length).map fun j => s!"b9_{pad3 (16 * g + j)}") ++ "]\n\n"
    wr dir s!"B9_{pad3 g}" (hdr ["RCert.Patt"] ++ body ++ ftr)
  for (m, g) in M9.zipIdx do
    wr dir s!"M9_{pad3 g}" (hdr ["RCert.Patt"] ++ s!"def m9_{pad3 g} : List (Nat × Nat) := {litL m}\n\n" ++ ftr)
  IO.println s!"B9 {B9.length} groups {G9.length} M9 sizes {M9.map (·.length)} L9 {L9.length}"
  let C9 := chunks 500 L9
  let C9f := chunks 10 C9
  for (grp, f) in C9f.zipIdx do
    let mut body := ""
    for (c, j) in grp.zipIdx do
      body := body ++ s!"def c9_{pad3 (10 * f + j)} : List (Nat × Nat) := {litL c}\n\n"
    wr dir s!"L9_{pad3 f}" (hdr ["RCert.Patt"] ++ body ++ ftr)
  wr dir "L9" (hdr ((List.range C9f.length).map fun f => s!"K45.G.L9_{pad3 f}") ++
    "def L9chunks : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range C9.length).map fun j => s!"c9_{pad3 j}") ++
    "]\n\ndef L9 : List (Nat × Nat) := L9chunks.flatten\n\n" ++ ftr)
  -- orbit codes
  let mut norb := 0
  for (c, k) in C9.zipIdx do
    let os := c.filterMap orbF
    let codes := os.map enc
    if (codes.map orbOf).length != os.length then throw (IO.userError "len")
    for (z, o) in codes.zip os do
      let d := orbOf z
      if d.cnt != o.cnt || d.s != o.s || d.n != o.n then throw (IO.userError s!"decode mismatch chunk {k}")
    norb := norb + os.length
    IO.FS.writeFile s!"{dir}/O{pad3 k}.lean"
      ("import K45.Defs\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace K45.Orb\n\nopen R45 K45\n\n" ++
       s!"def codes{pad3 k} : List Nat := [" ++ ", ".intercalate (codes.map toString) ++ "]\n\n" ++
       s!"def orbs{pad3 k} : List Orb := codes{pad3 k}.map orbOf\n\nend K45.Orb\n")
  IO.println s!"L9 chunks {C9.length} files {C9f.length} orbits {norb}"
  -- orbit chunk list
  IO.FS.writeFile s!"{dir}/OAll.lean"
    ("".intercalate ((List.range C9.length).map fun k => s!"import K45.Orb.O{pad3 k}\n") ++
     "\nnamespace K45.Orb\n\nopen R45 K45\n\n" ++
     "/-- The orbits of the fold, in chunks of 500 (the last one shorter). -/\n" ++
     "def orbChunks : List (List Orb) := [" ++ ", ".intercalate ((List.range C9.length).map fun k => s!"orbs{pad3 k}") ++ "]\n\n" ++
     "/-- The orbit list `orbits 120 (ellPO.map (·.1))` as a literal (`K45.orbits_eq`). -/\n" ++
     "def orbLit : List Orb := orbChunks.flatten\n\nend K45.Orb\n")
  -- kernel-check modules (namespace K45.S)
  let sh (imps : List String) : String :=
    "".intercalate (imps.map fun i => s!"import {i}\n") ++
      "\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace K45.S\n\nopen R45 K45 K45.G\n\n"
  let sf : String := "end K45.S\n"
  let dk := " := by\n  decide +kernel\n\n"
  let mut ob := ""
  for p in ps do
    ob := ob ++ s!"theorem opts{p}_eq : optsP 120 {p} = opts{p}{dk}theorem opts{p}_pos : ∀ x ∈ opts{p}, 0 < x.2{dk}"
  wr dir "SOpts" (sh ["K45.G.Opts"] ++ ob ++ sf)
  let mut sm := ""
  let prev := ["[(0, 1)]", "L1", "L2", "L3", "L4", "L5", "L6"]
  for i in [1, 2, 3, 4, 5, 6, 7] do
    sm := sm ++ s!"theorem s{i} : normK (prodK 120 {prev[i - 1]!} opts{ps[i - 1]!}) = L{i}{dk}theorem p{i} : strictPos L{i} = true{dk}"
  wr dir "SSmall" (sh ["K45.G.Lsmall", "K45.G.Opts", "K45.Defs"] ++ sm ++ sf)
  let mut n8 := 0
  for (grp, m) in (chunks 3 (List.range C7.length)).zipIdx do
    let body := "".intercalate (grp.map fun j => s!"theorem s8_{pad3 j} : normK (prodK 120 c7_{pad3 j} opts41) = b8_{pad3 j}{dk}")
    wr dir s!"S8_{pad3 m}" (sh ["K45.G.Lsmall", "K45.G.B8", "K45.G.Opts", "K45.Defs"] ++ body ++ sf)
    n8 := n8 + 1
  wr dir "S8M" (sh ["K45.G.B8", "K45.G.L8", "K45.Defs"] ++ s!"theorem m8 : mergeRuns B8s = L8{dk}theorem p8 : strictPos L8 = true{dk}" ++ sf)
  let mut n9 := 0
  for (grp, m) in (chunks 4 (List.range C8.length)).zipIdx do
    let imps := (grp.map fun j => s!"K45.G.L8_{pad3 (j / 28)}") ++ (grp.map fun j => s!"K45.G.B9_{pad3 (j / 16)}")
    let imps := imps.eraseDups ++ ["K45.G.Opts", "K45.Defs"]
    let body := "".intercalate (grp.map fun j => s!"theorem s9_{pad3 j} : normK (prodK 120 c8_{pad3 j} opts241) = b9_{pad3 j}{dk}")
    wr dir s!"S9_{pad3 m}" (sh imps ++ body ++ sf)
    n9 := n9 + 1
  for g in List.range G9.length do
    wr dir s!"SM9_{pad3 g}" (sh [s!"K45.G.B9_{pad3 g}", s!"K45.G.M9_{pad3 g}", "K45.Defs"] ++
      s!"theorem m9_{pad3 g} : mergeRuns B9g_{pad3 g} = m9_{pad3 g}{dk}" ++ sf)
  wr dir "SL9M" (sh (((List.range G9.length).map fun g => s!"K45.G.M9_{pad3 g}") ++ ["K45.G.L9", "K45.Defs"]) ++
    "theorem m9all : mergeRuns [" ++ ", ".intercalate ((List.range G9.length).map fun g => s!"m9_{pad3 g}") ++ s!"] = L9{dk}" ++
    s!"theorem p9 : strictPos L9 = true{dk}" ++ sf)
  let mut noc := 0
  for (grp, m) in (chunks 2 (List.range C9.length)).zipIdx do
    let imps := ((grp.map fun k => s!"K45.G.L9_{pad3 (k / 10)}").eraseDups) ++ (grp.map fun k => s!"K45.Orb.O{pad3 k}") ++ ["K45.Defs"]
    let body := "".intercalate (grp.map fun k => s!"theorem oc_{pad3 k} : c9_{pad3 k}.filterMap orbF = K45.Orb.orbs{pad3 k}{dk}")
    wr dir s!"SOC_{pad3 m}" (sh imps ++ body ++ sf)
    noc := noc + 1
  let mods := ["K45.S.SOpts", "K45.S.SSmall", "K45.S.S8M", "K45.S.SL9M"] ++ ((List.range n8).map fun m => s!"K45.S.S8_{pad3 m}") ++
    ((List.range n9).map fun m => s!"K45.S.S9_{pad3 m}") ++ ((List.range G9.length).map fun g => s!"K45.S.SM9_{pad3 g}") ++
    ((List.range noc).map fun m => s!"K45.S.SOC_{pad3 m}")
  IO.FS.writeFile s!"{dir}/mods.txt" ("\n".intercalate mods ++ "\n")
  -- the assembly
  let cons (names : List String) : String := "".intercalate (names.map fun n => s!".cons {n} (") ++ ".nil" ++ "".pushn ')' names.length
  let s8n := (List.range C7.length).map fun j => s!"S.s8_{pad3 j}"
  let s9n := (List.range C8.length).map fun j => s!"S.s9_{pad3 j}"
  let m9n := (List.range G9.length).map fun g => s!"S.m9_{pad3 g}"
  let ocn := (List.range C9.length).map fun k => s!"S.oc_{pad3 k}"
  let mut smallSteps := ""
  for i in [1, 2, 3, 4, 5, 6] do
    let pp := ps[i - 1]!
    let inp := prev[i - 1]!
    let hL := if i = 1 then "(by decide)" else s!"(strictPos_spec _ S.p{i - 1}).2"
    smallSteps := smallSteps ++ s!"theorem step{i} : foldStep 120 {inp} (optsP 120 {pp}) = L{i} := by\n  rw [S.opts{pp}_eq]\n  exact step_of_normK {hL} S.opts{pp}_pos S.s{i} S.p{i}\n\n"
  let asm := "".intercalate ((["RCert.Data45", "K45.Assembly"] ++ mods ++ ["K45.G.B9All", "K45.G.M9All", "K45.Orb.OAll"]).map fun i => s!"import {i}\n") ++
    "\nset_option maxRecDepth 100000\n\n/-! The fold of the 45a certificate, kernel-checked: `foldOrbits 120 ps = L9` and `orbits 120 ps = orbLit`. -/\n\n" ++
    "namespace K45\n\nopen R45 R45.D45 Romanoff K45.G\n\n" ++ smallSteps ++
    "theorem step7 : foldStep 120 L6 (optsP 120 31) = L7 := by\n  rw [S.opts31_eq]\n  exact step_of_normK (strictPos_spec _ S.p6).2 S.opts31_pos S.s7 S.p7\n\n" ++
    "theorem step8 : foldStep 120 L7 (optsP 120 41) = L8 := by\n  rw [S.opts41_eq]\n" ++
    s!"  have hB : List.Forall₂ (fun C B => normK (prodK 120 C opts41) = B) L7chunks B8s :=\n    {cons s8n}\n" ++
    "  exact step_exact (strictPos_spec _ S.p7).2 S.opts41_pos (step_check hB S.m8) S.p8\n\n" ++
    "theorem step9 : foldStep 120 L8 (optsP 120 241) = L9 := by\n  rw [S.opts241_eq]\n" ++
    s!"  have hB : List.Forall₂ (fun C B => normK (prodK 120 C opts241) = B) L8chunks B9s :=\n    {cons s9n}\n" ++
    s!"  have hG : List.Forall₂ (fun G M => mergeRuns G = M) B9groups M9s :=\n    {cons m9n}\n" ++
    "  exact step_exact (strictPos_spec _ S.p8).2 S.opts241_pos (step_check2 hB hG rfl S.m9all) S.p9\n\n" ++
    "theorem fold_eq : foldOrbits 120 (ellPO.map (·.1)) = L9 := by\n" ++
    "  show foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120\n" ++
    "    (foldStep 120 (foldStep 120 [(0, 1)] (optsP 120 3)) (optsP 120 5)) (optsP 120 7)) (optsP 120 11))\n" ++
    "    (optsP 120 13)) (optsP 120 17)) (optsP 120 31)) (optsP 120 41)) (optsP 120 241) = L9\n" ++
    "  rw [step1, step2, step3, step4, step5, step6, step7, step8, step9]\n\n" ++
    "theorem orbits_eq : orbits 120 (ellPO.map (·.1)) = K45.Orb.orbLit := by\n" ++
    "  rw [orbits_eq_filterMap, fold_eq]\n" ++
    s!"  have hOC : List.Forall₂ (fun c o => c.filterMap orbF = o) L9chunks K45.Orb.orbChunks :=\n    {cons ocn}\n" ++
    "  show L9chunks.flatten.filterMap orbF = K45.Orb.orbChunks.flatten\n" ++
    "  rw [filterMap_flatten, map_filterMap_of_forall₂ hOC]\n\nend K45\n"
  wr dir "Fold" asm
  -- the B9 lists for the assembly
  wr dir "B9All" (hdr ((List.range G9.length).map fun g => s!"K45.G.B9_{pad3 g}") ++
    "def B9s : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range C8.length).map fun j => s!"b9_{pad3 j}") ++ "]\n\n" ++
    "def B9groups : List (List (List (Nat × Nat))) := [" ++ ", ".intercalate ((List.range G9.length).map fun g => s!"B9g_{pad3 g}") ++ "]\n\n" ++ ftr)
  wr dir "M9All" (hdr ((List.range G9.length).map fun g => s!"K45.G.M9_{pad3 g}") ++
    "def M9s : List (List (Nat × Nat)) := [" ++ ", ".intercalate ((List.range G9.length).map fun g => s!"m9_{pad3 g}") ++ "]\n\n" ++ ftr)
  IO.println s!"modules: S8 {n8}, S9 {n9}, SM9 {G9.length}, SOC {noc}"
