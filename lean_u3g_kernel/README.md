# Kernel-only Lean 4 proofs of d ≥ 0.110825 and, assuming (I2), d ≥ 0.119178 for Romanoff's constant (certificates U3g, V4g)

This directory contains Lean 4 (v4.35.0-rc3) proofs, with Mathlib (see `lake-manifest.json`), of

```lean
theorem Romanoff.G.romanoff_U3g_K (h1 : ESP28 G.ell) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.U3gStatement
theorem Romanoff.G.romanoff_V4g_K (h1 : ESP28 G.ell) (h2 : JTProp2) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.V4gStatement
```

in GK/FinalK.lean. They are Theorems 1.1 and 1.2 of the paper. The statements, hypotheses and definitions are those of
`Romanoff.G.romanoff_U3g` and `Romanoff.G.romanoff_V4g` in `lean_u3g/`, and the files that define them
(Romanoff/Defs.lean, Romanoff/G/Spec.lean) are the same bytes as there. Thus `G.U3gStatement` is `(110825 / 1000000 :
ℝ) ≤ liminf dens atTop`, `G.V4gStatement` is `(119178 / 1000000 : ℝ) ≤ liminf dens atTop`, and `G.ell` is the modulus
`l_3` of the paper. The hypotheses (I1), (I3), (I5) and (I2) are those of `lean_u3g/README.md`.

**Scope.** Lean's kernel checks both theorems without compiled code. `#print axioms` lists `propext`,
`Classical.choice` and `Quot.sound` and nothing else (Axioms_K45G.lean, output in results/axioms_shipped.txt). Every
finite check is a `decide +kernel` theorem. No Lean file in this directory uses `native_decide`. Among the modules of
the proof the word occurs only in a comment of RCert/G/Ev.lean (results/closure_GK_FinalK.txt).

## Labels used in the comments

- "native" refers to the proofs in `lean_u3g/`, which use compiled evaluation (`native_decide`), and to their evaluator
  `evalKey` (RCert/G/Ev.lean). A suffix K marks a kernel-only counterpart, as in `romanoff_U3g_K`, `tboundALitK` and
  `evalKeyK`.
- "Stage 1" and "stage 2" are the two parts of the proof in `lean_u3g/README.md`. Stage 1 is the bound
  `TBoundA (tabB BLit) R0tLit` on the tables at period 27720, and stage 2 the evaluation of both bounds.
- "K3" is the kernel-only stage 1, and "K1" the kernel-only list of BASE keys (parts 1 and 2 below).
- "k45g" is the label of the files written for part 3 (GK/, gen/).
- A BASE key is an entry of `foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241]`, a mask on Z/120 that stands for one
  rotation orbit. As in `lean_u3g/`, a core row is a BASE key lifted to period 360 together with options of the primes
  41, 19, 73 and 37. A rest row is a BASE key together with one of the 21 options of the prime 41. A slot is one of the 64
  entries of an accumulator, indexed by the Pintz index.
- Some comments name files that are not in this directory. Romanoff/G/U3g.lean, Romanoff/G/V4g.lean,
  Romanoff/G/Lit.lean, Romanoff/G/S2/Final.lean, RCert/G/BCheck.lean and u3g/tools/ are in `lean_u3g/`.
  Romanoff/CertKFinal.lean and M3/tools/kbuild45.py, gen_kfiles.py, gen_kglue.py and gen_kplan.py (the period-120
  versions of the stage-1 tools) are in `lean_kernel/`. RCert/M3/TeffLit.lean names its generator RCert/M3/GenLit.lean,
  which is M3/tools/GenLit.lean in `lean_kernel/`. As noted in `lean_u3g/README.md`, RCert/Data45.lean names its
  generator and the period-120 certificate files of the proofs in `lean/`.

## Structure

The proof is the proof in `lean_u3g/` with its six compiled checks replaced by kernel checks. The files of that proof
that this one uses are the same bytes as there, among them Romanoff/G/Reduce.lean, ReduceMu.lean and Assembly.lean and Basic.lean,
Core.lean, Crt.lean, Ind.lean, Row.lean, Mino.lean, Value.lean, Lift.lean and Key.lean of Romanoff/G/S2/. There are
three new parts.

1. Stage 1 (K3). `Romanoff.G.K.tboundALitK : R0Bound → TBoundA (tabB BLit) R0tLit` (Romanoff/G/LitK.lean) has the
   statement of `tboundALit` in `lean_u3g/`. It replaces the five checks `certOK_data`, `sumsOK_data`, `teffD_eq`,
   `R0tD_eq` and `tabB_BLit_eq`.
   - 327 kernel checks in Romanoff/G/M3/K/, one `decide +kernel` theorem each: the dynamic program of the tables in 39
     segments (`KDP1` … `KDP39`), the tail-mass table in 15 parts (`KR1` … `KR15`), 96 subtables, one for each value of
     `gcd(L, 27720)` (`KSub<h>`), the class-B data in 115 chunks (`KB0` … `KB114`), the certificate check (Pratt
     certificates, sorting and the group conditions) in 56 parts (`KCr0` … `KCr50`, `KCs`, `KCb`, `KCg`, `KCp`, `KCm`), and
     six checks of the values (`KVsA`, `KVsB`, `KVr0a`, `KVacc1`, `KV96`, `KTB`).
   - Romanoff/G/M3/KGcd.lean proves that the table entry of residue `c` depends on `c` only through `gcd(c, 27720)`.
     The checks `valsOK` and `tabBOK` at the 96 divisors of 27720 therefore give `(tabB BLit).getD c 0 = (tabOf …).getD c
     0` for every `c < 27720`.
   - RCert/M3G/KFun.lean defines the checks, Romanoff/G/M3/KSplit.lean proves them sound, and Romanoff/G/M3/KMain.lean
     chains them.
2. The BASE keys (K1). `K45G.foldBase_eq : foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241] = K45G.LG` (K45G/Fold.lean).
   - The primes 3, 5, 7, 11, 13, 17, 31 and 241 are the prime factors of `l'` in the paper. The first seven fold steps are
     those of `lean_kernel/` (K45/S/SSmall.lean). The step for 241 is checked in 18 chunks (K45G/SG_000 … SG_017).
   - The list `K45G.LG` has 7,871 entries, with counts summing to 1,907,010,105. They are the 7,870 rotation orbits that
     leave a residue unblocked and the fully blocked key 2^120 - 1 (count 16,368), whose rows add 0 to every slot.
3. Stage 2. `R45.GK.values_K : claimU ≤ VU (evalPar 123 (foldOrbits 120 baseP)) ∧ claimV ≤ VV (evalPar 123 (foldOrbits
   120 baseP))` (GK/Final.lean) gives the inequalities that `finalOK_true` of `lean_u3g/` checks by compiled evaluation.
   - GK/Ev.lean, the fibered evaluator, computes the accumulators of `evalKey` in a different order. The base-3 digit
     `w = ⌊(x mod 9)/3⌋` of a residue `x mod 360` is seen only by the primes 19, 73 and 37, so the tables of a core row
     depend on the options of these three primes only through their signature. The 7,030 option triples have 412
     signatures (GK/Data.lean).
   - `R45.GK.key_eq` (GK/Spec1.lean … GK/Spec5.lean) states that, for every BASE key and every slot function linear in the
     slot sums, the fibered evaluator gives the value of `evalKey`. Five data checks support it (GK/ChecksK.lean, by the
     kernel).
   - The key modules GK/Keys/K0000.lean … K7870.lean, one per BASE key, hold 21 theorems each, one per option of the prime
     41, of the form `(evalRestK x j).beq LIT = true` by `decide +kernel`.
   - The chunk modules GK/Glue/C000.lean … C063.lean each sum the trees of 123 keys (the last one 122) from their rest
     rows, with the weights of `K45G.LG`. GK/GlueTotal.lean adds the 64 chunk totals to `TOT` (`total_eq`).
   - `claimU_TOT` and `claimV_TOT` check `110825/10^6 ≤ VU` and `119178/10^6 ≤ VV` on `TOT` by `decide +kernel`. The values
     are VU = 0.1108276292911 and VV = 0.1191809294180, equal to those of the compiled evaluation in `lean_u3g/`.
   - GK/Final.lean proves `romanoff_U3g_of_S1` and `romanoff_V4g_of_S1` with stage 1 as a hypothesis, using the
     reductions of `lean_u3g/` (`liminf_ge_of_TBoundA`, `liminf_ge_of_TBoundA_mu`, `lagBound_ge_Vf`). GK/FinalK.lean
     supplies `tboundALitK`.

The import closure of GK.FinalK consists of Mathlib and 8,557 modules of this directory, 7,871 of them key modules
(`python3 -I gen/closure_check_v1.py GK.FinalK .`, output in results/closure_GK_FinalK.txt).

## Build

The commands below build the proof in the order of this build. The key modules were compiled on four machines (f1 to f4
in results/FLEET_BUILD_LOG.tsv) with `lean` and a LEAN_PATH holding the oleans of the import closure of GK.Ev, the
setting that `lake env` gives. Memory figures are peak resident memory per compiling process; the tables in results/
give it in kB of 1024 bytes. The key modules need about 9 GiB each, the stage-1 check `KV96` about 81 GiB and
GK/ChecksK.lean about 67 GiB.

```
lake exe cache get
lake build GK.ChecksK GK.Glue3 K45G Romanoff.G.ReduceMu Romanoff.G.S2.Key Romanoff.G.Assembly Romanoff.G.Spec
# stage 1 (K3)
lake build RCert.M3G.Data RCert.M3G.KFun Romanoff.M3.KGlue Romanoff.G.M3.KGcd RCert.G.BLit RCert.M3G.TeffLit Romanoff.G.Tables
lake build $(ls Romanoff/G/M3/K | grep -E '^(Tab|Sub|Vals|BDs)' | sed 's/.lean$//; s/^/Romanoff.G.M3.K./')
python3 -I M3/tools/kbuild45_g.py Romanoff/G/M3/K/jobs.txt 96 7 0.14
lake env lean -o .lake/build/lib/lean/Romanoff/G/M3/KMain.olean Romanoff/G/M3/KMain.lean
lake env lean -o .lake/build/lib/lean/Romanoff/G/LitK.olean Romanoff/G/LitK.lean
lake env lean Axioms_K3.lean
# stage 2: the key modules (in parallel), the chunk modules, the total and the final theorems
mkdir -p .lake/build/lib/lean/GK/Keys .lake/build/lib/lean/GK/Glue
lake env lean -o .lake/build/lib/lean/GK/Keys/K0000.olean GK/Keys/K0000.lean     # and so on up to K7870
lake env lean -o .lake/build/lib/lean/GK/Glue/C000.olean GK/Glue/C000.lean       # and so on up to C063
lake env lean -o .lake/build/lib/lean/GK/GlueTotal.olean GK/GlueTotal.lean
lake env lean -o .lake/build/lib/lean/GK/Final.olean GK/Final.lean
lake env lean -o .lake/build/lib/lean/GK/FinalK.olean GK/FinalK.lean
lake env lean Axioms_K45G.lean
```

- `kbuild45_g.py JOBS MEMCAP_GB MAXJOBS GB_PER_S` runs the 327 stage-1 checks with a memory-aware scheduler and appends
  one line per check to M3/logs/kbuild45g.tsv. results/kbuild45g.tsv is that table for this build (name, rc, seconds,
  peak memory in kB, estimate). It has 327 checks with rc 0 and 14,358 s in total, and the largest, `KV96`, used
  84,495,984 kB. The literal modules were built in batches of 16.
- results/FLEET_BUILD_LOG.tsv has one line per key module (module, build machine f1 to f4, rc, seconds, peak memory in
  kB). All 7,871 modules have rc 0 and took 877 to 1,255 s each, 2,494.3 hours in total, with at most 9,445,012 kB.
- The key modules import GK.Ev only and do not need Mathlib. They, the chunk modules and the final modules were compiled
  with `lean` directly, since `lake build` does not see oleans written this way and would compile the key modules again.
  For leanchecker, their oleans must lie in real directories under .lake/build/lib/lean/GK/, not behind symbolic links.
  Each chunk module took at most 98 s and 7,042,868 kB, and GK/GlueTotal.lean, GK/Final.lean and GK/FinalK.lean took
  about 4 s and 8.2 million kB each.
- A single `lake build GK.FinalK` would build the same modules through Lake, given memory for its parallel jobs. It was
  not run.
- Axioms_K1.lean and Axioms_K3.lean print the axioms of parts 2 and 1 (results/axioms_K1.txt, results/axioms_K3.txt).

## Generated files

The generators named below are in this directory. None of the files they write needs to be trusted, since each enters the
proof only through kernel checks.

- Romanoff/G/M3/K/ (481 files, with jobs.txt and plan.json) is written by `python3 M3/tools/gen_kfiles_g.py
  M3/data/pratt_v1.json M3/data/kplan_g.json Romanoff/G/M3/K 6`, M3/data/kplan_g.json by `python3 M3/tools/gen_kplan_g.py
  M3/data/pratt_v1.json M3/data/kplan_g.json 250000`, and Romanoff/G/M3/KMain.lean by `python3 M3/tools/gen_kglue_g.py
  Romanoff/G/M3/K/plan.json Romanoff/G/M3/KMain.lean`.
- K45G/ (all files except Fold.lean) and LG.json are written by `lake env lean --run tools/KGenG.lean .`.
- GK/Data.lean is written by `python3 gen/gen_sig_data.py gen/sig_data_v1.json` followed by `python3
  gen/gen_lean_data.py gen/sig_data_v1.json RCert/G/EvData.lean GK/Data.lean`.
- GK/Keys/ is written by `lake build gkkeys` followed by `.lake/build/bin/gkkeys START 263 GK/Keys` for START = 0, 263,
  …, 7627 (arguments: first key, number of keys, directory). KEYS_SHA256SUMS.txt lists the sha256 of the 7,871 key
  modules.
- GK/Glue/C000.lean … C063.lean and the chunk totals C000.T … C063.T are written by `lake build gkglue3` followed by
  `.lake/build/bin/gkglue3 n n GK/Glue` for n = 0, …, 63, and GK/GlueTotal.lean by `python3 gen/gen_glue_total.py GK/Glue
  GK/GlueTotal.lean`.
- The generated files that are the same bytes as in `lean_u3g/` (RCert/M3G/Data.lean, RCert/M3G/TeffLit.lean,
  RCert/G/BLit.lean, RCert/G/EvData.lean) are described in `lean_u3g/README.md`.

The Python generators above were run again on this directory, and their outputs (Romanoff/G/M3/K/,
M3/data/kplan_g.json, Romanoff/G/M3/KMain.lean, gen/sig_data_v1.json, GK/Data.lean, GK/GlueTotal.lean) are identical to
the files here. The key modules match KEYS_SHA256SUMS.txt.

## Checks and controls

The logs named below are byte-identical copies of the build's logs, under results/logs/.

- `lake exe gktest N STEP` compares, as compiled code, `evalKeyK` with `evalKey` on the keys 0, STEP, …, (N - 1)·STEP.
  The two agreed on 200 sampled keys and on keys 0 and 7870 (results/logs/test2.log, results/logs/test_fullkey.log).
  This is a cross-check, not part of the proof.
- Must-fail copies of chunk C000, one with a slot of its total `T` increased by 1 and one with a slot of the first key's
  tree increased by 1, are rejected (results/logs/glue_logs/CtlT.log, results/logs/glue_logs/CtlK.log).
- The bounds 0.1108277 and 0.1191810 fail on `TOT` (results/logs/glue_logs/TotK2.log, results/logs/glue_logs/TotK3.log).
- Other kernels:
  - on the export of one rest row, leanchecker, lean4lean and nanoda accept (results/logs/ext/summary.txt and the
    checkers' logs lc.log, l4l.log and nd.log there);
  - leanchecker accepts a copy of the key module GK/Keys/K1234.lean under another module name (21 theorems, 13 min 43 s;
    results/logs/pilot_leanchecker.log);
  - leanchecker accepts the declarations of each of the 64 chunk modules and of GK.GlueTotal, GK.Final and GK.FinalK
    (results/logs/glue_logs/lc_summary.txt, results/logs/glue_logs/lc2_summary.txt).

## Provenance

PROVENANCE.txt gives the sha256 and the source of every file. "same bytes as" names the identical file in `lean_u3g/` or
`lean_kernel/` (100 files), "generated" marks the files of the section above, "log of the build" names the build log
that a file under results/logs/ copies, and the remaining files are new. After the
build, comments were edited in GK/Data.lean, GK/Ev.lean, GK/Spec2.lean, GK/Test.lean, GK/GenGlue3.lean,
gen/gen_glue_total.py, gen/gen_lean_data.py and gen/gen_sig_data.py. Without comments, the Lean files are the ones that
were built. In gen/gen_lean_data.py the edit also changes the header comment that it writes, so that it writes
GK/Data.lean as shipped.
