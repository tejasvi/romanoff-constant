# Lean proof of the bounds for Romanoff's constant, checked by the kernel

This directory contains a second proof in Lean 4 of the bounds `d >= 0.109406` and `d >= 0.117953` of Section 4 of
the paper, which are weaker than its Theorems 1.1 and 1.2. Every computation in it is
checked by the Lean kernel; no module uses `native_decide`. It is a separate Lake project for Lean v4.35.0-rc3 and
Mathlib commit c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). Section 7 of the paper describes the proof.

The main theorems are in `Romanoff/CertKFinal.lean`:

    theorem Romanoff.romanoff_U2_K (h1 : ESP28 ell) (h3 : PNTAP ell) (h5 : R0Bound) : U2Statement
    theorem Romanoff.romanoff_v3_K (h1 : ESP28 ell) (h2 : JTProp2) (h3 : PNTAP ell) (h5 : R0Bound) : V3Statement

They have the statements and hypotheses of `Romanoff.romanoff_U2` and `Romanoff.romanoff_v3` in `../lean/`; the
definitions, in `Romanoff/Defs.lean`, are the same file in both directories and are explained in `../lean/README.md`.
`lake env lean Axioms45K.lean` prints the axioms of these two theorems and of `cert_U2_K`, `cert_v3_K`,
`Romanoff.M3.tboundLitK` and `K45.orbits_eq`: each depends only on `propext`, `Classical.choice` and `Quot.sound`
(`results/axioms_shipped.txt`).

The proof uses the analytic part of the native proof unchanged. In place of the four checks that the native proof
evaluates with `native_decide`, it uses three results checked by the kernel:

- `Romanoff.M3.tboundLitK` (`Romanoff/M3/KMain.lean`): the bounds `T+(c)` from the certified list of primes and the
  lower sums for `R0`, checked in 244 theorems in `Romanoff/M3/K/` (`M3/README_K.md`).
- `K45.orbits_eq` (`K45/Fold.lean`): the list of the 92,206 rotation orbits of the class patterns modulo 120 (the native
  proof computes this list inside its check of the Lagrangian bound). A fold over the prime factors of `ell` computes it; the lists after each step are given as literals in `K45/G/`, the modules
  in `K45/S/` check the steps chunk by chunk, and `K45/Orb/` holds the orbits in 185 chunks.
- `cert_U2_K` and `cert_v3_K` (`Romanoff/CertKFinal.lean`, with `Romanoff/CertK.lean` and `Romanoff/CertKGlue.lean`):
  the Lagrangian bound (4.5) of the paper, evaluated in the 185 theorems `K45/Lag/C000` to `C184`, each on at most 500
  orbits, against the bounds in `K45/Lag/Bounds.lean`, which are rounded outward at 10^-24.

Each of these checks is a theorem proved by `decide +kernel`. The import closure of the main theorems has 983 modules of
this project; outside it they import only Mathlib.

## Building

    lake exe cache get
    bash tools/build_k.sh [K45_JOBS] [MEMCAP_GB]

`tools/build_k.sh` builds with Lake the modules that the 244 theorems of `Romanoff/M3/K/` import and the 70 literal
modules, then the K45 modules with at most `K45_JOBS` parallel jobs, then the 244 theorems with `M3/tools/kbuild45.py`,
which starts a job only while the estimated memory of its jobs stays below `MEMCAP_GB`, and finally writes the axioms
into `results/axioms_shipped.txt`, replacing the shipped copy (`sha256sum -c SHA256SUMS` then compares it with the
shipped one). Both arguments default to values computed from the memory of the machine. The script runs on Linux and
needs Python 3 and GNU time (`/usr/bin/time -v`). The largest of the 244 theorems needs about 21 GB, and
`M3/tools/kbuild45.py` stops and requeues a job whenever less than 12 GB of memory is free, so the machine needs at least
about 40 GB. On one machine with 32 threads and 128 GB of memory the build took 1 h 35 min and 10.3 CPU-hours, not
counting Mathlib. The largest process used 20.8 GB, and the machine had at most 91 GB in use (sampled every 10 seconds).

## Regenerating the generated files

Run these commands in this directory, with `OUT` a new directory; apart from `gen_kfiles.py`, the generators do not
create directories. Each should print no differences.

The Lagrangian chunks `K45/Lag/C000.lean` to `C184.lean`, `Bounds.lean` and `BOUNDS.txt` (a native evaluation of about
3.5 minutes; without the second argument the program writes into `K45/Lag` itself):

    mkdir -p OUT/lag
    lake build k45genlag
    .lake/build/bin/k45genlag 500 OUT/lag
    for f in OUT/lag/*.lean; do cmp "$f" "K45/Lag/$(basename "$f")"; done; cmp OUT/lag/BOUNDS.txt K45/Lag/BOUNDS.txt

The 421 files of `K45/G/`, `K45/S/` and `K45/Orb/` and `K45/Fold.lean` (about 2 minutes; it needs `K45.Defs` built and
writes the files into one flat directory, together with a module list `mods.txt`):

    mkdir -p OUT/kgen
    lake env lean --run tools/KGen.lean OUT/kgen
    for f in OUT/kgen/*.lean; do b=$(basename "$f"); t=$(ls K45/G/"$b" K45/S/"$b" K45/Orb/"$b" K45/"$b" 2>/dev/null | head -1); cmp -s "$f" "$t" || echo "differs: $b"; done

The modules of `Romanoff/M3/K/` and `Romanoff/M3/KMain.lean` (leave the environment variable `KAPPA` unset):

    python3 M3/tools/gen_kplan.py M3/data/pratt_v1.json OUT/kplan.json 250000; cmp OUT/kplan.json M3/data/kplan.json
    python3 M3/tools/gen_kfiles.py M3/data/pratt_v1.json M3/data/kplan.json OUT/K 6; diff -r OUT/K Romanoff/M3/K
    python3 M3/tools/gen_kglue.py Romanoff/M3/K/plan.json OUT/KMain.lean; cmp OUT/KMain.lean Romanoff/M3/KMain.lean

The data modules `RCert/Data45.lean` and `RCert/M3/Data.lean`, from the files in `../reproduce/` and `../check/` and
from `M3/data/pratt_v1.json`:

    python3 tools/gen_data45.py ../reproduce/tails_p120b_v5_c073e0de.json ../check/cert_p120b_v3_6fd62e90.json OUT/Data45.lean
    cmp OUT/Data45.lean RCert/Data45.lean
    python3 M3/tools/gen_data_lean.py M3/data/pratt_v1.json OUT/Data.lean
    cmp OUT/Data.lean RCert/M3/Data.lean

`M3/data/pratt_v1.json` is the output of `M3/tools/gen_pratt.py` on `../check/fac300_41e4cdd6.json` and
`../check/fac1200_fdb_af082adc.json`; that program needs python-flint and takes long to run. `RCert/M3/TeffLit.lean` was
printed by `M3/tools/GenLit.lean` (see `M3/README_M3.md`), and the theorem `KF` of `Romanoff/M3/K/` checks it. None of the generated files
needs to be trusted, since every check is a theorem about their contents that the kernel checks.

Two comments are out of date: `lakefile.toml` says that the library `RCert` is compiled to native code for
`native_decide`, which no module here uses, and `Romanoff/Reduction.lean` names `Romanoff/Theorems.lean`, which is in
`../lean/`.

`SHA256SUMS` lists the files of this directory except this README.
