# Lean proof of the bounds for Romanoff's constant

This directory contains a proof in Lean 4 of the bounds `d >= 0.109406` and `d >= 0.117953` of Section 4 of the
paper, which are weaker than its Theorems 1.1 and 1.2. The analytic inputs from the literature are hypotheses of the
formal theorems. Section 7 of the paper describes the proof.

The main theorems are in `Romanoff/Theorems.lean`:

    theorem Romanoff.romanoff_U2 (h1 : ESP28 ell) (h3 : PNTAP ell) (h5 : R0Bound) : U2Statement
    theorem Romanoff.romanoff_v3 (h1 : ESP28 ell) (h2 : JTProp2) (h3 : PNTAP ell) (h5 : R0Bound) : V3Statement

The definitions are in `Romanoff/Defs.lean`:

- `U2Statement` is `(109406 / 1000000 : ℝ) ≤ liminf dens atTop` and `V3Statement` the same with 117953 / 1000000.
  Here `dens N` is N⁻¹ times the number of n with 1 ≤ n ≤ N and n = p + 2^a for a prime p and a ≥ 1. The lemma
  `lowerDensityGe_iff` gives the equivalent form: for every ε > 0, eventually `c - ε ≤ dens N`.
- `ell` is the modulus 3·5·7·11·13·17·31·41·241 = 78,187,414,305.
- `ESP28 ell` is the per-class bound (2.1) of the paper (Elsholtz and Schlage-Puchta, Math. Z. 288 (2018), (28)) for
  the modulus `ell`, and `JTProp2` is the bound (2.2) for the total (Johnston and Trudgian, arXiv:2605.17825,
  Proposition 2, from Lichtman, arXiv:2309.08522, Theorems 1.2 and 1.7). Both have the upper bound
  `C0up = 0.66016181584686958` in place of the twin prime constant C₀, which only weakens them.
- `PNTAP ell` is the prime number theorem in progressions modulo `ell`.
- `R0Bound` states that every finite partial sum of the series R₀ of (2.3) is at most 1.93656.

Pintz's inequality (Lemma 2.1 of the paper) is proved, not assumed.

## Axioms

`lake env lean Axioms45.lean` prints the definitions, the statements and the axioms; `results/axioms_shipped.txt` is
its output from a build of this directory. Each of the two theorems depends on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound` and on four auxiliary axioms, one for each check evaluated by `native_decide`,
which runs compiled code:

- `R45.M3.certOK_data`: the list of certified primes and the orders of 2 modulo them (the check `certOK` of
  `RCert/M3/Check.lean`);
- `R45.M3.sumsOK_data`: the lower sums for R₀;
- `R45.M3.teffD_eq`: the table of the 120 upper bounds T⁺(c) computed from these data equals the literal table in
  `RCert/M3/TeffLit.lean`;
- `R45.P45.cert_U2_lit` (for `romanoff_U2`) or `R45.P45.cert_v3_lit` (for `romanoff_v3`): the Lagrangian bound (4.5)
  of the paper, evaluated with this table, is at least 0.109406 or 0.117953 (`RCert/Cert45Check.lean`).

The first three are proved in `RCert/M3/NCheck.lean`.

So the trusted base includes the Lean compiler, the C compiler that it uses, the Lean runtime and the compiled
core-library functions that the checks call. The rest of the proof uses only the three standard axioms, in particular
`Romanoff.lagR_le_liminf`, which bounds the density from below by the Lagrangian bound for any table of upper bounds
for the sums T(c).

## How the proof works

- `Romanoff/`: the analytic part of the proof: the first moment in each class from the prime number theorem in
  progressions (`FirstMoment.lean`), the moments of the number of representations (`Moments.lean`), the pair counts
  against the hypotheses (`PairBounds.lean`, `M4B.lean`), the singular series and its mean value (`Sing.lean`,
  `SingSeries.lean`, `ETail.lean`), Pintz's inequality (`Pintz.lean`), the residue classes and their patterns modulo
  rotation (`Classes.lean`, `FoldSound.lean`, `OrbSound.lean`), the Lagrangian bound (`LPFinite.lean`, `LagSound.lean`),
  the link between the evaluation program and the sums over the residue classes (`M4C.lean`), the assembly at one N
  (`Assembly.lean`, `Assembly2.lean`) and the passage to the limit (`M4E.lean`, `Final.lean`, `Theorems.lean`).
  `Log2.lean` proves 0.693147180559945309 < log 2 < 0.693147180559945310.
- `Romanoff/M3/` and `RCert/M3/`: the upper bounds T⁺(c). Primes above 2¹⁶ are certified by Pratt certificates, smaller
  ones by trial division, and the order t of 2 modulo each prime by 2^t ≡ 1 and 2^(t/r) ≢ 1 for the primes r dividing t.
  A dynamic program over these primes in fixed-point integer arithmetic, with lower and upper bounds, gives the table;
  `Romanoff/M3/Sound.lean` proves that it bounds the sums T(c) from above under `R0Bound`.
- `RCert/`: the checking programs and data in core Lean, compiled to native code: the residue patterns and the
  evaluation of the Lagrangian bound (`Patt.lean`, `Lag.lean`, `Data45.lean`, `Cert45Check.lean`).
- `tools/gen_data45.py` and `M3/tools/` (with the inputs in `M3/data/`) wrote the generated data files
  `RCert/Data45.lean`, `RCert/M3/Data.lean` and `RCert/M3/TeffLit.lean`. They need not be trusted: every generated
  value is either checked by a proof or enters an inequality that holds for any value of it.

## Building

Install `elan`, the Lean toolchain manager. `lean-toolchain` selects Lean `v4.35.0-rc3`, and `lake-manifest.json` pins
Mathlib at commit `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). Then run

    lake exe cache get
    lake build Romanoff.Theorems
    lake env lean Axioms45.lean

`lake exe cache get` should download compiled Mathlib files; without them, `lake build` compiles Mathlib from source,
which takes much longer. With compiled Mathlib in place, `lake build Romanoff.Theorems` took 8 minutes 35 seconds on 8
cores (about 800 CPU-seconds for the 72 modules of the project) and at most 6.9 GB of memory, most of it for the
compiled checks in `RCert/Cert45Check.lean` and `RCert/M3/NCheck.lean`. The output of the last command should agree with
`results/axioms_shipped.txt`.
