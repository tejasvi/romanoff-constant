# Lean 4 proofs of d ≥ 0.110825 and, assuming (I2), d ≥ 0.119178 for Romanoff's constant (certificates U3g, V4g)

This directory contains Lean 4 (v4.35.0-rc3) proofs, with Mathlib (see `lake-manifest.json`), of

```lean
theorem Romanoff.G.romanoff_U3g (h1 : ESP28 G.ell) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.U3gStatement
theorem Romanoff.G.romanoff_V4g (h1 : ESP28 G.ell) (h2 : JTProp2) (h3 : PNTAP G.ell) (h5 : R0Bound) : G.V4gStatement
```

where `G.U3gStatement : Prop := (110825 / 1000000 : ℝ) ≤ liminf dens atTop`, `G.V4gStatement : Prop := (119178 / 1000000
: ℝ) ≤ liminf dens atTop` and `G.ell = 3·5·7·11·13·17·31·241·41·19·73·37·23·43·29`, the modulus `l_3` of the paper
(Romanoff/G/Spec.lean); the two theorems are Theorems 1.1 and 1.2 of the paper. Here `dens N` (Romanoff/Defs.lean) is
N⁻¹ times the number of n with 1 ≤ n ≤ N and n = p + 2^a for a prime p and a ≥ 1. The hypotheses `ESP28 G.ell`, `PNTAP
G.ell` and `R0Bound` are the per-class bound (2.1), the prime number theorem in progressions and the bound (2.3) of the
paper, at this modulus; `JTProp2` is Proposition 2 of Johnston and Trudgian with the budget constant 6.7814. Below they
are called (I1), (I3), (I5) and (I2).

**Scope.** Both theorems are verified in Lean 4 with Mathlib. U3g is conditional on (I1), (I3) and (I5), and V4g also on
(I2). The proof relies on compiled evaluation (`native_decide`) for its six finite checks, with one auxiliary axiom for
each: five for the period-27720 tables and one for the evaluation of the two bounds. With these six auxiliary axioms
admitted, the exported proof is accepted by two independent kernel implementations: Lean's own kernel, run by
leanchecker, and lean4lean. A third type checker, nanoda, gave no verdict. It crashed with an internal error ("index
2147483648 exceeds 31-bit capacity", exit code 101) and reported no error in the proof. `results/axioms_shipped.txt`
lists the axioms: `propext`, `Classical.choice`, `Quot.sound` and the six `native_decide` auxiliaries.

## Structure

Stage 1 (the period-27720 tail bound and the reductions):
- `tboundALit : R0Bound → TBoundA (tabB BLit) R0tLit` (Romanoff/G/Lit.lean): the class-(a)/(b) tables at period 27720
  (Romanoff/G/M3/*, RCert/M3G/*) in divisor form `tabB B c = Σ_{g ∣ 27720, g ∣ c} B_g`, with 96 values `BLit` that
  `tabB_BLit_eq` checks against the per-residue table. Native checks: `certOK_data`, `sumsOK_data`, `teffD_eq`,
  `R0tD_eq`, `tabB_BLit_eq`.
- `lagR_le_liminf` at period 27720 (Romanoff/G/SingSeries … Final), `liminf_ge_of_TBoundA` (Romanoff/G/Reduce.lean, μ =
  0) and `liminf_ge_of_TBoundA_mu` (Romanoff/G/ReduceMu.lean, a uniform budget multiplier μ ≥ 0 with (I2)). By these
  reductions, it suffices to bound `lagBound (parOf (teffA (tabB BLit) α) C1 μ) (orbits 27720 ellPrimes)` below for
  every rational `α ≥ 0` with `Σ_g α_g ≤ R0t + δ`.

Stage 2 (Romanoff/G/S2/*), in which no file except Native.lean contains a `native_decide` (Final.lean also uses the five
stage-1 native facts, through `tboundALit`):
- The evaluator RCert/G/Ev.lean (constants RCert/G/EvData.lean) is written in core Lean and runs as compiled code. It
  works on core rows at period 360: the rotation orbits of the BASE primes 3, 5, 7, 11, 13, 17, 31 and 241 (the prime
  factors of `l'` in the paper), `foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241]`, lifted to 360 bits, times the options
  of the primes 41, 19, 73 and 37. For each core row it computes the class counts mod 4 for the divisors of 360 and, for
  each of the 38 patterns of the residues of 23, 43 and 29, the row size `|U|` and `Q = Σ_g ⌈B_g 2^32⌉ S_g(U)` at period
  27720, and adds them to the slot of the row's Pintz index. One evaluation serves both bounds.
- Crt.lean proves the reduction of Section 6 of the paper (the paragraph on the modulus `l_3`) for every row of product
  form: by the Chinese remainder theorem for 27720 = 360 · 7 · 11, `S_{g_c τ} = Σ_{u,v<4} W7(u,v) W11(u,v) T_{g_c}(u,v)`
  and `|U| = Σ_u f7(u) f11(u) n_u`, with `T` and `n` the class counts of the core row.
- Ind.lean shows that the rows of the residues of 23, 43 and 29 have product form, checks the tables of every residue
  against its pattern (see below) and regroups the residues by pattern with their weights. Row.lean identifies the
  evaluator's `(|U|, Q)` of a pattern with the exact values of each of its rows.
- Mino.lean writes `lagBound` as a sum over classes, with the budget term spread over the classes, and bounds one row:
  weak duality on the cap of a class, Pintz's inequality, `B_g ≤ ⌈B_g 2^32⌉/2^32` and the tail by `g S_g ≤ 27720 |U|`.
- Value.lean, Lift.lean and Key.lean: the linearity of the accumulators, the lifts of the masks from 120 and 360 bits to
  27720 bits, and `lagBound_ge_Vf`, the inequality for both parameter sets (U3g: μ = 0; V4g: μ = 687217/10^12, C1 =
  6.7814, with the optimal integer `i*(J)` of the minorant from `istarV`, checked by `decide`).
- Native.lean: `finalOK_true : finalOK 123 = true`, i.e. `110825/10^6 ≤ VU` and `119178/10^6 ≤ VV` for the accumulators
  `evalPar 123 (foldOrbits 120 baseP)`. Final.lean, U3g.lean and V4g.lean assemble the theorems, with `δ = 10^-12`.

### The patterns

The certificate checker (`check/check_r45u3f_a028b118.py` of the archive) groups the residue pairs `(r43, r29)` into the
23 orbits of Section 6 of the paper and the residues `r23` into 2. The evaluator groups them by their tables `(f(u),
W(u, v))` instead, which gives 19 patterns for q = 7 (and 2 for q = 11, 38 combined), since four pairs of orbit patterns
have identical tables. When `b43 = b29` and `a29 ≡ a43 (mod 2)`, the residues excluded by 29 (`e ≡ j29 mod 28`) lie
inside those excluded by 43 (`e ≡ j43 mod 14`), so the row is the row of `(a43, none)`. The proof does not use the orbit
argument. Instead, kernel `decide` checks the tables of all 1,247 residue pairs and all 23 residues of 23 against their
pattern (`tab7`, `tab11`), and `List.count` gives the weights, which add up to 1,247 = 43 · 29 and to 23. Every row
keeps its exact `|U|` and `S_g`.

## The values and the certificate checker's minima

A separate compiled evaluation of the same accumulators gives `VU = 0.1108276292…` and `VV = 0.1191809294…`; the bounds
0.110828 and 0.119181 would fail. The values exceed the bounds of Theorems 1.1 and 1.2 by 2.6e-6 and 2.9e-6, and the
certificate checker's minima 0.110825738804 and 0.119178909685, both attained at the tail vertex `g = 27720`, by 1.9e-6
and 2.0e-6. As for the proof in `lean_u3e/`, the values and the checker's minima rest on tables of the same form and
differ in the bound for the stopped branches of the dynamic program (DP), the classes whose lcm of orders exceeds LMAX =
3·10^6. The checker adds it to `B_1` at every residue, while the stage-1 table of this proof bounds it at residue `c` by
`⌈prM gcd(c, 27720) / LMAX⌉` (RCert/M3G/Defs.lean), which spreads the same mass over the divisors. The sum of the `B_g`
is 1.19767165 for the checker and 1.19766647 here. u3g/tools/chk_bg_compare_g.py recomputes the checker's `B_g` and,
with the sensitivities from the checker's vertex values, predicts the differences +1.89e-6 and +2.02e-6. The 2^-32 grid
of the `B_g` in the evaluator, `δ` and the rule for the Pintz index change the values by at most about 1e-9.

## Build

```
lake exe cache get
lake build Romanoff.G.U3g Romanoff.G.V4g
lake env lean Axioms45U3gV4g.lean
```

Native.lean evaluates both bounds in one pass, in 64 parallel pieces; it runs fastest with one physical core per piece.
It must run as compiled code. `RCert.G.Ev` is a root of the precompiled library `RCert` (lakefile.toml), and `lake
build` loads that library; a plain `lake env lean` on Native.lean would interpret the evaluator, about three times
slower. The rest of the build takes minutes once Mathlib is available.

## Generated files

- RCert/M3G/Data.lean: `python3 M3/tools/gen_data_lean_g.py M3/data/pratt_v1.json RCert/M3G/Data.lean`.
  M3/data/pratt_v1.json comes from M3/tools/gen_pratt.py and the certificates' factorization files fac300/fac1200.
- RCert/M3G/TeffLit.lean: `lake exe m3ggenlit > RCert/M3G/TeffLit.lean`.
- RCert/G/BLit.lean: `python3 u3g/tools/gen_blit_g.py RCert/M3G/TeffLit.lean RCert/G/BLit.lean`, the 96 values `B_g` by
  Möbius inversion of the per-residue table over the divisors of 27720. The file need not be trusted, since
  `tabB_BLit_eq`, a native check in RCert/G/BCheck.lean, states `tabB BLit c = teff(c) - gcd(c, 27720) R0t` for every `c
  < 27720`.
- RCert/G/EvData.lean: `python3 u3g/tools/gen_evg.py .` (divisors and count plan at 360, `⌈B_g 2^32⌉`, the pattern
  tables with their weights and residue signatures, the Pintz-index constants and `istarV`). Its tables need not be
  trusted either, since they enter the proof only through the kernel `decide` checks of Ind.lean, Mino.lean and
  Key.lean.

## Cross-checks

- `lake exe gpilot row K R41 R19 R73 R37 > row.out`, then `python3 u3g/tools/xcheck_row_g.py . row.out 3` (needs numpy):
  for BASE key number `K` and core residues `r_p`, the evaluator's `(|U|, Q)` of every pattern against a brute-force
  count at period 27720 of up to 3 residue triples per pattern. results/xcheck_rows.log: 4 core rows, 456 full rows, no
  mismatch. `lake exe gpilot time N` times `N` BASE keys on one thread.
- `python3 u3g/tools/chk_bg_compare_g.py CERTS_DIR RCert/G/BLit.lean U3G_LOG V4G_LOG` compares the Lean table with the
  certificate checker's divisor form and predicts the differences between the values and the checker's minima.
  `CERTS_DIR` must contain fac300_41e4cdd6.json and fac1200_fdb_af082adc.json, the certificates' factorization files;
  the logs are the checker's runs at the bounds of Theorems 1.1 and 1.2, logs/u3f_u3g27720_96663daa.log and
  logs/u3f_v4g27720_6557658d.log.

## Notes

- The docstring of Romanoff/CertK.lean refers to Romanoff/CertKFinal.lean, and RCert/Data45.lean names its generator and
  the period-120 certificate files; these belong to the proofs in `lean/` (`romanoff_U2`, `romanoff_v3`) and are not
  shipped here.
- Axioms45U3gV4g.lean prints the types and the axioms of both theorems; results/axioms_shipped.txt holds that output.
