# Lean 4 proof of the bound d ≥ 0.110449 for Romanoff's constant (certificate r45a-u3e)

This directory contains a Lean 4 (v4.35.0-rc3) proof, with Mathlib (see `lake-manifest.json`), of

```lean
theorem Romanoff.E.romanoff_U3e (h1 : ESP28 E.ell) (h3 : PNTAP E.ell) (h5 : R0Bound) : E.U3eStatement
```

where `E.U3eStatement : Prop := (110449 / 1000000 : ℝ) ≤ liminf dens atTop` and
`E.ell = 3·5·7·11·13·17·31·241·41·19·73·23·37` (Romanoff/E/Spec.lean). Here `dens N` (Romanoff/Defs.lean) is N⁻¹ times
the number of n with 1 ≤ n ≤ N and n = p + 2^a for a prime p and a ≥ 1. The hypotheses `ESP28 E.ell`, `PNTAP E.ell` and
`R0Bound` are the per-class bound (2.1), the prime number theorem in progressions and the bound (2.3) of the paper, at
this modulus. In the certificate notes they are the inputs (I1), (I3) and (I5).

**Scope.** The theorem is verified in Lean 4 with Mathlib, conditional on these three inputs, (I1), (I3) and (I5). Its
six finite checks are evaluated by `native_decide`, with one auxiliary axiom for each. With these six auxiliary axioms
admitted, the exported proof is accepted by three independent kernel implementations: Lean's own kernel, run by
leanchecker, and the independent type checkers nanoda and lean4lean. `results/axioms_shipped.txt` lists the axioms:
`propext`, `Classical.choice`, `Quot.sound` and the six `native_decide` auxiliaries.

## Structure

Stage 1 (the period-3960 tail bound and the reduction):
- `tboundALit : R0Bound → TBoundA (tabB BLit) R0tLit` (Romanoff/E/Lit.lean): the class-(a)/(b) tables at period 3960
  (Romanoff/E/M3/*, RCert/M3E/*) in divisor form `tabB B c = Σ_{g ∣ 3960, g ∣ c} B_g`, with 48 values `BLit` that
  `tabB_BLit_eq` checks against the per-residue table. Native checks: `certOK_data`, `sumsOK_data`, `teffD_eq`,
  `R0tD_eq`, `tabB_BLit_eq`.
- `lagR_le_liminf` at period 3960 (Romanoff/E/SingSeries … Final) and `liminf_ge_of_TBoundA` (Romanoff/E/Reduce.lean):
  it suffices to bound `lagBound (parOf (teffA (tabB BLit) α) 8 0) (orbits 3960 ellPrimes)` below for every rational
  `α ≥ 0` with `Σ_g α_g ≤ R0t + δ`.

Stage 2 (Romanoff/E/S2/*), in which every file except Native.lean uses only the standard axioms:
- The evaluator RCert/E/Ev.lean is written in core Lean and runs as compiled code. Its classes are the BASE rotation
  orbits, `foldOrbits 3960 [3, 5, 7, 11, 13, 17, 31, 241]`, times the options of the primes 41, 19, 73, 23 and 37. For
  each row it computes `|U|` and `Q = Σ_g ⌈B_g 2^36⌉ S_g(U)` and adds them to the slot of the row's Pintz index.
- `lagBound_ge_V` (Key.lean) proves `V (evalPar k (foldOrbits 3960 BASE)) ≤ lagBound …` for every such `α` and every
  piece size `k`, from Basic.lean (counts, `S_g`, `g S_g ≤ 3960 |U|`), Arr.lean (count arrays), Cross.lean (the classes
  of 37 by the Chinese remainder theorem), Value.lean (linearity of `V`), Mino.lean (the minorant of one row: Pintz's
  inequality, the divisor lemma, `B_g ≤ ⌈B_g 2^36⌉/2^36`, the tail by `g S_g ≤ 3960 |U|`).
- Native.lean: `finalOK_true : finalOK baseP 88 = true`, i.e. `110449/1000000 ≤ V (evalPar 88 (foldOrbits 3960 baseP))`;
  the value of `V` is discussed in the next section.
- Romanoff/E/U3e.lean assembles the theorem, with `δ = 10^-12`.

## V and the certificate checker's minimum

The evaluated value is `V = 0.110450135328…`. It exceeds the claim 0.110449 by 1.14e-6 and the certificate checker's
minimum 0.110449798661, attained at the tail vertex `g = 3960`, by 3.37e-7. Both rest on tables of the same form,
`T(c) ≤ Σ_{g ∣ 3960, g ∣ c} B_g + gcd(c, 3960) R0t`; they differ in the bound for the stopped branches of the DP, that
is, the classes whose lcm of orders exceeds LMAX = 3·10^6:
- The certificate checker bounds their contribution by a constant at every residue, i.e. adds it to `B_1`: 2.9466e-6 for
  class (a) and 5.661e-7 for class (b).
- The stage-1 table of this proof (RCert/M3E/Defs.lean, `prC`) bounds it at residue `c` by `⌈prM gcd(c, 3960) / LMAX⌉`,
  where `prM` is the stopped mass; in divisor form this spreads the same mass over the divisors `g` with weights `φ(g)`.
So `B_1` is 1.002833409093 for the checker and 1.002829897005 here (`BLit`), and the `B_g` with `g > 1` are slightly
larger here. Since `S_1 = |U|^2` is by far the largest `S_g`, the checker's `Q` is larger. The checker's own
sensitivities `-∂V/∂B_g > 0`, obtained from its vertex values, give `Σ_g (B^checker_g - BLit_g) (-∂V/∂B_g) = +3.367e-7`,
which matches the evaluated `V`; u3e/tools/chk_bg_compare.py recomputes the checker's `B_g` and this sum. The 2^-36 grid
of the `B_g` in the evaluator, `δ` and the rule for the Pintz index change `V` by at most about 1e-9.

## Build

```
lake exe cache get
lake build Romanoff.E.U3e
lake env lean Axioms45U3e.lean
```

Native.lean evaluates the bound in 90 parallel pieces, which takes about 50 minutes on 90 cores. One piece per physical
core is the fastest setting. It must run as compiled code: `RCert.E.Ev` is a root of the precompiled library `RCert`
(lakefile.toml), and `lake build` loads that library; a plain `lake env lean` on Native.lean would interpret the
evaluator, about three times slower. The rest of the build takes minutes once Mathlib is available.

## Generated files

- RCert/M3E/Data.lean: `python3 M3/tools/gen_data_lean_e.py M3/data/pratt_v1.json RCert/M3E/Data.lean`.
  M3/data/pratt_v1.json comes from M3/tools/gen_pratt.py and the certificate's factorization files fac300/fac1200.
- RCert/M3E/TeffLit.lean: `lake exe m3egenlit`.
- RCert/E/EvData.lean: `python3 u3e/tools/gen_ev.py .`.
- RCert/E/BLit.lean: the 48 values `B_g`, by Möbius inversion of the per-residue table over the divisors of 3960. No
  generator is shipped. The file need not be trusted: `tabB_BLit_eq`, a native check in RCert/E/BCheck.lean, states
  `tabB BLit c = teff(c) - gcd(c, 3960) R0t` for every `c < 3960`, and these equations determine every `B_g`.

## Cross-checks

- `python3 u3e/tools/xcheck_key.py INDEX .` recomputes the accumulators of one BASE key by direct counts with numpy.
- `python3 u3e/tools/chk_bg_compare.py CERTS_DIR RCert/E/BLit.lean` compares the Lean table with the certificate
  checker's divisor form and predicts the difference between `V` and the checker's minimum. `CERTS_DIR` must contain
  fac300_41e4cdd6.json and fac1200_fdb_af082adc.json, the certificate's factorization files, and the checker's run log
  under the name u3e_23_37.log. In the archive the log is logs/u3e_u3e2337_2c4b8603.log; copy or link it under that
  name.

## Notes

- The comments of Romanoff/E/Spec.lean, Romanoff/E/U3e.lean, RCert/E/Params.lean and RCert/E/Ev.lean write `l'` for the
  13-prime modulus `E.ell`. In the paper, `l'` denotes 3·5·7·11·13·17·31·241.
- The docstring of Axioms45U3e.lean refers to u3e/runlogs/check_u3e.out, a run log that is not shipped;
  results/axioms_shipped.txt holds that output.
