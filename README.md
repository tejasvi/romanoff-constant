# New lower bounds for Romanoff's constant (version 10)

Programs and data for the paper *New lower bounds for Romanoff's constant* by Tejasvi Singh Tomar
(doi:10.5281/zenodo.23609839). The programs, the data and five proofs in Lean 4, two of the two theorems and three of
weaker bounds, are archived at doi:10.5281/zenodo.23609840.

This is version 10 of the archive; the section Versions at the end lists the changes from earlier versions. Section,
proposition, lemma and equation numbers refer to the paper unless another source is named.

## Results

Let `d` be the lower density of the set of integers `p + 2^a` with `p` prime and `a >= 1`. The paper proves

    d >= 0.110825                                                                  (Theorem 1.1)
    d >= 0.119178, assuming a bound deduced from Lichtman's Theorems 1.2 and 1.7   (Theorem 1.2)

The best lower bound in the literature was 0.10788, from the method of Elsholtz and Schlage-Puchta (Math. Z. 288 (2018),
end of p. 721; recomputed by Johnston and Trudgian, arXiv:2605.17825v2). Theorem 1.2 assumes the bound of Proposition 2
of Johnston and Trudgian, which they deduce from Theorems 1.2 and 1.7 of J. D. Lichtman, arXiv:2309.08522. Both papers
are preprints. Theorem 1.1 uses neither. Theorems 1.1 and 1.2 are proved in Lean twice: in `lean_u3g/`, with compiled
checks, and in `lean_u3g_kernel/`, with all computations checked by the Lean kernel. Three further Lean proofs establish
weaker bounds: the one in `lean_u3e/` gives `d >= 0.110449`, the bound of the same method for the modulus `l_1` below,
and the other two give `d >= 0.109406` and, under the same assumption, `d >= 0.117953`. In all five the analytic inputs
from the literature are hypotheses.

## Method

The integers are split into residue classes modulo an odd squarefree integer `l`. In each class the second moment of the
number of representations is bounded with the per-class sieve bound of Elsholtz and Schlage-Puchta, whose constant 8 is
four times the Hardy-Littlewood prediction. The singular series is bounded with the prime factors of `2^t - 1` for
`t <= 1200` (Section 5).

- Theorem 1.1 uses `l_3 = 29*43*l_1`, where `l_1 = 3*5*7*11*13*17*19*23*31*37*41*73*241`. The period of `2^a` modulo
  `l_3` is 27720, and modulo `l_1` it is 3960. For the part of the singular series that is not computed, only an upper
  bound for its total is known, not its distribution over the divisors of the period. Bounding Pintz's function in each
  class from below by one of the linear functions of which it is the maximum makes the bound affine in this
  distribution, so its minimum over all distributions is attained at one of 97 extreme ones for `l_3` (Proposition 4.2).
  The checker evaluates the bound exactly at all 97. For `l_1` the same method gives `d >= 0.110449`, with 49 extreme
  distributions.
- Theorem 1.2 uses the same modulus `l_3` and also bounds the total over all classes with the constant 6.7814 of
  Johnston and Trudgian, through one Lagrange multiplier for the total and one for the caps of each class (Proposition
  4.3). For `l_1` the same method gives `d >= 0.118859`.
- The bounds `d >= 0.109406` and `d >= 0.117953` come from a linear program over the distribution of the pair counts
  among the classes, for `l = 3*5*7*11*13*17*31*41*241`, with period 120, and the tail bound `gcd(c, P) theta`. A
  Lagrangian certificate (one multiplier per difference class, Section 4) bounds its minimum from below; for the first
  bound all multipliers are zero, so the constant 6.7814 plays no role. `lean/` and `lean_kernel/` contain Lean proofs
  of these two bounds.

## Contents

In this README, *the main checker* is `check/check_r45u3f_a028b118.py`, *the u3e checker* is
`check/check_r45u3e_7e8e7170.py`, *the v3 checker* is `check/check_r45u3x_2cefa154.py`, and *the first checker* is
`check/check_r45a5_rel2_3cf71761.py`. The names of the programs, data files and logs end with the first eight hex digits
of the file's SHA-256. "Earlier" marks files from previous versions of the archive (see Versions).

| Path | Content |
|---|---|
| `check/check_r45u3f_a028b118.py` | the checking program for Theorems 1.1 and 1.2 (period 27720) |
| `check/cert_u3g_27720_703c7aee.json` | the certificate of Theorem 1.1 |
| `check/cert_v4g_27720_95ae70b9.json` | the certificate of Theorem 1.2 |
| `check/u3e_to_u3f_ae792b11.diff`, `check/rel2_to_u3f_dc3ad2c3.diff` | the changes to this checker from the u3e checker and from the first checker |
| `check/cert_u3f_repro_12c92a51.json`, `check/test_cert_t1_u3e_c0395af7.json`, `check/test_cert_t1_u3f_642b5a5a.json`, `check/test_cert_t2_u3e_b1fdae48.json`, `check/test_cert_t2_u3f_43e56246.json` | certificates for its tests below |
| `check/test_ref_u3e_batched_518e70a9.py` | a copy of the u3e checker for one of these tests, with exact group sums (below) |
| `check/check_r45u3e_7e8e7170.py` | the checking program for the bounds 0.110449 and 0.118859 (modulus `l_1`) |
| `check/cert_u3e_23_37_a0644bf2.json` | the certificate of the bound `d >= 0.110449` |
| `check/cert_v4e_23_37_5d9c3a60.json` | the certificate of the bound `d >= 0.118859` |
| `check/cert_v4d_37e_763ec021.json` | an earlier certificate for 0.118747, with the modulus `l_1/23` |
| `check/cert_u3d_37e_305b0bd9.json`, `check/cert_u3d_perm_2e5fe6fa.json`, `check/cert_u3e_73_f4510070.json`, `check/cert_u3e_41_23_4c20954a.json`, `check/cert_u3e_23_41_64008dfe.json`, `check/cert_u3e_41_aac6e106.json`, `check/cert_u3d_u3x_43bc59a1.json`, `check/cert_v4d_u3x_69a4a859.json` | certificates for the tests below |
| `check/rel2_to_u3e_5800af3a.diff`, `check/u3x_v3_to_u3e_82e5c280.diff` | the changes to this checker from the first checker and from the v3 checker |
| `check/check_r45u3x_2cefa154.py` | the v3 checker, which keeps the bounds for the singular series per residue |
| `check/cert_u3c_73_18aa78b6.json`, `check/cert_v4bb_73_73e5cf24.json` | earlier certificates for 0.110118 and 0.118601 |
| `check/cert_u3b_19_bc628a98.json` | a certificate with the added primes 41 and 19 only (0.109943846) |
| `check/cert_u3x_41_ad7a2738.json`, `check/cert_u3a_c2728dff.json` | the test of the splitting of `l` (below) |
| `check/rel2_to_u3x_cb818175.diff` | the changes from the first checker to the v3 checker |
| `check/check_r45a5_rel2_3cf71761.py` | the checking program for the bounds `d >= 0.109406` and `d >= 0.117953` (the first checker) |
| `check/cert_p120b_v3_6fd62e90.json` | the certificate of the bound `d >= 0.117953` |
| `check/cert_p120b_uncond_af1c16be.json` | the certificate of the bound `d >= 0.109406` (all multipliers zero) |
| `check/fac300_41e4cdd6.json` | the complete factorizations of `Phi_t(2)` for `t <= 300` |
| `check/fac1200_fdb_af082adc.json` | factorizations of `Phi_t(2)` for `301 <= t <= 1200` |
| `controls/` | four altered certificates that the u3e checker rejects, with its output |
| `logs/` | the output of the checking runs and of runs of the floating-point models `scan45d.py` and `scan45e.py`; `logs/review/` holds the runs of an independent review on another machine |
| `reproduce/` | the programs that produced the data and the certificates (not needed for checking) |
| `lean/` | the proof of the bounds `d >= 0.109406` and `d >= 0.117953` in Lean 4, with compiled checks (see `lean/README.md`) |
| `lean_kernel/` | a second proof of the same two bounds in Lean 4, checked by the Lean kernel alone (see `lean_kernel/README.md`) |
| `lean_u3e/` | the proof of the bound `d >= 0.110449` in Lean 4, with compiled checks (see `lean_u3e/README.md`) |
| `lean_u3g/` | the proofs of Theorems 1.1 and 1.2 in Lean 4, with compiled checks (see `lean_u3g/README.md`) |
| `lean_u3g_kernel/` | the proofs of Theorems 1.1 and 1.2 in Lean 4, checked by the kernel alone (see `lean_u3g_kernel/README.md`) |
| `SHA256SUMS` | the SHA-256 checksums of all other files |

## Checking

The checkers need Python 3 with python-flint (tested with 0.9.0) and numpy. In the directory `check`:

    python3 -I check_r45u3f_a028b118.py fac300_41e4cdd6.json cert_u3g_27720_703c7aee.json 3000000 fac1200_fdb_af082adc.json 1200 --claim 0.110825 --workers 42
    python3 -I check_r45u3f_a028b118.py fac300_41e4cdd6.json cert_v4g_27720_95ae70b9.json 3000000 fac1200_fdb_af082adc.json 1200 --claim 0.119178 --workers 42
    python3 -I check_r45u3e_7e8e7170.py fac300_41e4cdd6.json cert_u3e_23_37_a0644bf2.json 3000000 fac1200_fdb_af082adc.json 1200 --claim 0.110449 --workers 80
    python3 -I check_r45u3e_7e8e7170.py fac300_41e4cdd6.json cert_v4e_23_37_5d9c3a60.json 3000000 fac1200_fdb_af082adc.json 1200 --claim 0.118859 --workers 42
    python3 -I check_r45a5_rel2_3cf71761.py fac300_41e4cdd6.json cert_p120b_v3_6fd62e90.json 3000000 fac1200_fdb_af082adc.json 1200 --claim 0.117953
    python3 -I check_r45a5_rel2_3cf71761.py fac300_41e4cdd6.json cert_p120b_uncond_af1c16be.json 3000000 fac1200_fdb_af082adc.json 1200 --claim 0.109406

The runs of these commands, in the same order:

| run | worker processes / threads of the machine | time | log | claim raised by `1e-6` (`FAIL`, exit code 1) | runs of the review |
|---|---|---|---|---|---|
| Theorem 1.1, `--claim 0.110825` | 42 / 44 | about 3.2 hours | `logs/u3f_u3g27720_96663daa.log` | `logs/u3f_u3g27720_above_89238c30.log` | `logs/review/u3f_u3g27720_8e98b047.log`, `logs/review/u3f_u3g27720_above_45e14172.log` (96 / 384, about 35 minutes each) |
| Theorem 1.2, `--claim 0.119178` | 42 / 44 | about 3.2 hours | `logs/u3f_v4g27720_6557658d.log` | `logs/u3f_v4g27720_above_b56d66db.log` | `logs/review/u3f_v4g27720_adbbd4f6.log`, `logs/review/u3f_v4g27720_above_fa58e65d.log` (96 / 384, about 35 minutes each) |
| the bound 0.110449, `--claim 0.110449` | 80 / 96 | about 45 minutes | `logs/u3e_u3e2337_2c4b8603.log` | `logs/review/u3e_u3e2337_above_c735e7cc.log` | `logs/review/u3e_u3e2337_b436f95f.log` |
| the bound 0.118859, `--claim 0.118859` | 42 / 44 | about 2 hours | `logs/u3e_v4e2337_6eff9e57.log` | `logs/u3e_v4e2337_above_7883abe7.log`, `logs/review/u3e_v4e2337_above_db187433.log` | `logs/review/u3e_v4e2337_d5f14078.log` |
| `d >= 0.117953`, `--claim 0.117953` | 1 | about 29 minutes | `logs/rel2_v3_37d572d2.log` |  |  |
| `d >= 0.109406`, `--claim 0.109406` | 1 | about 24 minutes | `logs/rel2_u2_cad2f274.log` |  |  |

The runs of the review printed the same vertex values as the runs in the column "log". An earlier run of the
certificates of Theorems 1.1 and 1.2, with `--claim 0.1105` and `--claim 0.1188`, printed the same 97 vertex values.
Logs: `logs/u3f_u3g27720_first_bcb0b0d1.log`, `logs/u3f_v4g27720_first_d7f9ea4c.log`.

Each run prints the certified value and the value rounded down, and ends with `PASS` and exit code 0 if the certified
value is at least the claim. The line `CERTIFIED` gives the smallest value rounded to the nearest multiple of `1e-9`.
For Theorems 1.1 and 1.2 and for the bounds 0.110449 and 0.118859 this rounding goes up: the lines for the vertices show
the smallest values to 12 digits, 0.11082573880..., 0.11917890968..., 0.11044979866... and 0.11885963462..., and the
line `CERTIFIED` shows them rounded up in the ninth decimal. The line `rounded down` and the comparison with the claim
are exact. `3000000` is the bound at which the dynamic program over the orders stops a branch, and `1200` is the largest
order of 2 modulo the primes of class (b) (Section 5). Without the arguments
`fac1200_fdb_af082adc.json 1200` the checkers leave out class (b) and certify smaller values.

The first checker recomputes everything from the factorization files and the
certificate:
- It checks by multiplication that the factorizations for `t <= 300` are complete and proves every factor prime. For
  `301 <= t <= 1200` it checks the products and proves the primality and the order `t` of every factor below `10^100`
  that is coprime to `t`. It does not use the other factors.
- It computes the orders exactly, bounds the singular series in ball arithmetic and, for class (b), in floating point with
  outward rounding and a relative margin of `1e-9`.
- It builds the residue patterns and their rotation orbits and evaluates the Lagrangian bound in exact rational arithmetic.

The certificate contains the prime factors of `l`, the multipliers and the external constants: the per-class constant 8,
the total constant 6.7814, `C0 < 0.66016181584686958` for the twin prime constant `C0`,
`0.693147180559945309 < log 2 < 0.693147180559945310` and `R0 < 1.93656` for the sum (2.3). In the
certificate of the bound `d >= 0.109406` the total constant is 8; it has no effect there, since all multipliers are zero.
The checker requires:
- the per-class constant to be at least 8 and the total constant at least 6.7814, both at most 100;
- `0.66016181584686958 <= C0_up <= 1`, `0.6931471805599453 <= log2_low <= 0.693147180559945309`,
  `0.693147180559945310 <= log2_up <= 0.6931471805599454` and `1.93656 <= R0_up <= 2`;
- the prime factors of `l` to be distinct odd primes, and the primes in each factorization to be distinct;
- the multipliers to be nonnegative.

It prints all parameters in its first line, and as a precaution it refuses to run under `python -O`.

The u3e checker contains the code of the first checker unchanged for the factorizations and the
external constants. For the bounds for the singular series it uses the dynamic program and the class-(b) sums of the
first checker, but adds them up per divisor of the period instead of per residue; `rel2_to_u3e_5800af3a.diff` lists every
change. From the v3 checker it keeps the code for the patterns, the orbits, the Pintz indices and the
vertices; `u3x_v3_to_u3e_82e5c280.diff` lists the changes. For a certificate of format `r45a-u3e` it evaluates the bound
of Proposition 4.2:
- It splits `l` into `l' = 3*5*7*11*13*17*31*241` and the added primes, 41, 19, 73, 23 and 37 for `l_1`. It
  enumerates the residue patterns modulo `l'` and the 7,870 rotation orbits of the nonempty ones, combines each orbit
  with all residues modulo the added primes, and checks that the class counts add up to `l` (Section 6).
- It groups the bounds for the singular series of classes (a) and (b) by the divisors `g` of the period: `T_0(c)` is the
  sum of the numbers `B_g` over the `g` that divide `c` (Section 5), each `B_g` rounded up to a multiple of
  `2^-48`; the bounds for the branches that the dynamic program stops go into `B_1`. For each combination it computes
  the size of the pattern, the sums `S_g` and `Q = sum_g B_g S_g` of Proposition 4.2 exactly in integers. The residues
  modulo the last added prime, 37, are evaluated together from the counts of one pattern in the classes modulo the
  divisors of the period.
- It chooses the Pintz index of each combination in floating point, at the point given by the certificate's field
  `alpha_j`. This choice affects only how good the bound is.
- It evaluates the bound at all vertices of the simplex, 49 for the period 3960 and 25 for 360, in exact rational
  arithmetic, prints all values and certifies the smallest.

Besides the checks of the first checker, it requires:
- the tail mode `alpha_simplex` and no multipliers per difference class (the field `duals` of the first checker);
- the added primes to be distinct prime factors of `l`, and `l'` to be nonempty;
- the number of orbits to match the certificate;
- the point `alpha_j` to lie in the simplex, on divisors of the period, and the Pintz indices to be at least 1;
- integer bounds under which all its int32 and int64 arithmetic is exact.

It starts its worker processes with `fork`, which needs Linux or macOS. The certificates `cert_v4e_23_37` and
`cert_v4d_37e_763ec021.json` have a field `mu`, the multiplier of Proposition 4.3, which must be
nonnegative, and their total constant is 6.7814; the checker then evaluates the bound of Proposition 4.3 in the same
way. The other certificates of format `r45a-u3e` here have no such field, so the total bound is not used, and their
total constant 8 has no effect.

The tests of the u3e checker are listed with those of the main checker in the table below.

The main checker is the u3e checker with a branch for the format `r45a-u3f` (`u3e_to_u3f_ae792b11.diff` lists every
change; `rel2_to_u3f_dc3ad2c3.diff` lists the changes from the first checker). The bounds for the singular series and
the numbers `B_g` are computed as in the u3e checker, and the new branch repeats its rotation orbits modulo `l'`, its
rule for the Pintz indices, the evaluation at the vertices and the claim check. For a certificate with a field `mu`,
such as the certificate of Theorem 1.2 (`mu = 687217/10^12`, total constant 6.7814), it evaluates the bound of
Proposition 4.3 in the same way as the u3e checker. Unlike the u3e checker, it runs through the exclusions
by the core added primes one at a time, without the joint evaluation at the last added prime. The certificate lists in
the field `IND` primes `q` that divide the period `P` exactly once, so that `P = P_c prod q` with `P_c` prime to each
`q`; for the certificates of Theorems 1.1 and 1.2 these are 7 and 11, and `P_c = 360`. The checker then:
- classifies every added prime `p` as a core prime (`ord_p(2)` divides `P_c`: here 41, 19, 73 and 37) or as attached to
  one `q` (`ord_p(2) = q m_p` with `m_p` dividing `P_c`: here 43 and 29 to 7, with `m_p = 2` and 4, and 23 to 11, with
  `m_p = 1`), and refuses any other case;
- writes the residues modulo the period as tuples (`r mod P_c`, `r mod 7`, `r mod 11`) and computes the sums `S_g` from
  the numbers of the residues modulo `P_c` that survive `l'` and the core primes in the classes modulo `lcm(g_c, M)`,
  with `M = 4` the least common multiple of the `m_p` (Section 6);
- evaluates one combination of exclusions by the attached primes of each `q` for every orbit under the permutations of
  the residues modulo `q`, with the number of residue classes modulo the attached primes in the orbit as its
  multiplicity (no exclusion by `p` stands for `p - ord_p(2)` residues): 23 orbits of the 435 combinations for 7 and 2
  of the 12 for 11, so 46 in all; it checks that the multiplicities add up to `43*29 = 1247` and to 23;
- checks, before the floating-point matrix products that enter the bound, bounds under which every partial sum is an
  integer below `2^53`, so that the products are exact, and multiplies the sums by the multiplicities in Python
  integers.

The u3e checker and the main checker were tested as follows (Section 6). Vertex values agree when all 12
printed digits are equal.

| certificates | what is tested | checkers | result | logs |
|---|---|---|---|---|
| `cert_u3e_73_f4510070.json` | the earlier certificate `cert_u3c_73_18aa78b6.json` (the modulus `3*5*7*11*13*17*19*31*41*73*241`, period 360) in the format `r45a-u3e` | u3e and v3 | both certify 0.110118630 (`--claim 0.110118`); 24 of the 25 vertex values agree, and the value at `e_72` differs by `1e-12`, since the u3e checker rounds on the grid `2^-48` and the v3 checker on the grid `2^-40` | `logs/review/u3e_u3e73_9b11f98b.log`, `logs/u3x_u3c73_6c56e930.log` |
| `cert_u3d_u3x_43bc59a1.json`, `cert_v4d_u3x_69a4a859.json` | `cert_u3d_37e_305b0bd9.json` and `cert_v4d_37e_763ec021.json` (modulus `l_1/23`) in the format `r45a-u3x` of the v3 checker, which evaluates every exclusion at every added prime separately | v3 | `--claim 0.110277` and `--claim 0.118747` pass, with the smallest vertex values 0.110277417054 and 0.118747326926 of the u3e checker; all 25 vertex values agree for `cert_v4d_37e`, and 23 for the other (`e_8` and `e_45` differ by `1e-12`) | `logs/review/u3x_u3d37_878419da.log`, `logs/review/u3x_v4d37_754e23b3.log` (about 2.2 and 2.4 hours with 48 worker processes) |
| `cert_u3d_37e_305b0bd9.json`, `cert_v4d_37e_763ec021.json` | the unconditional and the conditional certificate for `l_1/23` | u3e | 0.110277417 and 0.118747326 (`--claim 0.110277`, `--claim 0.118747`); the review ran `cert_v4d_37e` at the claim and with `--claim 0.118748` (`FAIL`) | `logs/u3e_u3d37_0e81d689.log`, `logs/u3e_v4d37_8ebad28f.log`, `logs/review/u3e_v4d37_30fec38c.log`, `logs/review/u3e_v4d37_above_cdd7c1b1.log` |
| `cert_u3d_perm_2e5fe6fa.json` | `cert_u3d_37e` with the added primes in the order 41, 19, 37, 73, so that 73 instead of 37 is evaluated as the last added prime | u3e | in the review, the same 25 vertex values as `cert_u3d_37e` | `logs/review/u3e_u3d37_e38cf6e6.log`, `logs/review/u3e_u3d37perm_5338ef8d.log` |
| `cert_u3e_41_23_4c20954a.json`, `cert_u3e_23_41_64008dfe.json` | the added primes 41 and 23 (period 1320), with either of them last | u3e | both certify 0.109834575 (`--claim 0.109834`); the 33 vertex values agree | `logs/u3e_u3e4123_6b24f0d0.log`, `logs/u3e_u3e2341_5a7ff866.log` (about 3 minutes each with one worker process) |
| `cert_u3f_repro_12c92a51.json` | the certificate of the bound 0.110449 in the format `r45a-u3f`, with 11 split off and 23 attached to it | main and u3e | the same 49 vertex values | `logs/u3f_repro_ed46415b.log` (78 minutes with 42 worker processes on a machine with 44 threads), `logs/u3e_u3e2337_2c4b8603.log` |
| `test_cert_t1_u3f_642b5a5a.json`, `test_cert_t1_u3e_c0395af7.json` | one small certificate in the two formats: `l' = 3*5`, the core primes 7 and 13, the primes 43 and 29 attached to 7 and 23 attached to 11, period 924 | main and u3e | the same 25 vertex values | `logs/u3f_test_t1_b28f911b.log`, `logs/u3e_test_t1_ffb5efd1.log` |
| `test_cert_t2_u3f_43e56246.json`, `test_cert_t2_u3e_b1fdae48.json` | the same with the prime 127, of order 7, also attached to 7 | main, u3e and `test_ref_u3e_batched_518e70a9.py` | the u3e checker stops at its bound for the int64 group sums (exit code 1); the test copy, which is the u3e checker with only this step replaced by sums in Python integers, gives the same 25 vertex values as the main checker | `logs/u3e_test_t2_25abb650.log` (the paths in its traceback shortened), `logs/ref_test_t2_b9261f6e.log`, `logs/u3f_test_t2_9206768b.log` |
| `cert_u3x_41_ad7a2738.json`, `cert_u3a_c2728dff.json`, `cert_u3e_41_aac6e106.json` | the splitting of `l` (below) | v3; u3e for the last | the first two certify 0.109618905 (`--claim 0.109618`); all three give the same 17 vertex values | `logs/u3x_u3x41_3bab4a50.log`, `logs/u3x_u3a_c6c2b1f4.log`, `logs/u3e_u3e41_3a5dba29.log` |
| `cert_u3c_73_18aa78b6.json`, `cert_v4bb_73_73e5cf24.json` | the earlier certificates for 0.110118 and 0.118601 | v3 | 0.110118630 and 0.118601142 | `logs/u3x_u3c73_6c56e930.log`, `logs/u3x_v4bb73_7a2c56b2.log` |

The two tests with period 924 use class (a) only, without the file for class (b), and take a few minutes on one core.
Their certificates contain only parameters and are not produced by a program in `reproduce/`. The fields `note` of
`cert_u3d_u3x`, `cert_v4d_u3x` and `cert_u3d_perm` are copied unchanged from the certificates they come from.

The directory `controls/` holds four certificates derived from `cert_u3e_73_f4510070.json` and the output of the checker
on them. Each run ends with `FAIL` and exit code 1: `alpha_mass` puts 1.001 times the allowed mass on the point `alpha_j`,
`add_not_in_ell` lists an added prime that does not divide `l`, `orbits` states 7,871 instead of 7,870 orbits, and
`wrong_vertex` chooses the Pintz indices at the vertex `e_1` and claims 0.110173, while the smallest vertex value is then
0.11011862659.

The splitting of `l` into `l'` and the added primes is tested, for one added prime and without a change of period, on
the modulus `3*5*7*11*13*17*31*41*241` of the bound `d >= 0.109406`, with period 120: `cert_u3x_41_ad7a2738.json` splits
off the prime 41, `cert_u3a_c2728dff.json` (format `r45a-u3`) runs through the 92,206 rotation orbits of the full
patterns, as the first checker does, and `cert_u3e_41_aac6e106.json` is `cert_u3x_41_ad7a2738.json` in the format
`r45a-u3e`. The table of tests above gives the results.

## Formal proofs in Lean

Each of the directories `lean/`, `lean_kernel/`, `lean_u3e/`, `lean_u3g/` and `lean_u3g_kernel/` holds one proof, with a
`README.md` that describes its files and gives the build commands.

The directory `lean/` contains a proof of the bounds `d >= 0.109406` and, under the bound (2.2), `d >= 0.117953` in Lean
4 (version v4.35.0-rc3) with Mathlib (commit c55e6e786f49): the theorems `Romanoff.romanoff_U2` and
`Romanoff.romanoff_v3` in `lean/Romanoff/Theorems.lean`. They are weaker than Theorems 1.1 and 1.2. The analytic inputs
of Section 2 are the hypotheses of these theorems: the per-class bound (2.1) for the modulus
`l = 3*5*7*11*13*17*31*41*241`, the prime number theorem in progressions modulo `l` and the bound (2.3) for `R0`, stated
for its finite partial sums, and for the second bound also the bound (2.2) for the total. Pintz's inequality (Lemma 2.1)
is proved. The checks of the data run as compiled code through `native_decide`, so `#print axioms` lists the three
standard axioms and four auxiliary axioms for each theorem (`lean/results/axioms_shipped.txt`).

The directory `lean_kernel/` contains a second proof, a separate Lake project in which no module uses `native_decide`:
the theorems `Romanoff.romanoff_U2_K` and `Romanoff.romanoff_v3_K` in `lean_kernel/Romanoff/CertKFinal.lean` have the
same statements and hypotheses, and each depends only on the three standard axioms
(`lean_kernel/results/axioms_shipped.txt`). The computations are split into theorems that the kernel checks by
evaluation: 244 for the list of primes, the lower sums for `R0` and the bounds `T+(c)`, and 185 for the Lagrangian
bound, with the 92,206 rotation orbits computed by a fold whose steps the kernel checks. `lean_kernel/README.md` also
gives the regeneration commands; the build took 1 h 35 min, not counting Mathlib, on one machine with 32 threads and 128
GB of memory.

The directory `lean_u3e/` contains a proof of the bound `d >= 0.110449` for `l_1`, a separate Lake project with the same
Lean and Mathlib versions: the theorem `Romanoff.E.romanoff_U3e` in `lean_u3e/Romanoff/E/U3e.lean` states
`0.110449 <= liminf d_N`, where `d_N` is the proportion of the integers `1 <= n <= N` of the form `p + 2^a`. Its
hypotheses are the per-class bound (2.1) and the prime number theorem in progressions for the modulus `l_1`, and the
bound (2.3) for `R0`, stated as for the other proofs. Six computations run as compiled code through `native_decide`:
five checks of the data and of the bounds for the singular series, and the evaluation of the bound by a program written
in Lean, which follows the u3e checker. So `#print axioms` lists the three standard axioms and six auxiliary axioms
(`lean_u3e/results/axioms_shipped.txt`). The exported proof was accepted by `leanchecker`, which runs Lean's kernel, and
by two further implementations of the Lean kernel, nanoda and lean4lean, with the six auxiliary axioms admitted. The
program obtains the value 0.1104501353..., a little above the checker's smallest value, because its bounds for the
singular series spread the contribution of the branches that the dynamic program stops over the divisors of the period,
as `lean_u3e/README.md` explains. The evaluation takes about 50 minutes on 90 cores.

The directory `lean_u3g/`, another separate Lake project with the same versions, contains the proofs of Theorems 1.1 and
1.2: the theorems `Romanoff.G.romanoff_U3g` in `lean_u3g/Romanoff/G/U3g.lean` and `Romanoff.G.romanoff_V4g` in
`lean_u3g/Romanoff/G/V4g.lean` state `0.110825 <= liminf d_N` and `0.119178 <= liminf d_N`. The hypotheses are those of
`lean_u3e/` with `l_3` in place of `l_1`, and for Theorem 1.2 also the bound (2.2). Of the six computations that run
through `native_decide`, five check the period-27720 tables and one evaluates both bounds at the vertex `e_27720`, where
they are smallest, with a program written in Lean; `#print axioms` lists the three standard axioms and these six
auxiliary axioms (`lean_u3g/results/axioms_shipped.txt`). The program obtains the values 0.1108276292... and
0.1191809294..., a little above the main checker's smallest values for the same reason as in `lean_u3e/`; with the
claims raised to 0.110828 and 0.119181 the evaluation fails. It runs in 64 parallel tasks and took about 46 minutes. The
exported proof was accepted by `leanchecker` and by lean4lean, with the six auxiliary axioms admitted, and both rejected
a copy in which the proof of Theorem 1.2 is replaced by that of Theorem 1.1; nanoda stopped at an internal capacity
limit on this export. The Lean kernel also replayed, one module at a time and again with the six auxiliary axioms
admitted, 81 of the 82 modules of the project that make up the proof; the remaining one, which contains only
definitions, was not part of that run. Built from scratch, with the evaluation run again, the files of this directory
reproduced the declarations and axioms of the build on which these checks were made, and its compiled modules for the
evaluation and for the two theorems (`Native.olean`, `U3g.olean`, `V4g.olean`) byte for byte.

The directory `lean_u3g_kernel/` contains a second proof of Theorems 1.1 and 1.2, a separate Lake project with the same
versions in which no module uses `native_decide`: the theorems `Romanoff.G.romanoff_U3g_K` and
`Romanoff.G.romanoff_V4g_K` in `lean_u3g_kernel/GK/FinalK.lean` have the same statements and hypotheses as those of
`lean_u3g/`, and each depends only on the three standard axioms (`lean_u3g_kernel/results/axioms_shipped.txt`). The
kernel checks the data and the bounds for the sums `T(c)` in 327 parts and computes the list of the rotation orbits of
the patterns modulo `l'`, 7,870 orbits and the empty pattern, with the number of classes in each. Its program for the
two bounds treats the core primes 19, 73 and 37 as attached to the digit `floor((r mod 9) / 3)`, so that their 7,030
combinations of exclusions enter only through 412 tables; a Lean proof shows that it gives the value of the program of
`lean_u3g/` for every subset of `Z/120` in place of a pattern. The kernel evaluates it for each of these 7,871 patterns
in a separate module (`lean_u3g_kernel/GK/Keys/`), adds the results in 64 further modules and checks both bounds on the
total; the values are those of `lean_u3g/`. Most of the files of the directory are generated, by generators that it
contains. The 7,871 modules of the patterns took from 877 to 1,255 seconds each to build, 2,494 CPU-hours in total
(`lean_u3g_kernel/results/FLEET_BUILD_LOG.tsv`). The Lean kernel replayed all 8,557 modules of the project that make up
the proof, one at a time (359,992 constants), compiled from the sources described under Provenance in
`lean_u3g_kernel/README.md`. The stored statements of the two theorems equal those of `lean_u3g/`. A rebuild from source
gave the same declarations in every module it rebuilt, and byte-identical compiled files for 150 pattern modules chosen
at random, 4 of the 64 summing modules and the final modules; `leanchecker`, lean4lean and nanoda accepted the exported
proofs of the first two of these 150 pattern modules. The build fails when the bound of Theorem 1.1 is raised to
0.110828 or when one entry in the module of a pattern is changed.

## Reproduction

The programs in `reproduce/` produced the data and the certificates. Their names, like those of the data files, end with
the first eight hex digits of the file's SHA-256. To run them, copy them to names without this suffix
(`dual_opt.py` imports `patterns_fast`). They need python-flint, numpy and highspy.
- `fetch_fdb.sh` and `fdb_to_phi.py` fetch the factorizations of `2^t - 1` from factordb and convert them to
  factorizations of `Phi_t(2)`; `factor_full.py` factors `Phi_t(2)` for `t <= 300` with FLINT; `verify_factors.py`
  checks the files.
- `patterns_fast.py` computes the residue patterns and their orbits, and `dual_opt.py` computes the multipliers from
  the parameter file `params_p120b_e724da74.json` and the singular-series bounds `tails_p120b_v5_c073e0de.json` (which
  the checker recomputes).
- `cert_build3.py` solves the linear program in floating point with HiGHS, as a cross-check of the multipliers.
- `sensitivity.py` evaluates the Lagrangian bound in floating point, with one common multiplier, for other values of
  the two constants; `sens_p120b_a87b7f38.log` is its output for the modulus `3*5*7*11*13*17*31*41*241`. These values
  are not certified, and the checker refuses most of these constants.
- From the certificate of the bound `d >= 0.109406`, `make_u3_certs.py` writes the earlier certificate `cert_u3c_73`,
  the certificate with the added primes 41 and 19, and the two certificates of the splitting test:
  `python3 -I make_u3_certs.py ../check/cert_p120b_uncond_af1c16be.json OUTDIR`.
  These certificates contain only parameters: the checkers recompute the number of orbits and require it to match, and
  the point `alpha_j` affects only how good the bound is.
- `make_u3de_certs.py` writes the certificate `cert_u3e_23_37` of the bound 0.110449, `cert_v4d_37e`, `cert_u3d_37e`,
  `cert_u3e_73` and the four certificates in `controls/` into the output directory of `make_u3_certs.py`:
  `python3 -I make_u3de_certs.py OUTDIR`. For `cert_v4d_37e` the only new data are the total constant 6.7814 and the
  multiplier `mu = t nu` (with `nu` as in Section 4), rounded to `10^-12`, with the value `t = 3.676e-3`
  chosen for version 3. `cert_u3d_perm` is `cert_u3d_37e` with the order of the added primes changed, and `cert_u3d_u3x`
  and `cert_v4d_u3x` are `cert_u3d_37e` and `cert_v4d_37e` with the field `format` changed to `r45a-u3x`; no program
  here writes these three files.
- `make_v4e_cert.py` writes the certificate `cert_v4e_23_37` of the bound 0.118859 from `cert_u3e_23_37` in `OUTDIR`
  (the output directory of `make_u3de_certs.py`), by the same rule: `python3 -I make_v4e_cert.py OUTDIR`.
- `make_u3f_certs.py` writes the certificate of Theorem 1.1, `cert_u3g_27720`, and `cert_u3f_repro` from
  `cert_u3e_23_37` in `OUTDIR`: `python3 -I make_u3f_certs.py OUTDIR`. The new data are the primes 43 and 29, the field
  `IND = [7, 11]`, the period 27720 and `alpha_j = {27720: 1}`.
- `make_v4g_cert.py` writes the certificate of Theorem 1.2, `cert_v4g_27720`, from `cert_u3g_27720` in `OUTDIR`, by the
  rule of `make_v4e_cert.py` (`mu = t nu` rounded to `10^-12` with `t = 3.676e-3`):
  `python3 -I make_v4g_cert.py OUTDIR`.
- `make_u3e_tests.py` writes the test certificates `cert_u3e_41`, `cert_u3e_41_23` and `cert_u3e_23_41` from
  `cert_u3x_41`: `python3 -I make_u3e_tests.py ../check/cert_u3x_41_ad7a2738.json OUTDIR`.
- `make_v4_certs.py` writes the earlier certificate `cert_v4bb_73` from `cert_u3c_73`:
  `python3 -I make_v4_certs.py DIR`, with `DIR` the output directory of `make_u3_certs.py`.
  It also writes three other conditional certificates, which are not used here. The only new data are the total
  constant 6.7814 and the multiplier `mu = t nu`, rounded to `10^-10`, with `t = 3.676e-3`; of the three values of `t`
  that were tried with the checker, this one gave the largest bound.
- `scan45e.py` is the floating-point model of the bound of Proposition 4.3 with which `t` was chosen. It divides by
  the number of classes with nonempty patterns instead of `l`, so its printed bounds are about `1e-6` too high, but
  the best `t` is the same. Its run for the added primes 41 and 19, and 41, 19 and 73, is `logs/scan45e_e2929b18.log`;
  for 41, 19 and 73 it gives 0.118602159 at `t = 3.676e-3`.
- `scan45b.py`, `scan45c.py` and `scan45d.py` are floating-point models of the bound with which the added primes and the
  point `alpha_j` were chosen; the runs that chose the added primes 23 and 37, each of which adds one candidate prime
  `q` to 41 (the modulus `l'*41*q`), are not included. They take class (b) from the factorization file without primality
  proofs, so they certify nothing. `scan45b.py` evaluates the bound with the tail bound `gcd(c, P) theta` of Section 5
  for candidate added primes, `scan45c.py` searches the simplex of Proposition 4.2 for its worst point, and `scan45d.py`
  evaluates the bound of Proposition 4.2 for candidate added primes. The command
  `python3 -I scan45d.py ../check/fac300_41e4cdd6.json ../check/fac1200_fdb_af082adc.json 3,5,7,11,13,17,31,241 41,19 73`
  prints 0.109943846 for the added primes 41 and 19 and 0.110118630 for 41, 19 and 73; its output is
  `logs/scan45d_ba953f7e.log` (10 minutes on one core, 20 GB of memory). The usage lines of all four scan programs say
  `scan45b.py`, and the docstring of `scan45e.py` still describes the unconditional bound.

## Notes

- The `note` fields inside the certificates of the bounds `d >= 0.117953` and `d >= 0.109406` were written for the
  earlier checker `check_r45a5_rel_ab861be2.py` and name the certificates without the hash suffix. The checker here
  supersedes that one: it adds the input checks listed above and certifies the same values.
- The notes call the inputs (I1) to (I5): (I1) is the per-class bound (2.1), (I2) the total bound (2.2),
  (I3) the prime number theorem in progressions, (I4) Lemma 2.1 and (I5) the bound (2.3) for `R0`.
- The docstrings and the `note` fields of the files use these names:
  - `U2`: the bound `d >= 0.109406`;
  - `U3a`: the same modulus with the tail of Proposition 4.2 (0.109618905);
  - `BASE` and `ADD`: the factor `l'` and the added primes;
  - `U3b` and `U3c`, in the `note` fields: the certificates with the added primes 41 and 19, and 41, 19 and 73 (the
    docstrings of `make_u3_certs.py` and `make_u3de_certs.py` use `U3b` for the stage of version 3 that includes both);
  - `V4bb`: the certificate `cert_v4bb_73`;
  - `U3e` and `V4e`: the certificates of the bounds 0.110449 and 0.118859 (`V4e` is the conditional form of `U3e`);
  - `U3g` and `V4g`: the certificates of Theorems 1.1 and 1.2;
  - `V4d`: `cert_v4d_37e`, the conditional form of `U3d`, the certificate `cert_u3d_37e`;
  - "divisor form": the grouping of the bounds by divisors of the period;
  - "independent": the attached primes and their primes `q`.
- The certificates of version 3 were first checked with an earlier revision of the v3 checker (SHA-256
  `b90c40dd77e6824d…`). It required `PER <= 4096` for its int64 arithmetic, which is too weak in general (it needs
  `PER < 1448`) but holds for `PER = 360`. The shipped revision requires `PER^2 max(Tg) < 2^63` for the grid integers
  `Tg = ceil(T 2^40)` instead, bounds the weighted row sums of every orbit, and sums the row weights as a Python integer.
  These are its only changes, and both revisions certify the same values.
- The parameter notes attribute `R0 < 1.93656` to Khalfalah and Pintz. The bound follows from Pintz's
  `C0 R0 < 1.2784421041` (Acta Math. Hungar. 112 (2006), Lemma 2'') and `C0 > 0.6601618158`, as quoted by Platt and
  Trudgian (J. Number Theory 153 (2015), p. 55).

## Versions

- Version 10 adds the proofs of Theorems 1.1 and 1.2 in Lean 4 that the kernel checks alone, in `lean_u3g_kernel/`.
  Apart from this README, `CITATION.cff` and `SHA256SUMS`, the files of version 9 are unchanged.
- Version 9 (doi:10.5281/zenodo.23588537) added the proofs of Theorems 1.1 and 1.2 in Lean 4, with compiled checks, in
  `lean_u3g/`.
- Version 8 (doi:10.5281/zenodo.23583779) raised Theorem 1.2 from 0.118859 to 0.119178. It used the modulus `l_3` of
  Theorem 1.1 and added the certificate, the logs of its checking runs and the program that wrote the certificate.
- Version 7 (doi:10.5281/zenodo.23580773) raised Theorem 1.1 from 0.110449 to 0.110825. It used the modulus
  `l_3 = 29*43*l_1` (period 27720), where `l_1` is the modulus of Theorem 1.1 in version 6, and added a checker that
  splits off the primes 7 and 11 of the period (`check/check_r45u3f_a028b118.py`), the certificate, the logs of the
  checking runs and of the tests of the checker, and the program that wrote the certificate.
- Version 6 (doi:10.5281/zenodo.23574563) added the proof in Lean 4 of the bound 0.110449, then Theorem 1.1, in
  `lean_u3e/`.
- Version 5 (doi:10.5281/zenodo.23565417) raised the bound of Theorem 1.2 from 0.118747 to 0.118859, with its
  certificate, the logs of two checking runs, one at the claimed bound and one just above it, and the program that wrote
  the certificate.
- Version 4 (doi:10.5281/zenodo.23557899) raised Theorem 1.1 from 0.110118 to 0.110449 and Theorem 1.2 from 0.118601 to
  0.118747, with the checking program that groups the bounds for the singular series by divisors of the period.
- Version 3 (doi:10.5281/zenodo.23552296) added the checking program of the bounds 0.110118 and 0.118601 and the Lean
  proof in `lean_kernel/`.
- Version 2 (doi:10.5281/zenodo.23548710) added the Lean proof in `lean/`.

## License

Apache License 2.0, see `LICENSE`.
