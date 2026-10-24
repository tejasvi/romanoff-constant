import Romanoff.M4Spec

/-!
# M4 layer (C): the evaluator against the classes, and the data

Proofs of the four frozen statements of layer (C) in `Romanoff.M4Spec`:
* `orbSumLink : OrbSumLink`, the orbit sum is the sum of the per-class minima over the classes with `U_k ≠ ∅`
  (`orbSum_eq_sum_classes`, `phiCls_exmaskL`);
* `ncQLink : NcQLink`, `N(c) = (1/l) Σ_{k < l} n_k(c)` (the fold computes the sum over all classes of the rotation
  invariant `x ↦ n_{full ^^^ x}(c)`, as for `orbSum`);
* `lagBoundSplit : LagBoundSplit`, `lagBound = orbit sum - μ C1 κ Σ_c N(c) teff(c)`;
* `dataFacts : DataFacts`, the evaluator's constants against the statement's (`φ(l)` from `Nat.totient_mul` and
  `Nat.totient_prime`, never by unfolding `Nat.totient`).

`l = ell = 78187414305`: the sums over `range ell` are only rewritten by sum lemmas, never evaluated.
-/

open Finset R45

namespace Romanoff

namespace M4C

/-! ## `N(c)` through the fold -/

/-- `n(c)` of the complement `full ^^^ x` of an exclusion mask `x`. -/
def nCls (per c x : ℕ) : ℚ := (((nShift per (full per ^^^ x)).getD c 0 : ℕ) : ℚ)

theorem nCls_rot {per : ℕ} (hper : 0 < per) (c : ℕ) {x : ℕ} (hx : x < 2 ^ per) :
    nCls per c (rot1 per x) = nCls per c x := by
  unfold nCls
  rw [full_xor_rot1 hper hx, nShift_rot1 hper (full_xor_lt per x hx)]

theorem nCls_exmaskL (per : ℕ) (ps : List ℕ) (k c : ℕ) (hc : c < per) :
    nCls per c (exmaskL per ps 0 k) = (nC per ps k c : ℚ) := by
  unfold nCls
  rw [← umask, nShift_umask per ps k c hc]

/-- `N(c)` of the evaluator's orbits as a weighted sum over the fold (the orbits with `U = ∅` have `n = 0`). -/
theorem ncQ_orbits (P : Par) (per : ℕ) (ps : List ℕ) (c : ℕ) (hc : c < per) :
    ncQ P (orbits per ps) c = (1 / (P.ell : ℚ)) * wsum (foldOrbits per ps) (nCls per c) := by
  unfold ncQ orbits wsum
  rw [foldl_add_eq_sum, zero_add]
  generalize foldOrbits per ps = L
  induction L with
  | nil => simp
  | cons xc L ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, mul_add, ← ih]
    by_cases h : full per ^^^ xc.1 = 0
    · have h0 : nCls per c xc.1 = 0 := by
        unfold nCls
        rw [h, nShift_getD per 0 c hc]
        simp
      rw [h0, mul_zero, mul_zero, zero_add]
      dsimp only
      rw [ite_eq_left h]
    · dsimp only
      rw [ite_eq_right h, List.map_cons, List.sum_cons]
      dsimp only
      unfold nCls
      ring

/-- `N(c) = (1/l) Σ_{k < ∏ ps} n_k(c)`. -/
theorem ncQ_eq_sum_classes {per : ℕ} (hper : 0 < per) (P : Par) (ps : List ℕ) (hg : GoodPrimes per ps)
    (hd : DistinctPrimes ps) (c : ℕ) (hc : c < per) :
    ncQ P (orbits per ps) c = (1 / (P.ell : ℚ)) * ∑ k ∈ range ps.prod, (nC per ps k c : ℚ) := by
  rw [ncQ_orbits P per ps c hc]
  congr 1
  have hsum : ∑ k ∈ range ps.prod, (nC per ps k c : ℚ) = ∑ k ∈ range ps.prod, nCls per c (exmaskL per ps 0 k) :=
    sum_congr rfl fun k _ => (nCls_exmaskL per ps k c hc).symm
  rw [hsum, sum_exmaskL per (nCls per c) ps hd 0]
  unfold foldOrbits
  rw [wsum_foldl hper (fun x hx => nCls_rot hper c hx) ps hg [(0, 1)]
    (fun xc hxc => by rw [List.mem_singleton.mp hxc]; exact Nat.two_pow_pos per)]
  rw [wsum_cons, wsum_nil]
  push_cast
  ring

/-! ## The second fold of `lagBound` -/

theorem foldl_zip_range' (f : ℕ → ℚ) : ∀ (t : List ℚ) (s : ℕ) (a : ℚ),
    ((List.range' s t.length).zip t).foldl (fun acc ct => acc + f ct.1 * ct.2) a =
      a + ∑ c ∈ range t.length, f (s + c) * t.getD c 0
  | [], s, a => by simp
  | y :: t, s, a => by
    have e : ∀ c, s + 1 + c = s + (c + 1) := fun c => by omega
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons, foldl_zip_range' f t (s + 1),
      sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero, e]
    ring

/-- `Σ_{c < n} f(c) t(c)` for a list `t` of length `n`, as the evaluator computes it. -/
theorem foldl_zip_range (f : ℕ → ℚ) (t : List ℚ) (n : ℕ) (hn : t.length = n) :
    ((List.range n).zip t).foldl (fun acc ct => acc + f ct.1 * ct.2) 0 = ∑ c ∈ range n, f c * t.getD c 0 := by
  subst hn
  rw [List.range_eq_range', foldl_zip_range' f t 0 0, zero_add]
  simp only [zero_add]

/-! ## Euler's function of a product of distinct primes -/

theorem totient_prod : ∀ (ps : List ℕ), DistinctPrimes ps → Nat.totient ps.prod = (ps.map (· - 1)).prod
  | [], _ => by simp
  | p :: ps, ⟨hnd, hpr⟩ => by
    have hp := hpr p (by simp)
    have hnd' := List.nodup_cons.mp hnd
    have hps : DistinctPrimes ps := ⟨hnd'.2, fun q hq => hpr q (by simp [hq])⟩
    have hcop : Nat.Coprime p ps.prod :=
      coprime_prod hp ps fun q hq => ⟨hpr q (by simp [hq]), fun h => hnd'.1 (h ▸ hq)⟩
    rw [List.prod_cons, Nat.totient_mul hcop, Nat.totient_prime hp, totient_prod ps hps, List.map_cons,
      List.prod_cons]

end M4C

/-! ## The four statements of layer (C) -/

theorem orbSumLink : OrbSumLink := by
  intro P ht
  rw [orbSum_eq_sum_classes (by norm_num : 0 < 120) P ellPrimes goodPrimes_ell distinctPrimes_ell, Rat.cast_sum,
    sum_filter]
  refine sum_congr rfl fun k _ => ?_
  rw [phiCls_exmaskL P 120 ellPrimes k ht]
  by_cases h : Uset 120 ellPrimes k = ∅
  · have hn : ¬ (Uset 120 ellPrimes k).Nonempty := by
      rw [h]; exact Finset.not_nonempty_empty
    rw [ite_eq_left h, ite_eq_right hn, Rat.cast_zero]
  · rw [ite_eq_right h, ite_eq_left (Finset.nonempty_iff_ne_empty.mpr h)]

theorem ncQLink : NcQLink := fun P c hc =>
  M4C.ncQ_eq_sum_classes (by norm_num) P ellPrimes goodPrimes_ell distinctPrimes_ell c hc

theorem lagBoundSplit : LagBoundSplit := by
  intro P os ht
  have h := M4C.foldl_zip_range (ncQ P os) P.teff P.per ht
  unfold lagBound orbSum
  rw [h]

theorem dataFacts : DataFacts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rw [show ell = ellPrimes.prod from rfl, M4C.totient_prod ellPrimes distinctPrimes_ell]
    decide
  · have hpell : R45.P45.pell = (26542080000 : ℚ) / 6021132975 := by
      simp only [R45.P45.pell, R45.D45.ellPO, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      norm_num
    have hPl : Pl ellPrimes = (26542080000 : ℝ) / 6021132975 := by
      rw [Pl, List.prod_toFinset _ distinctPrimes_ell.1]
      simp only [ellPrimes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      norm_num
    rw [hpell, hPl]
    norm_num
  · norm_num [R45.D45.C0up, Romanoff.C0up]
  · norm_num [R45.D45.log2lo]
  · norm_num [R45.D45.log2hi]

end Romanoff
