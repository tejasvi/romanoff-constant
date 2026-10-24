import Romanoff.E.S2.Mino
import Romanoff.E.Reduce

/-!
# U3e stage 2: the evaluator against the Lagrangian bound

* `T1_le`: the nested option sums of the row minorants are at most the tuple sums of `phiCls` over the options of the
  added primes (`optsP 3960 37` = the classes `j mod 36` and the empty class, `opts37_eq`);
* `V_evalPar`: the parallel evaluation is `Σ_{(x, c)} c · V (evalKey x)`;
* `lagBound_ge_V`: `V (evalPar k (foldOrbits 3960 baseP)) ≤ lagBound (parOf (teffA (tabB BLit) α) 8 0) (orbits 3960 ellPrimes)`
  for every `α ≥ 0` with `Σ_g α_g ≤ R0t + δ` (BASE fold, `wsum_foldl` over the added primes, `orbSum_orbits`, `μ = 0`).
-/

open Finset R45 R45.EV R45.U3E

namespace Romanoff.E.S2

/-- The options of 37: the classes `j mod 36` (one residue each) and the empty class (residue 0). -/
theorem opts37_eq : optsP 3960 37 = (o37.map fun j => (cmask36 j, 1)) ++ [(0, 1)] := by decide +kernel

section
variable (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3E.divE.map α).sum ≤ M3E.R0tLit + delta)
include hα hαs

theorem mv_le (X : ℕ) : mv X ≤ phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960 X :=
  mino α hα hαs X _ (jIdx_pos _ _)

theorem R4_le (X : ℕ) : R4 X ≤ tupleSum 3960 [37] X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) := by
  have h : tupleSum 3960 [37] X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) =
      (o37.map fun j => phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960 (X ||| cmask36 j)).sum +
        phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960 X := by
    have h0 : tupleSum 3960 [37] X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) =
        wsum (optsP 3960 37) (fun m => phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960 (X ||| m)) := by
      rw [wsum_optsP]; rfl
    rw [h0, opts37_eq, wsum_append, wsum_cons, wsum_nil, add_zero, Nat.or_zero]
    unfold wsum
    rw [List.map_map]
    simp only [Function.comp_def, Nat.cast_one, one_mul]
  refine le_of_le_of_eq ?_ h.symm
  unfold R4
  rw [add_comm (mv X)]
  exact add_le_add (List.sum_le_sum fun j _ => mv_le α hα hαs _) (mv_le α hα hαs X)

omit hα hαs in
/-- One level of option sums against `tupleSum`. -/
theorem lvlT (p : ℕ) (ps : List ℕ) (Tin : ℕ → ℚ)
    (hTin : ∀ X, Tin X ≤ tupleSum 3960 ps X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960)) (X : ℕ) :
    ((optsP 3960 p).map fun mc => (mc.2 : ℚ) * Tin (X ||| mc.1)).sum ≤
      tupleSum 3960 (p :: ps) X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) := by
  have h : tupleSum 3960 (p :: ps) X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) =
      wsum (optsP 3960 p) (fun m => tupleSum 3960 ps (X ||| m) (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960)) := by
    rw [wsum_optsP]; rfl
  refine le_of_le_of_eq ?_ h.symm
  unfold wsum
  exact List.sum_le_sum fun mc _ => mul_le_mul_of_nonneg_left (hTin _) (Nat.cast_nonneg _)

theorem T1_le (x : ℕ) :
    T1 x ≤ tupleSum 3960 [41, 19, 73, 23, 37] x (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) := by
  have h4 : ∀ X, T4 X ≤ tupleSum 3960 [23, 37] X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) :=
    fun X => lvlT α 23 [37] R4 (R4_le α hα hαs) X
  have h3 : ∀ X, T3 X ≤ tupleSum 3960 [73, 23, 37] X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) :=
    fun X => lvlT α 73 [23, 37] T4 h4 X
  have h2 : ∀ X, T2 X ≤ tupleSum 3960 [19, 73, 23, 37] X (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960) :=
    fun X => lvlT α 19 [73, 23, 37] T3 h3 X
  exact lvlT α 41 [19, 73, 23, 37] T2 h2 x

end

/-! ## The parallel evaluation -/

theorem V_axpy (c : ℕ) (v acc : Array ℕ) (hv : v.size = 128) (ha : acc.size = 128) :
    (axpy c v acc).size = 128 ∧ V (axpy c v acc) = V acc + (c : ℚ) * V v := by
  have hs : (axpy c v acc).size = 128 := by simp [axpy, hv, ha]
  refine ⟨hs, ?_⟩
  rw [V_eq, V_eq, V_eq, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro J hJ
  have hJ' := mem_range.mp hJ
  rw [axpy_getD c v acc (by rw [hv, ha]) _ (by rw [ha]; omega),
    axpy_getD c v acc (by rw [hv, ha]) _ (by rw [ha]; omega), vt_add]

theorem V_evalList (L : List (ℕ × ℕ)) :
    (evalList L).size = 128 ∧ V (evalList L) = (L.map fun xc => (xc.2 : ℚ) * V (evalKey xc.1)).sum := by
  let F : Array ℕ → ℕ × ℕ → Array ℕ := fun acc xc => axpy xc.2 (evalKey xc.1) acc
  let v : ℕ × ℕ → ℚ := fun xc => (xc.2 : ℚ) * V (evalKey xc.1)
  have hF : ∀ (acc : Array ℕ) (xc : ℕ × ℕ), xc ∈ L → acc.size = 128 →
      (F acc xc).size = 128 ∧ V (F acc xc) = V acc + v xc :=
    fun acc xc _ hacc => V_axpy xc.2 (evalKey xc.1) acc (V_evalKey xc.1).1 hacc
  have h := V_foldl F v L hF z128 z128_size
  rw [V_z128, zero_add] at h
  exact h

theorem chunks_flatten {β : Type} (k : ℕ) (L : List β) : (chunks k L).flatten = L := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    rw [chunks]
    split_ifs with hc
    · simp
    · simp only [not_or] at hc
      rw [List.flatten_cons, ih (L.drop k).length (by
        have : L.length ≠ 0 := fun h0 => hc.2 (List.eq_nil_of_length_eq_zero h0)
        simp only [List.length_drop]; omega) _ rfl, List.take_append_drop]

theorem sum_flatten_map {β : Type} (f : β → ℚ) : ∀ (LL : List (List β)),
    (LL.map fun l => (l.map f).sum).sum = (LL.flatten.map f).sum
  | [] => by simp
  | l :: LL => by rw [List.map_cons, List.sum_cons, sum_flatten_map f LL, List.flatten_cons, List.map_append,
      List.sum_append]

theorem V_evalPar (k : ℕ) (L : List (ℕ × ℕ)) :
    V (evalPar k L) = (L.map fun xc => (xc.2 : ℚ) * V (evalKey xc.1)).sum := by
  let F : Array ℕ → List (ℕ × ℕ) → Array ℕ := fun acc ch => axpy 1 (evalList ch) acc
  let v : List (ℕ × ℕ) → ℚ := fun ch => (1 : ℚ) * V (evalList ch)
  have hF : ∀ (acc : Array ℕ) (ch : List (ℕ × ℕ)), ch ∈ chunks k L → acc.size = 128 →
      (F acc ch).size = 128 ∧ V (F acc ch) = V acc + v ch := by
    intro acc ch _ hacc
    have := V_axpy 1 (evalList ch) acc (V_evalList ch).1 hacc
    exact ⟨this.1, by rw [this.2]; simp [v]⟩
  have h := V_foldl F v (chunks k L) hF z128 z128_size
  have e : evalPar k L = List.foldl F z128 (chunks k L) := by
    unfold evalPar
    rw [List.foldl_map]
    rfl
  rw [e, h.2, V_z128, zero_add]
  simp only [v, one_mul]
  have e2 : ∀ ch ∈ chunks k L, V (evalList ch) = (ch.map fun xc => (xc.2 : ℚ) * V (evalKey xc.1)).sum :=
    fun ch _ => (V_evalList ch).2
  rw [List.map_congr_left e2, sum_flatten_map, chunks_flatten]

/-! ## Against the Lagrangian bound -/

theorem foldOrbits_keys (per : ℕ) : ∀ (ps : List ℕ) (L : List (ℕ × ℕ)), (∀ xc ∈ L, xc.1 < 2 ^ per) →
    ∀ xc ∈ ps.foldl (fun L p => foldStep per L (optsP per p)) L, xc.1 < 2 ^ per
  | [], L, hL => hL
  | p :: ps, L, hL => foldOrbits_keys per ps _ (foldStep_keys per L _ hL (optsP_lt per p))

theorem goodAdd : GoodPrimes 3960 [41, 19, 73, 23, 37] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨by norm_num, by norm_num, by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem lagBound_ge_V (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3E.divE.map α).sum ≤ M3E.R0tLit + delta)
    (k : ℕ) : V (evalPar k (foldOrbits 3960 baseP)) ≤
      lagBound (PE.parOf (teffA (tabB BLit) α) 8 0) (orbits 3960 ellPrimes) := by
  have hlen : (PE.parOf (teffA (tabB BLit) α) 8 0).teff.length = (PE.parOf (teffA (tabB BLit) α) 8 0).per :=
    teffA_length _ _
  have hfold : foldOrbits 3960 ellPrimes =
      [41, 19, 73, 23, 37].foldl (fun L p => foldStep 3960 L (optsP 3960 p)) (foldOrbits 3960 baseP) := by
    show (baseP ++ [41, 19, 73, 23, 37]).foldl (fun L p => foldStep 3960 L (optsP 3960 p)) [(0, 1)] = _
    rw [List.foldl_append]
    rfl
  have hkeys : ∀ xc ∈ foldOrbits 3960 baseP, xc.1 < 2 ^ 3960 :=
    foldOrbits_keys 3960 baseP [(0, 1)] (fun xc hxc => by rw [List.mem_singleton.mp hxc]; exact Nat.two_pow_pos _)
  have e1 : lagBound (PE.parOf (teffA (tabB BLit) α) 8 0) (orbits 3960 ellPrimes) =
      wsum (foldOrbits 3960 baseP)
        (fun x => tupleSum 3960 [41, 19, 73, 23, 37] x (phiCls (PE.parOf (teffA (tabB BLit) α) 8 0) 3960)) := by
    have hmu : (PE.parOf (teffA (tabB BLit) α) 8 0).mu = 0 := rfl
    rw [lagBoundSplit _ _ hlen, hmu, zero_mul, zero_mul, zero_mul, sub_zero, orbSum_orbits, hfold,
      wsum_foldl (by norm_num) (fun x hx => phiCls_rot (by norm_num) _ hx) _ goodAdd (foldOrbits 3960 baseP) hkeys]
  refine le_of_eq_of_le (V_evalPar k _) (le_of_le_of_eq ?_ e1.symm)
  unfold wsum
  apply List.sum_le_sum
  intro xc _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  refine le_of_eq_of_le (V_evalKey xc.1).2 ?_
  exact T1_le α hα hαs xc.1

end Romanoff.E.S2
