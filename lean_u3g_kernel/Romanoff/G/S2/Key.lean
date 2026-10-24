import Romanoff.G.S2.Lift

/-!
# U3g/V4g stage 2: the evaluator against the Lagrangian bound

For parameters `(μ, C1, i*)` with `μ ≥ 0`, `C1 ≥ 0` and `i*(J)` bracketing `λ_J` for `1 ≤ J ≤ 63` (`Brk`), the slot function
`vt J a q = vtM μ C1 i*(J) J a q` satisfies, for every rational `α ≥ 0` with `Σ_{g ∈ divG} α_g ≤ R0t + δ`,
`Vf vt (evalPar k (foldOrbits 120 baseP)) ≤ lagBound (parOf (teffA (tabB BLit) α) C1 μ) (orbits 27720 ellPrimes)`
(`lagBound_ge_Vf`): `lagBound = Σ_classes phiClsB` (`lagBound_eq_wsumB`), the BASE fold at 120 lifted to 27720
(`tupleSum_lift`, `repB_rot`), the core options at 360 lifted to 27720, and per core row the weighted pattern sum of the
evaluator below the sum over the residue triples of `phiClsB` (`regroup`, `s_row`, `Q_row`, `mino`).
Instances: U3g (`μ = 0`, `i* = J`; `brkU`), V4g (`μ = muV`, `C1 = c1V`, `i* = istarV`; `brkV`).
-/

open Finset R45 R45.EVG R45.U3G

namespace Romanoff.G.S2

/-- The bracket conditions of `i*(J)` for `1 ≤ J ≤ 63`. -/
def Brk (mu : ℚ) (istar : ℕ → ℕ) : Prop :=
  ∀ J, 1 ≤ J → J ≤ 63 → 1 ≤ istar J ∧ PG.norm / ((istar J : ℚ) * ((istar J : ℚ) + 1)) ≤ lamJ mu J ∧
    (istar J = 1 ∨ lamJ mu J ≤ PG.norm / (((istar J : ℚ) - 1) * (istar J : ℚ)))

theorem brkU : Brk 0 (fun J => J) := by
  intro J hJ _
  refine ⟨hJ, le_max_right _ _, ?_⟩
  rcases Nat.lt_or_ge J 2 with h | h
  · left; show J = 1; omega
  · right
    have hJ2 : (2 : ℚ) ≤ J := by exact_mod_cast h
    have hn := normG_nonneg
    have h0 : 0 ≤ PG.norm / ((J : ℚ) * ((J : ℚ) + 1)) := div_nonneg hn (by positivity)
    unfold lamJ
    rw [max_eq_right h0]
    apply div_le_div_of_nonneg_left hn (by nlinarith)
    nlinarith

set_option maxRecDepth 100000 in
theorem brkV_dec : ∀ J < 64, 1 ≤ J → 1 ≤ istarV.getD J 1 ∧
    PG.norm / ((istarV.getD J 1 : ℚ) * ((istarV.getD J 1 : ℚ) + 1)) ≤ lamJ muV J ∧
      (istarV.getD J 1 = 1 ∨ lamJ muV J ≤ PG.norm / (((istarV.getD J 1 : ℚ) - 1) * (istarV.getD J 1 : ℚ))) := by
  decide +kernel

theorem brkV : Brk muV (fun J => istarV.getD J 1) := fun J hJ hJ63 => brkV_dec J (by omega) hJ

theorem rowX_lt (Y r23 r43 r29 : ℕ) : rowX Y r23 r43 r29 < 2 ^ 27720 :=
  Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (repB_lt _ _ _) (maskP_lt _ _ _)) (maskP_lt _ _ _))
    (maskP_lt _ _ _)

theorem regroup' (G : ℕ → ℚ) :
    ∑ r23 ∈ range 23, ∑ r43 ∈ range 43, ∑ r29 ∈ range 29, G (patOf r23 r43 r29) = ∑ P ∈ range npC, (pwt P : ℚ) * G P :=
  regroup G

theorem pwA_getD {P : ℕ} (hP : P < npC) : pwA.getD P 0 = pwt P := by
  rw [getD_eq_getElem' _ _ _ (by simp [pwA]; exact hP)]
  simp [pwA]

/-- The inner tuple sum of a core mask: the residues of 23, 43, 29 at period 27720. -/
def InnF (Φ : ℕ → ℚ) (Y : ℕ) : ℚ := tupleSum 27720 [23, 43, 29] (repB 360 27720 Y) Φ

theorem tupleSum_nil (per acc : ℕ) (G : ℕ → ℚ) : tupleSum per [] acc G = G acc := rfl

theorem InnF_eq (Φ : ℕ → ℚ) (Y : ℕ) : InnF Φ Y = tupleSum 27720 [23, 43, 29] (repB 360 27720 Y) Φ := rfl

theorem goodCore : ∀ q ∈ [41, 19, 73, 37], 1 < q ∧ 2 ^ 360 % q = 1 := by decide +kernel

theorem goodBase' : ∀ q ∈ baseP, 1 < q ∧ 2 ^ 120 % q = 1 := by decide +kernel

/-- The added primes at 27720 from the core options at 360. -/
theorem tuple_core (Φ : ℕ → ℚ) (x : ℕ) :
    tupleSum 27720 [41, 19, 73, 37, 23, 43, 29] (repB 120 27720 x) Φ = tupleSum 360 [41, 19, 73, 37] (repB 120 360 x) (InnF Φ) := by
  rw [show [41, 19, 73, 37, 23, 43, 29] = [41, 19, 73, 37] ++ [23, 43, 29] from rfl, tupleSum_append,
    ← repB_trans (show 120 ∣ 360 by norm_num) (by norm_num) x, tupleSum_lift (by norm_num) _ [41, 19, 73, 37] goodCore]
  rfl

section
variable (mu c1 : ℚ) (hmu : 0 ≤ mu) (hc1 : 0 ≤ c1) (istar : ℕ → ℕ) (hb : Brk mu istar) (α : ℕ → ℚ)
  (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3G.divG.map α).sum ≤ R45.M3G.R0tLit + delta)
include hmu hc1 hb hα hαs

/-- One core row: the evaluator's weighted pattern sum is at most the sum of `phiClsB` over the residue triples. -/
theorem Rrow_le (Y : ℕ) :
    Rrow (fun J a q => vtM mu c1 (istar J) J a q) Y ≤
      tupleSum 360 [] Y (InnF (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu))) := by
  rw [tupleSum_nil, InnF_eq]
  have e1 : tupleSum 27720 [23, 43, 29] (repB 360 27720 Y) (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu)) =
      ∑ r23 ∈ range 23, ∑ r43 ∈ range 43, ∑ r29 ∈ range 29,
        phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu) (rowX Y r23 r43 r29) := by
    simp only [tupleSum]; rfl
  rw [e1]
  unfold Rrow
  rw [range_map_sum]
  have e2 : ∀ P ∈ range npC,
      (pwA.getD P 0 : ℚ) * vtM mu c1 (istar (jIdx (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P)
        (qOf (zOf (tOf (csOf Y))) P))) (jIdx (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P)
        (qOf (zOf (tOf (csOf Y))) P)) (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P) (qOf (zOf (tOf (csOf Y))) P) =
      (pwt P : ℚ) * (fun P => vtM mu c1 (istar (jIdx (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P)
        (qOf (zOf (tOf (csOf Y))) P))) (jIdx (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P)
        (qOf (zOf (tOf (csOf Y))) P)) (sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) P)
        (qOf (zOf (tOf (csOf Y))) P)) P := by
    intro P hP
    rw [pwA_getD (mem_range.mp hP)]
  rw [sum_congr rfl e2, ← regroup']
  apply sum_le_sum; intro r23 h23; apply sum_le_sum; intro r43 h43; apply sum_le_sum; intro r29 h29
  have h23' := mem_range.mp h23
  have h43' := mem_range.mp h43
  have h29' := mem_range.mp h29
  beta_reduce
  rw [← s_row Y h23' h43' h29', ← Q_row Y h23' h43' h29']
  set J := jIdx (cntP 27720 (rowX Y r23 r43 r29) 1 0) (Qs (rowX Y r23 r43 r29))
  obtain ⟨hi, hb1, hb2⟩ := hb J (jIdx_pos _ _) (jIdx_le _ _)
  exact mino mu c1 hmu hc1 α hα hαs (rowX_lt Y r23 r43 r29) hi hb1 hb2

omit hmu hc1 hb hα hαs in
/-- One level of option sums against `tupleSum` at period 360. -/
theorem lvlT (Inn : ℕ → ℚ) (p : ℕ) (ps : List ℕ) (Tin : ℕ → ℚ) (hTin : ∀ X, Tin X ≤ tupleSum 360 ps X Inn) (X : ℕ) :
    ((optsP 360 p).map fun mc => (mc.2 : ℚ) * Tin (X ||| mc.1)).sum ≤ tupleSum 360 (p :: ps) X Inn := by
  have h : tupleSum 360 (p :: ps) X Inn = wsum (optsP 360 p) (fun m => tupleSum 360 ps (X ||| m) Inn) := by
    rw [wsum_optsP]; rfl
  refine le_of_le_of_eq ?_ h.symm
  unfold wsum
  exact List.sum_le_sum fun mc _ => mul_le_mul_of_nonneg_left (hTin _) (Nat.cast_nonneg _)

theorem T1_le (x : ℕ) :
    T1 (fun J a q => vtM mu c1 (istar J) J a q) (repB 120 360 x) ≤
      tupleSum 360 [41, 19, 73, 37] (repB 120 360 x) (InnF (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu))) := by
  have h4 : ∀ X, T4 (fun J a q => vtM mu c1 (istar J) J a q) X ≤
      tupleSum 360 [37] X (InnF (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu))) :=
    fun X => lvlT _ 37 [] _ (fun X' => Rrow_le mu c1 hmu hc1 istar hb α hα hαs X') X
  have h3 : ∀ X, T3 (fun J a q => vtM mu c1 (istar J) J a q) X ≤
      tupleSum 360 [73, 37] X (InnF (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu))) :=
    fun X => lvlT _ 73 [37] _ h4 X
  have h2 : ∀ X, T2 (fun J a q => vtM mu c1 (istar J) J a q) X ≤
      tupleSum 360 [19, 73, 37] X (InnF (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu))) :=
    fun X => lvlT _ 19 [73, 37] _ h3 X
  exact lvlT _ 41 [19, 73, 37] _ h2 _

end

/-! ## The BASE fold and the Lagrangian bound -/

theorem goodEll : GoodPrimes 27720 Romanoff.G.ellPrimes := by
  intro p hp
  simp only [Romanoff.G.ellPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num, by norm_num, by decide +kernel⟩

theorem goodAdd : GoodPrimes 27720 [41, 19, 73, 37, 23, 43, 29] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num, by decide +kernel⟩

theorem goodBase : GoodPrimes 120 baseP := by
  intro p hp
  simp only [baseP, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num, by decide +kernel⟩

theorem ellPrimes_split : Romanoff.G.ellPrimes = baseP ++ [41, 19, 73, 37, 23, 43, 29] := rfl

theorem lag_split (Φ : ℕ → ℚ) (hΦ : ∀ x, x < 2 ^ 27720 → Φ (rot1 27720 x) = Φ x) :
    wsum (foldOrbits 27720 Romanoff.G.ellPrimes) Φ =
      wsum (foldOrbits 120 baseP) (fun x => tupleSum 27720 [41, 19, 73, 37, 23, 43, 29] (repB 120 27720 x) Φ) := by
  have hK : ∀ x, x < 2 ^ 120 → (fun x => tupleSum 27720 [41, 19, 73, 37, 23, 43, 29] (repB 120 27720 x) Φ) (rot1 120 x) =
      (fun x => tupleSum 27720 [41, 19, 73, 37, 23, 43, 29] (repB 120 27720 x) Φ) x := by
    intro x hx
    show tupleSum 27720 _ (repB 120 27720 (rot1 120 x)) Φ = tupleSum 27720 _ (repB 120 27720 x) Φ
    rw [repB_rot hx]
    exact tupleSum_rot (by norm_num) hΦ _ goodAdd _ (repB_lt _ _ _)
  rw [wsum_tupleSum (by norm_num) hΦ _ goodEll, ellPrimes_split, tupleSum_append, ← repB_zero 120 27720,
    tupleSum_lift (by norm_num) _ baseP goodBase', wsum_tupleSum (by norm_num) hK _ goodBase]

theorem lagBound_ge_Vf (mu c1 : ℚ) (hmu : 0 ≤ mu) (hc1 : 0 ≤ c1) (istar : ℕ → ℕ) (hb : Brk mu istar)
    (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3G.divG.map α).sum ≤ R45.M3G.R0tLit + delta) (k : ℕ) :
    Vf (fun J a q => vtM mu c1 (istar J) J a q) (evalPar k (foldOrbits 120 baseP)) ≤
      lagBound (PG.parOf (teffA (tabB BLit) α) c1 mu) (orbits 27720 Romanoff.G.ellPrimes) := by
  have e1 : lagBound (PG.parOf (teffA (tabB BLit) α) c1 mu) (orbits 27720 Romanoff.G.ellPrimes) =
      wsum (foldOrbits 120 baseP) (fun x => tupleSum 27720 [41, 19, 73, 37, 23, 43, 29] (repB 120 27720 x)
        (phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu))) := by
    rw [lagBound_eq_wsumB (PG.parOf (teffA (tabB BLit) α) c1 mu) (pOf_per _ _ _)
      (by rw [pOf_teff]; exact teffA_length _ _) (by rw [pOf_cap]; norm_num)]
    exact lag_split _ fun x hx => phiClsB_rot _ hx
  rw [e1, Vf_evalPar (vtM_lin mu c1 istar)]
  unfold wsum
  apply List.sum_le_sum
  intro xc _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  beta_reduce
  rw [(Vf_evalKey (vtM_lin mu c1 istar) xc.1).2, tuple_core]
  exact T1_le mu c1 hmu hc1 istar hb α hα hαs xc.1

end Romanoff.G.S2
