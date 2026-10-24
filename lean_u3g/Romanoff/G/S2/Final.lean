import Romanoff.G.S2.Key
import Romanoff.G.ReduceMu
import Romanoff.G.Lit

/-!
# U3g/V4g: the headlines from the evaluation (the native fact as a hypothesis)

`romanoff_U3g_of`, `romanoff_V4g_of`: from `finalOK 123 = true` (Romanoff/G/S2/Native.lean), stage 1 (`tboundALit`) and
the reductions (`liminf_ge_of_TBoundA` with `μ = 0`; `liminf_ge_of_TBoundA_mu` with `μ = muV`, `C1 = c1V` and (I2)), the
two bounds `0.110825 ≤ liminf dens` and `0.119178 ≤ liminf dens`.
-/

open Filter R45 R45.EVG R45.U3G

namespace Romanoff.G

theorem values_of (h : finalOK 123 = true) :
    claimU ≤ VU (evalPar 123 (foldOrbits 120 baseP)) ∧ claimV ≤ VV (evalPar 123 (foldOrbits 120 baseP)) := by
  unfold finalOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- With `μ = 0` the budget constant does not enter the minorant. -/
theorem VU_eq8 (acc : Array ℕ) : VU acc = S2.Vf (fun J a q => vtM 0 8 J J a q) acc := by
  rw [S2.VU_eq]
  unfold S2.Vf vtM cpJ
  simp

theorem romanoff_U3g_of (hfin : finalOK 123 = true) (h1 : ESP28 G.ell) (h3 : PNTAP G.ell) (h5 : R0Bound) :
    G.U3gStatement := by
  have hv := (values_of hfin).1
  have h := liminf_ge_of_TBoundA (claim := claimU) (δ := delta) (tboundALit h5) (by norm_num [delta])
    (fun α hα hαs => hv.trans (by
      rw [VU_eq8]
      exact S2.lagBound_ge_Vf 0 8 le_rfl (by norm_num) (fun J => J) S2.brkU α hα hαs 123)) h1 h3 h5
  have e : ((claimU : ℚ) : ℝ) = 110825 / 1000000 := by norm_num [claimU]
  unfold U3gStatement
  rw [← e]
  exact h

theorem romanoff_V4g_of (hfin : finalOK 123 = true) (h1 : ESP28 G.ell) (h2 : JTProp2) (h3 : PNTAP G.ell)
    (h5 : R0Bound) : G.V4gStatement := by
  have hv := (values_of hfin).2
  have h := liminf_ge_of_TBoundA_mu (claim := claimV) (δ := delta) (c1 := c1V) (mu := muV) (tboundALit h5)
    (by norm_num [delta]) (by norm_num [muV])
    (fun α hα hαs => hv.trans (by
      rw [S2.VV_eq]
      exact S2.lagBound_ge_Vf muV c1V (by norm_num [muV]) (by norm_num [c1V]) (fun J => istarV.getD J 1) S2.brkV α hα
        hαs 123)) h1 h3 h5 (Or.inr ⟨h2, by norm_num [c1V, C1R]⟩)
  have e : ((claimV : ℚ) : ℝ) = 119178 / 1000000 := by norm_num [claimV]
  unfold V4gStatement
  rw [← e]
  exact h

end Romanoff.G
