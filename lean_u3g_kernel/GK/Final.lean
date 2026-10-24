import GK.GlueTotal
import GK.ChecksK
import K45G.Fold
import Romanoff.G.ReduceMu
import Romanoff.G.S2.Key
import Romanoff.G.Assembly
import Romanoff.G.Spec

/-!
# k45g: U3g and V4g with the stage-2 evaluation checked by the kernel

`values_K`: the two claims against the native evaluator's accumulator over `foldOrbits 120 baseP`, from the fibered kernel
evaluation (key modules GK/Keys, chunk glue GK/Glue, total GK/GlueTotal), the key theorem `key_eq` and K1's `foldBase_eq`.
`romanoff_U3g_of_S1`, `romanoff_V4g_of_S1`: the headlines from `values_K` and stage 1 given as a hypothesis `hS1`
(the type of the native `tboundALit`); K3's `Romanoff.G.K.tboundALitK` proves it kernel-only (GK/FinalK.lean).
The proofs follow `romanoff_U3g_of` / `romanoff_V4g_of` of Romanoff/G/S2/Final.lean; that module is not imported (its import
closure holds the native stage-1 checks), so `VU_eq8` is restated here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Filter Finset R45 R45.EVG R45.U3G R45.M3G Romanoff.G.S2

namespace R45.GK

theorem baseP_eq : baseP = [3, 5, 7, 11, 13, 17, 31, 241] := rfl

theorem Vf_evalPar_eq {vt : ℕ → ℕ → ℕ → ℚ} (hvt : Lin vt) :
    Vf vt (evalPar 123 (foldOrbits 120 baseP)) = VfA vt TOT := by
  rw [Vf_evalPar hvt, baseP_eq, K45G.foldBase_eq]
  have e : (K45G.LG.map fun xc => (xc.2 : ℚ) * Vf vt (evalKey xc.1)) =
      (K45G.LG.map fun xc => (xc.2 : ℚ) * VfA vt (evalKeyK xc.1)) := by
    apply List.map_congr_left
    intro xc _
    rw [key_eq hvt xc.1 o41OK_true patsOK_true fibOK_true sigOKall_true wtOK_true]
  rw [e, total_eq hvt]

theorem claimU_TOT : claimU ≤ ((List.range 64).map fun J => vtM 0 0 J J (TOT.get 6 J).1 (TOT.get 6 J).2).sum := by
  decide +kernel

theorem claimV_TOT : claimV ≤ ((List.range 64).map fun J =>
    vtM muV c1V (istarV.getD J 1) J (TOT.get 6 J).1 (TOT.get 6 J).2).sum := by
  decide +kernel

/-- With `μ = 0` the budget constant does not enter the minorant (as `Romanoff.G.VU_eq8`). -/
theorem VU_eq8 (acc : Array ℕ) : VU acc = Vf (fun J a q => vtM 0 8 J J a q) acc := by
  rw [VU_eq]
  unfold Vf vtM cpJ
  simp

theorem values_K : claimU ≤ VU (evalPar 123 (foldOrbits 120 baseP)) ∧ claimV ≤ VV (evalPar 123 (foldOrbits 120 baseP)) := by
  constructor
  · rw [VU_eq, Vf_evalPar_eq (vtM_lin 0 0 (fun J => J)), VfA_list]
    exact claimU_TOT
  · rw [VV_eq, Vf_evalPar_eq (vtM_lin muV c1V (fun J => istarV.getD J 1)), VfA_list]
    exact claimV_TOT

end R45.GK

namespace Romanoff.G

open R45.GK

/-- U3g from the kernel stage-2 evaluation and stage 1 as the hypothesis `hS1`. -/
theorem romanoff_U3g_of_S1 (hS1 : R0Bound → TBoundA (tabB BLit) R0tLit) (h1 : ESP28 G.ell) (h3 : PNTAP G.ell)
    (h5 : R0Bound) : G.U3gStatement := by
  have hv := values_K.1
  have h := liminf_ge_of_TBoundA (claim := claimU) (δ := delta) (hS1 h5) (by norm_num [delta])
    (fun α hα hαs => hv.trans (by
      rw [R45.GK.VU_eq8]
      exact S2.lagBound_ge_Vf 0 8 le_rfl (by norm_num) (fun J => J) S2.brkU α hα hαs 123)) h1 h3 h5
  have e : ((claimU : ℚ) : ℝ) = 110825 / 1000000 := by norm_num [claimU]
  unfold U3gStatement
  rw [← e]
  exact h

/-- V4g from the kernel stage-2 evaluation and stage 1 as the hypothesis `hS1`. -/
theorem romanoff_V4g_of_S1 (hS1 : R0Bound → TBoundA (tabB BLit) R0tLit) (h1 : ESP28 G.ell) (h2 : JTProp2)
    (h3 : PNTAP G.ell) (h5 : R0Bound) : G.V4gStatement := by
  have hv := values_K.2
  have h := liminf_ge_of_TBoundA_mu (claim := claimV) (δ := delta) (c1 := c1V) (mu := muV) (hS1 h5)
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
