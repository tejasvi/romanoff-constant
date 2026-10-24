import Romanoff.CertKGlue

/-!
# K track: the certificate values from chunk checks (generic in the chunk data)

Given the orbit list split into chunks `Ls` (`orbits 120 (ellPO.map (·.1)) = Ls.flatten`, from the kernel-checked fold)
and per-chunk bounds `B` verified chunkwise by `chunkOK` (kernel), the evaluator's bounds clear the claims once the
literal sums of `B` do.  Instantiated with the fold data in `Romanoff/CertKFinal.lean`.
-/

open Finset R45 R45.D45 R45.P45 R45.K45L

namespace Romanoff

theorem teffLit_length : R45.M3.teffLit.length = 120 := by decide

theorem teffLit_nonneg : ∀ c, (0 : ℚ) ≤ R45.M3.teffLit.getD c 0 := by
  intro c
  by_cases hc : c < 120
  · have h : (List.range 120).all (fun c => decide ((0 : ℚ) ≤ R45.M3.teffLit.getD c 0)) = true := by decide +kernel
    have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
    simpa using this
  · rw [List.getD_eq_default _ _ (by rw [teffLit_length]; omega)]

theorem dotNQ_teffLit_nonneg (n : List ℕ) (hn : n.length = 120) : 0 ≤ dotNQ n R45.M3.teffLit := by
  unfold dotNQ
  rw [dotNQ_eq n _ 0 (by rw [hn, teffLit_length]), zero_add]
  exact sum_nonneg fun c _ => mul_nonneg (Nat.cast_nonneg _) (teffLit_nonneg c)

theorem kap_nonneg : (0 : ℚ) ≤ kap := by
  unfold kap pell R45.D45.C0up R45.D45.log2lo per
  norm_num [R45.D45.ellPO]

/-- U2: the certificate value from chunk data. -/
theorem certK_U2_of (Ls : List (List Orb)) (B : List (ℚ × ℚ × ℚ))
    (hLs : orbits 120 (ellPO.map (·.1)) = Ls.flatten) (hlen : Ls.length = B.length)
    (hall : (Ls.zip B).all (fun p => chunkOK p.1 p.2.1 p.2.2.1 p.2.2.2) = true)
    (hnum : (109406 / 1000000 : ℚ) ≤ (B.map (·.1)).sum) :
    (109406 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit 8 0) (orbits 120 (ellPO.map (·.1))) := by
  have hent := fun o (ho : o ∈ orbits 120 (ellPO.map (·.1))) => orbits_entry ho
  rw [lagBound_orbs _ _ (by exact teffLit_length) (fun o ho => (hent o ho).2)]
  have hmu : (parOf R45.M3.teffLit 8 0).mu = 0 := rfl
  have hterm : ∀ o ∈ orbits 120 (ellPO.map (·.1)),
      (o.cnt : ℚ) * minQ (parOf R45.M3.teffLit 8 0) o.s (ymaxQ (parOf R45.M3.teffLit 8 0) o.n) =
        (o.cnt : ℚ) * gQ PU2 o.s (8 * kap * dotNQ o.n R45.M3.teffLit) := by
    intro o ho
    have hy : ymaxQ (parOf R45.M3.teffLit 8 0) o.n = 8 * kap * dotNQ o.n R45.M3.teffLit := rfl
    rw [hy, minQ_mu0 _ hmu (by decide +kernel) (hent o ho).1
      (mul_nonneg (mul_nonneg (by norm_num) kap_nonneg) (dotNQ_teffLit_nonneg o.n (hent o ho).2))]
    rfl
  rw [List.map_congr_left hterm, hmu]
  have hs := (sums_of_chunks Ls B hlen hall).1
  unfold sumU at hs
  rw [← hLs] at hs
  simp only [zero_mul, sub_zero]
  exact hnum.trans hs

/-- v3: the certificate value from chunk data. -/
theorem certK_v3_of (Ls : List (List Orb)) (B : List (ℚ × ℚ × ℚ))
    (hLs : orbits 120 (ellPO.map (·.1)) = Ls.flatten) (hlen : Ls.length = B.length)
    (hall : (Ls.zip B).all (fun p => chunkOK p.1 p.2.1 p.2.2.1 p.2.2.2) = true)
    (hnum : (117953 / 1000000 : ℚ) ≤
      (B.map (·.2.1)).sum - muV3 * C1v3 * kap * ((1 / (ellN : ℚ)) * (B.map (·.2.2)).sum)) :
    (117953 / 1000000 : ℚ) ≤ lagBound (parOf R45.M3.teffLit C1v3 muV3) (orbits 120 (ellPO.map (·.1))) := by
  have hent := fun o (ho : o ∈ orbits 120 (ellPO.map (·.1))) => orbits_entry ho
  rw [lagBound_orbs _ _ (by exact teffLit_length) (fun o ho => (hent o ho).2)]
  have hs := sums_of_chunks Ls B hlen hall
  have hV : (orbits 120 (ellPO.map (·.1)) |>.map fun o =>
      (o.cnt : ℚ) * minQ (parOf R45.M3.teffLit C1v3 muV3) o.s (ymaxQ (parOf R45.M3.teffLit C1v3 muV3) o.n)).sum =
      sumV Ls.flatten := by
    rw [← hLs]; rfl
  have hD : (orbits 120 (ellPO.map (·.1)) |>.map fun o =>
      (o.cnt : ℚ) * dotNQ o.n (parOf R45.M3.teffLit C1v3 muV3).teff).sum = sumD Ls.flatten := by
    rw [← hLs]; rfl
  rw [hV, hD]
  have hc : (0 : ℚ) ≤ muV3 * C1v3 * kap * (1 / (ellN : ℚ)) := by
    have : (0 : ℚ) ≤ muV3 * C1v3 := by unfold muV3 C1v3; norm_num
    exact mul_nonneg (mul_nonneg this kap_nonneg) (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hs.2.2 hc
  show (117953 / 1000000 : ℚ) ≤ sumV Ls.flatten - muV3 * C1v3 * kap * ((1 / (ellN : ℚ)) * sumD Ls.flatten)
  nlinarith [hs.2.1]

end Romanoff
