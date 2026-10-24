import Romanoff.G.S2.Ind

/-!
# U3g/V4g stage 2: the row quantities of the evaluator

For a core mask `Y` and residues `r23 < 23`, `r43 < 43`, `r29 < 29`, the row `rowX Y r23 r43 r29` at period 27720 has
* `s_row`: `|U| = sOf n4 P` and
* `Q_row`: `Q(U) = Σ_{t < 4} Σ_{c < 24} ⌈B_{dC[c] τ_t} 2^32⌉ S_{dC[c] τ_t}(U) = qOf Z P`,
with `P = patOf r23 r43 r29` the combined pattern and `n4`, `Z` the arrays that `rowStep` computes from `mrow Y`
(`s_prod`, `S_prod` with the tables of the pattern, and the symmetric pairs `u ≤ v`).
-/

open Finset R45 R45.EVG

namespace Romanoff.G.S2

/-- `Q(X) = Σ_{t < 4} Σ_{c < 24} ⌈B_{dC[c] τ_t} 2^32⌉ S_{dC[c] τ_t}(X)` at period 27720. -/
def Qs (X : ℕ) : ℕ := ∑ t ∈ range 4, ∑ c ∈ range 24, bnC.getD (24 * t + c) 0 * SP 27720 X (dC.getD c 0 * tau t)

/-- The row at period 27720 of the core mask `Y` and the residues `(r23, r43, r29)`. -/
def rowX (Y r23 r43 r29 : ℕ) : ℕ :=
  repB 360 27720 Y ||| maskP 27720 23 r23 ||| maskP 27720 43 r43 ||| maskP 27720 29 r29

/-- The combined pattern of the residues. -/
def patOf (r23 r43 r29 : ℕ) : ℕ := np11 * sig7.getD (29 * r43 + r29) 0 + sig11.getD r23 0

theorem patOf_div (r23 r43 r29 : ℕ) (h23 : r23 < 23) : patOf r23 r43 r29 / np11 = sig7.getD (29 * r43 + r29) 0 := by
  have hb := (tab11 h23).1
  unfold patOf
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < np11), Nat.div_eq_of_lt hb, zero_add]

theorem patOf_mod (r23 r43 r29 : ℕ) (h23 : r23 < 23) : patOf r23 r43 r29 % np11 = sig11.getD r23 0 := by
  have hb := (tab11 h23).1
  unfold patOf
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem patOf_lt {r23 r43 r29 : ℕ} (h23 : r23 < 23) (h43 : r43 < 43) (h29 : r29 < 29) : patOf r23 r43 r29 < npC := by
  have ha := (tab7 h43 h29).1
  have hb := (tab11 h23).1
  unfold patOf npC
  calc np11 * sig7.getD (29 * r43 + r29) 0 + sig11.getD r23 0 < np11 * sig7.getD (29 * r43 + r29) 0 + np11 := by omega
    _ = np11 * (sig7.getD (29 * r43 + r29) 0 + 1) := by ring
    _ ≤ np11 * np7 := Nat.mul_le_mul_left _ ha
    _ = np7 * np11 := by ring

/-! ## The pattern tables in the evaluator -/

theorem pfA_getD {P u : ℕ} (hP : P < npC) (hu : u < 4) : pfA.getD (4 * P + u) 0 = pf P u := by
  rw [getD_eq_getElem' _ _ _ (by simp [pfA]; omega)]
  simp only [pfA, Array.getElem_ofFn]
  congr 1 <;> omega

theorem pqA_getD {P t k : ℕ} (hP : P < npC) (ht : t < 4) (hk : k < 10) :
    pqA.getD (40 * P + (10 * t + k)) 0 = pw P t k := by
  rw [getD_eq_getElem' _ _ _ (by simp [pqA]; omega)]
  simp only [pqA, Array.getElem_ofFn]
  congr 1 <;> omega

theorem sOf_eq (n4 : Array ℕ) (P : ℕ) : sOf n4 P = ∑ u ∈ range 4, pfA.getD (4 * P + u) 0 * n4.getD u 0 := by
  unfold sOf; rw [foldl_range_add, zero_add]

theorem qOf_eq (Z : Array ℕ) (P : ℕ) :
    qOf Z P = ∑ t ∈ range 4, ∑ k ∈ range 10, pqA.getD (40 * P + (10 * t + k)) 0 * Z.getD (10 * t + k) 0 := by
  unfold qOf
  rw [foldl_range_add, zero_add, show (40 : ℕ) = 4 * 10 by norm_num,
    sum_range_mul_split 10 (fun i => pqA.getD (4 * 10 * P + i) 0 * Z.getD i 0) 4]

/-! ## `s` -/

theorem s_row (Y : ℕ) {r23 r43 r29 : ℕ} (h23 : r23 < 23) (h43 : r43 < 43) (h29 : r29 < 29) :
    cntP 27720 (rowX Y r23 r43 r29) 1 0 =
      sOf ((csOf Y).map fun c => (c.getD 0 #[]).getD 0 0) (patOf r23 r43 r29) := by
  rw [rowX, s_prod (prodForm_row Y r23 r43 r29), sOf_eq]
  refine sum_congr rfl fun u hu => ?_
  have hu' := mem_range.mp hu
  rw [pfA_getD (patOf_lt h23 h43 h29) hu', n4_spec Y u hu', (tab7 h43 h29).2 u hu' |>.1, (tab11 h23).2 u hu' |>.1]
  unfold pf
  rw [patOf_div _ _ _ h23, patOf_mod _ _ _ h23]

/-! ## `Q` -/

/-- The table entry `W^{τ_t}(u, v)` of the pattern `(a, b)` (the second factor of `pw`). -/
def Wpat (a b t u v : ℕ) : ℕ :=
  if t = 0 then f7.getD (4 * a + u) 0 * f7.getD (4 * a + v) 0 * (f11.getD (4 * b + u) 0 * f11.getD (4 * b + v) 0)
  else if t = 1 then q7.getD (16 * a + 4 * u + v) 0 * (f11.getD (4 * b + u) 0 * f11.getD (4 * b + v) 0)
  else if t = 2 then f7.getD (4 * a + u) 0 * f7.getD (4 * a + v) 0 * q11.getD (16 * b + 4 * u + v) 0
  else q7.getD (16 * a + 4 * u + v) 0 * q11.getD (16 * b + 4 * u + v) 0

theorem pw_eq (P t k : ℕ) :
    pw P t k = (if pu.getD k 0 = pv.getD k 0 then 1 else 2) * Wpat (P / np11) (P % np11) t (pu.getD k 0) (pv.getD k 0) := by
  rfl

theorem Wq_symm (q : ℕ) (φ : ℕ → ℕ → ℕ) (b : Bool) (u v : ℕ) : Wq q φ b u v = Wq q φ b v u := by
  unfold Wq
  cases b
  · simp [mul_comm]
  · simp only [if_true]; exact sum_congr rfl fun y _ => mul_comm _ _

theorem W_row {r23 r43 r29 : ℕ} (h23 : r23 < 23) (h43 : r43 < 43) (h29 : r29 < 29) {t u v : ℕ} (ht : t < 4)
    (hu : u < 4) (hv : v < 4) :
    Wq 7 (phi7 r43 r29) (b7 t) u v * Wq 11 (phi11 r23) (b11 t) u v =
      Wpat (sig7.getD (29 * r43 + r29) 0) (sig11.getD r23 0) t u v := by
  have t7 := (tab7 h43 h29).2
  have t11 := (tab11 h23).2
  unfold Wq
  rw [(t7 u hu).1, (t7 v hv).1, (t7 u hu).2 v hv, (t11 u hu).1, (t11 v hv).1, (t11 u hu).2 v hv]
  unfold Wpat
  interval_cases t <;> simp [b7, b11]

/-- `Σ_{u, v < 4} A(u, v) = Σ_{k < 10} m_k A(u_k, v_k)` for symmetric `A`. -/
theorem sym_fold (A : ℕ → ℕ → ℕ) (hA : ∀ u v, A u v = A v u) :
    ∑ u ∈ range 4, ∑ v ∈ range 4, A u v =
      ∑ k ∈ range 10, (if pu.getD k 0 = pv.getD k 0 then 1 else 2) * A (pu.getD k 0) (pv.getD k 0) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e : ∀ k, k < 10 → (pu.getD k 0, pv.getD k 0) =
      ((#[0, 0, 0, 0, 1, 1, 1, 2, 2, 3] : Array ℕ).getD k 0, (#[0, 1, 2, 3, 1, 2, 3, 2, 3, 3] : Array ℕ).getD k 0) :=
    fun k _ => rfl
  simp only [pu, pv, Array.getD, Array.size, List.length_cons, List.length_nil]
  norm_num
  rw [hA 1 0, hA 2 0, hA 3 0, hA 2 1, hA 3 1, hA 3 2]
  ring

theorem Q_row (Y : ℕ) {r23 r43 r29 : ℕ} (h23 : r23 < 23) (h43 : r43 < 43) (h29 : r29 < 29) :
    Qs (rowX Y r23 r43 r29) = qOf (zOf (tOf (csOf Y))) (patOf r23 r43 r29) := by
  have hP := patOf_lt h23 h43 h29
  rw [qOf_eq]
  unfold Qs
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  -- `S` of each divisor by the factorization and the tables
  have e1 : ∀ c ∈ range 24, bnC.getD (24 * t + c) 0 * SP 27720 (rowX Y r23 r43 r29) (dC.getD c 0 * tau t) =
      ∑ k ∈ range 10, (if pu.getD k 0 = pv.getD k 0 then 1 else 2) *
        Wpat (sig7.getD (29 * r43 + r29) 0) (sig11.getD r23 0) t (pu.getD k 0) (pv.getD k 0) *
          (bnC.getD (24 * t + c) 0 * Tc Y (dC.getD c 0) (pu.getD k 0) (pv.getD k 0)) := by
    intro c hc
    have hc' := mem_range.mp hc
    rw [rowX, S_prod (prodForm_row Y r23 r43 r29) (dC_facts c hc').2 (dC_facts c hc').1 ht',
      sym_fold (fun u v => Wq 7 (phi7 r43 r29) (b7 t) u v * Wq 11 (phi11 r23) (b11 t) u v * Tc Y (dC.getD c 0) u v)
        (fun u v => by rw [Wq_symm 7 _ _ u v, Wq_symm 11 _ _ u v, Tc_symm]), mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [W_row h23 h43 h29 ht' (pu_lt k hk') (pv_lt k hk')]
    ring
  rw [sum_congr rfl e1, Finset.sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have e2 : ∑ c ∈ range 24, bnC.getD (24 * t + c) 0 * (tOf (csOf Y)).getD (10 * c + k) 0 =
      ∑ c ∈ range 24, bnC.getD (24 * t + c) 0 * Tc Y (dC.getD c 0) (pu.getD k 0) (pv.getD k 0) :=
    sum_congr rfl fun c hc => by rw [tOf_spec Y (mem_range.mp hc) hk']
  rw [pqA_getD hP ht' hk', pw_eq, patOf_div _ _ _ h23, patOf_mod _ _ _ h23, zOf_spec _ ht' hk', e2, mul_sum]

end Romanoff.G.S2
