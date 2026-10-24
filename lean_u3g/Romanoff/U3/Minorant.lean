import Romanoff.CertK
import RCert.U3

/-!
# U3a: the evaluator's value at any `α` of the simplex is at least the certified vertex bound

`lagBound_ge_U3`: for a table `tab ≥ 0` (120 entries), any `α ≥ 0` with `Σ_{g ∈ div120} α_g ≤ R0t + δ` and any orbit list
with `s > 0` and 120 entries, `boundU3 R0t δ (valU3 tab R0t os) ≤ lagBound (parOf (teffA tab α) 8 0) os`.
Per orbit, `μ = 0` puts the minimum at `Ymax` (`minQ_mu0`); Pintz's inequality `φ(D) ≥ (2j + 1 - D)/(j (j+1))`
(`lin_le_phi`) bounds `φ` below by an affine function; `Ymax(α) = 8 κ (D + Σ_g α_g g N_g)` (`dotNQ_teffA`) makes the
bound affine in `α`; the coefficients of `α` are at most their maximum.
-/

open Finset R45 R45.P45 R45.U3

namespace Romanoff

/-! ## List sums -/

theorem filter_map_sum {M : Type*} [AddCommMonoid M] (p : ℕ → Bool) (f : ℕ → M) :
    ∀ L : List ℕ, ((L.filter p).map f).sum = (L.map fun x => if p x = true then f x else 0).sum
  | [] => by simp
  | x :: L => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← filter_map_sum p f L]
    by_cases h : p x = true
    · simp [h]
    · simp [h]

theorem range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ k : ℕ, ((List.range k).map f).sum = ∑ c ∈ range k, f c
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, range_map_sum f k, sum_range_succ]
    simp

theorem sum_list_swap {β : Type*} (L : List ℕ) (a : ℕ → ℚ) (F : β → ℕ → ℚ) :
    ∀ os : List β, (os.map fun o => (L.map fun g => a g * F o g).sum).sum =
      (L.map fun g => a g * (os.map fun o => F o g).sum).sum
  | [] => by simp
  | o :: os => by
    rw [List.map_cons, List.sum_cons, sum_list_swap L a F os, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro g _
    rw [List.map_cons, List.sum_cons]
    ring

theorem sum_mul_list_swap (L : List ℕ) (n : ℕ → ℚ) (T : ℕ → ℕ → ℚ) (k : ℕ) :
    ∑ c ∈ range k, n c * (L.map fun g => T g c).sum = (L.map fun g => ∑ c ∈ range k, n c * T g c).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, sum_add_distrib, ih]

theorem zipWith_map_add (f g : ℕ → ℚ) : ∀ L : List ℕ,
    List.zipWith (· + ·) (L.map f) (L.map g) = L.map fun x => f x + g x
  | [] => rfl
  | x :: L => by rw [List.map_cons, List.map_cons, List.zipWith_cons_cons, zipWith_map_add f g L, List.map_cons]

theorem sum_map_sub' {β : Type*} (f g : β → ℚ) : ∀ L : List β,
    (L.map fun x => f x - g x).sum = (L.map f).sum - (L.map g).sum
  | [] => by simp
  | x :: L => by rw [List.map_cons, List.sum_cons, sum_map_sub' f g L, List.map_cons, List.sum_cons, List.map_cons,
      List.sum_cons]; ring

theorem foldl_max_ge_init : ∀ (L : List ℚ) (init : ℚ), init ≤ L.foldl max init
  | [], _ => le_refl _
  | x :: L, init => le_trans (le_max_left init x) (foldl_max_ge_init L _)

theorem le_foldl_max : ∀ (L : List ℚ) (init : ℚ), ∀ x ∈ L, x ≤ L.foldl max init
  | [], _, x, hx => by simp at hx
  | y :: L, init, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right init x) (foldl_max_ge_init L _)
    · exact le_foldl_max L _ x hx

/-! ## The table `teffA` and the linearity of `Ymax` in `α` -/

theorem teffA_length (tab : List ℚ) (α : ℕ → ℚ) : (teffA tab α).length = 120 := by
  unfold teffA; simp

theorem teffA_getD (tab : List ℚ) (α : ℕ → ℚ) {c : ℕ} (hc : c < 120) :
    (teffA tab α).getD c 0 = tab.getD c 0 + tailA α c := by
  unfold teffA
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

theorem tailA_eq (α : ℕ → ℚ) (c : ℕ) :
    tailA α c = (div120.map fun g => if c % g = 0 then (g : ℚ) * α g else 0).sum := by
  unfold tailA
  rw [filter_map_sum]
  simp only [beq_iff_eq]

theorem ngAux_eq (g : ℕ) : ∀ (n : List ℕ) (k : ℕ),
    ((ngAux g k n : ℕ) : ℚ) = ∑ i ∈ range n.length, if (k + i) % g = 0 then ((n.getD i 0 : ℕ) : ℚ) else 0
  | [], _ => by simp [ngAux]
  | x :: xs, k => by
    rw [ngAux, Nat.cast_add, ngAux_eq g xs (k + 1), List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero, beq_iff_eq]
    rw [add_comm]
    congr 1
    · apply sum_congr rfl
      intro i _
      rw [show k + (i + 1) = k + 1 + i by ring]
    · split_ifs <;> simp

theorem ngOf_eq (n : List ℕ) (hn : n.length = 120) (g : ℕ) :
    ((ngOf n g : ℕ) : ℚ) = ∑ c ∈ range 120, if c % g = 0 then ((n.getD c 0 : ℕ) : ℚ) else 0 := by
  unfold ngOf
  rw [ngAux_eq g n 0, hn]
  simp only [Nat.zero_add]

theorem tailA_nonneg (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (c : ℕ) : 0 ≤ tailA α c := by
  unfold tailA
  apply List.sum_nonneg
  intro x hx
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (Nat.cast_nonneg _) (hα g)

theorem teffA_nonneg (tab : List ℚ) (htab0 : ∀ c, 0 ≤ tab.getD c 0) (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (c : ℕ) :
    0 ≤ (teffA tab α).getD c 0 := by
  by_cases hc : c < 120
  · rw [teffA_getD tab α hc]; exact add_nonneg (htab0 c) (tailA_nonneg α hα c)
  · rw [List.getD_eq_default _ _ (by rw [teffA_length]; omega)]

/-- `Σ_c n(c) (tab(c) + Σ_{g ∣ c} g α_g) = Σ_c n(c) tab(c) + Σ_g α_g g N_g`. -/
theorem dotNQ_teffA (n : List ℕ) (hn : n.length = 120) (tab : List ℚ) (htab : tab.length = 120) (α : ℕ → ℚ) :
    dotNQ n (teffA tab α) = dotNQ n tab + (div120.map fun g => α g * ((g : ℚ) * (ngOf n g : ℚ))).sum := by
  unfold dotNQ
  rw [dotNQ_eq n _ 0 (by rw [hn, teffA_length]), dotNQ_eq n tab 0 (by rw [hn, htab]), zero_add, zero_add, hn]
  have h1 : ∀ c ∈ range 120, ((n.getD c 0 : ℕ) : ℚ) * (teffA tab α).getD c 0 =
      ((n.getD c 0 : ℕ) : ℚ) * tab.getD c 0 + ((n.getD c 0 : ℕ) : ℚ) *
        (div120.map fun g => if c % g = 0 then (g : ℚ) * α g else 0).sum := by
    intro c hc
    rw [teffA_getD tab α (mem_range.mp hc), tailA_eq, mul_add]
  rw [sum_congr rfl h1, sum_add_distrib]
  congr 1
  rw [sum_mul_list_swap div120 (fun c => ((n.getD c 0 : ℕ) : ℚ)) (fun g c => if c % g = 0 then (g : ℚ) * α g else 0)]
  apply congrArg
  apply List.map_congr_left
  intro g _
  rw [ngOf_eq n hn, mul_sum, mul_sum]
  apply sum_congr rfl
  intro c _
  split_ifs <;> ring

/-! ## One orbit -/

/-- `w = cnt · norm / l`. -/
def wO (o : Orb) : ℚ := (o.cnt : ℚ) * (R45.P45.norm * (1 / (ellN : ℚ)))

/-- The constant term of one orbit. -/
def a0D (R0t : ℚ) (o : Orb) (D : ℚ) : ℚ :=
  wO o * (2 * (jOf R0t o D : ℚ) * (o.s : ℚ) - 8 * kap * D) / ((jOf R0t o D : ℚ) * ((jOf R0t o D : ℚ) + 1))

/-- The coefficient of `α_g` of one orbit. -/
def agD (R0t : ℚ) (o : Orb) (D : ℚ) (g : ℕ) : ℚ :=
  wO o * (8 * kap * ((g : ℚ) * (ngOf o.n g : ℚ))) / ((jOf R0t o D : ℚ) * ((jOf R0t o D : ℚ) + 1))

theorem vecD_eq (R0t : ℚ) (o : Orb) (D : ℚ) : vecD R0t o D = a0D R0t o D :: div120.map (agD R0t o D) := rfl

theorem jOf_pos (R0t : ℚ) (o : Orb) (D : ℚ) : 1 ≤ jOf R0t o D := le_max_left _ _

theorem normP_nonneg : (0 : ℚ) ≤ R45.P45.norm := by
  unfold R45.P45.norm per ellN philN R45.D45.log2hi
  norm_num [R45.D45.ellPO]

/-- `Σ_g α_g (W 8 K g N_g / d) = W 8 K (Σ_g α_g g N_g) / d`. -/
theorem sum_coef (W K d : ℚ) (α N : ℕ → ℚ) : ∀ L : List ℕ,
    (L.map fun g => α g * (W * (8 * K * ((g : ℚ) * N g)) / d)).sum =
      W * (8 * K * (L.map fun g => α g * ((g : ℚ) * N g)).sum) / d
  | [] => by simp
  | g :: L => by rw [List.map_cons, List.sum_cons, sum_coef W K d α N L, List.map_cons, List.sum_cons]; ring

/-- The affine step: with `Y = 8 K (D + G)` and `φ ≥ (2j + 1 - (1 + Y/s)) / (j (j+1))`. -/
theorem affine_step (W K s j D G Y φv : ℚ) (hW : 0 ≤ W) (hs : 0 < s) (hj : 1 ≤ j) (hY : Y = 8 * K * (D + G))
    (hφ : (2 * j + 1 - (1 + Y / s)) / (j * (j + 1)) ≤ φv) :
    W * (2 * j * s - 8 * K * D) / (j * (j + 1)) - W * (8 * K * G) / (j * (j + 1)) ≤ W * s * φv := by
  have hd : 0 < j * (j + 1) := by positivity
  have key : W * (2 * j * s - 8 * K * D) / (j * (j + 1)) - W * (8 * K * G) / (j * (j + 1)) =
      W * s * ((2 * j + 1 - (1 + Y / s)) / (j * (j + 1))) := by
    rw [hY]; field_simp; ring
  rw [key]
  exact mul_le_mul_of_nonneg_left hφ (mul_nonneg hW hs.le)

/-- Pintz's inequality at a rational point: `(2j + 1 - D)/(j (j+1)) ≤ phiQ D` (`j ≥ 1`, `D ≥ 1`). -/
theorem lin_le_phiQ {j : ℕ} (hj : 1 ≤ j) {D : ℚ} (hD : 1 ≤ D) :
    (2 * (j : ℚ) + 1 - D) / ((j : ℚ) * ((j : ℚ) + 1)) ≤ phiQ D := by
  have h1 := lin_le_phi hj (D := (D : ℝ)) (by exact_mod_cast hD)
  rw [← phiQ_eq D hD] at h1
  unfold lin at h1
  exact_mod_cast h1

set_option maxRecDepth 8000 in
/-- One orbit: the affine minorant is at most the orbit's term of `lagBound` (at `μ = 0`). -/
theorem orbit_minorant (tab : List ℚ) (htab : tab.length = 120) (htab0 : ∀ c, 0 ≤ tab.getD c 0) (R0t : ℚ)
    (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (o : Orb) (hs : 0 < o.s) (hn : o.n.length = 120) :
    a0D R0t o (dotNQ o.n tab) - (div120.map fun g => α g * agD R0t o (dotNQ o.n tab) g).sum ≤
      (o.cnt : ℚ) * minQ (parOf (teffA tab α) 8 0) o.s (ymaxQ (parOf (teffA tab α) 8 0) o.n) := by
  have hs' : (0 : ℚ) < (o.s : ℚ) := by exact_mod_cast hs
  have hY : ymaxQ (parOf (teffA tab α) 8 0) o.n =
      8 * kap * (dotNQ o.n tab + (div120.map fun g => α g * ((g : ℚ) * (ngOf o.n g : ℚ))).sum) := by
    show 8 * kap * dotNQ o.n (teffA tab α) = _
    rw [dotNQ_teffA o.n hn tab htab α]
  have hdot0 : 0 ≤ dotNQ o.n (teffA tab α) := by
    unfold dotNQ
    rw [dotNQ_eq o.n _ 0 (by rw [hn, teffA_length]), zero_add]
    exact sum_nonneg fun c _ => mul_nonneg (Nat.cast_nonneg _) (teffA_nonneg tab htab0 α hα c)
  have hY0 : 0 ≤ ymaxQ (parOf (teffA tab α) 8 0) o.n :=
    mul_nonneg (mul_nonneg (show (0 : ℚ) ≤ 8 by norm_num) kap_nonneg) hdot0
  rw [minQ_mu0 _ rfl normP_nonneg hs hY0]
  have hgQ : ∀ Y : ℚ, gQ (parOf (teffA tab α) 8 0) o.s Y =
      R45.P45.norm * (1 / (ellN : ℚ)) * (o.s : ℚ) * phiQ (1 + Y / (o.s : ℚ)) := by
    intro Y
    show R45.P45.norm * (1 / (ellN : ℚ)) * (o.s : ℚ) * phiQ (1 + Y / (o.s : ℚ)) + (1 / (ellN : ℚ)) * 0 * Y = _
    ring
  rw [hgQ]
  have hD1 : (1 : ℚ) ≤ 1 + ymaxQ (parOf (teffA tab α) 8 0) o.n / (o.s : ℚ) := by
    have := div_nonneg hY0 hs'.le; linarith
  have hφ := lin_le_phiQ (jOf_pos R0t o (dotNQ o.n tab)) hD1
  have hW : 0 ≤ wO o := by
    unfold wO
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg normP_nonneg (by positivity))
  have hstep := affine_step (wO o) kap (o.s : ℚ) (jOf R0t o (dotNQ o.n tab) : ℚ) (dotNQ o.n tab)
    ((div120.map fun g => α g * ((g : ℚ) * (ngOf o.n g : ℚ))).sum) _ _ hW hs'
    (by exact_mod_cast jOf_pos R0t o (dotNQ o.n tab)) hY hφ
  have hsum : (div120.map fun g => α g * agD R0t o (dotNQ o.n tab) g).sum =
      wO o * (8 * kap * (div120.map fun g => α g * ((g : ℚ) * (ngOf o.n g : ℚ))).sum) /
        ((jOf R0t o (dotNQ o.n tab) : ℚ) * ((jOf R0t o (dotNQ o.n tab) : ℚ) + 1)) :=
    sum_coef (wO o) kap _ α (fun g => (ngOf o.n g : ℚ)) div120
  rw [hsum]
  unfold a0D
  calc _ ≤ wO o * (o.s : ℚ) * phiQ (1 + ymaxQ (parOf (teffA tab α) 8 0) o.n / (o.s : ℚ)) := hstep
    _ = (o.cnt : ℚ) * (R45.P45.norm * (1 / (ellN : ℚ)) * (o.s : ℚ) *
          phiQ (1 + ymaxQ (parOf (teffA tab α) 8 0) o.n / (o.s : ℚ))) := by unfold wO; ring

/-! ## The orbit list -/

/-- `Σ_o a0` and `Σ_o a_g` over an orbit list. -/
def sumA0 (tab : List ℚ) (R0t : ℚ) (os : List Orb) : ℚ := (os.map fun o => a0D R0t o (dotNQ o.n tab)).sum
def sumAg (tab : List ℚ) (R0t : ℚ) (os : List Orb) (g : ℕ) : ℚ := (os.map fun o => agD R0t o (dotNQ o.n tab) g).sum

set_option maxRecDepth 8000 in
theorem foldl_vec (tab : List ℚ) (R0t : ℚ) : ∀ (os : List Orb) (x : ℚ) (f : ℕ → ℚ),
    os.foldl (fun acc o => addV acc (vecD R0t o (dotNQ o.n tab))) (x :: div120.map f) =
      (x + sumA0 tab R0t os) :: div120.map (fun g => f g + sumAg tab R0t os g)
  | [], x, f => by simp [sumA0, sumAg]
  | o :: os, x, f => by
    rw [List.foldl_cons, vecD_eq]
    have h : addV (x :: div120.map f) (a0D R0t o (dotNQ o.n tab) :: div120.map (agD R0t o (dotNQ o.n tab))) =
        (x + a0D R0t o (dotNQ o.n tab)) :: div120.map (fun g => f g + agD R0t o (dotNQ o.n tab) g) := by
      unfold addV
      rw [List.zipWith_cons_cons, zipWith_map_add]
    rw [h, foldl_vec tab R0t os]
    congr 1
    · unfold sumA0
      rw [List.map_cons, List.sum_cons]
      ring
    · apply List.map_congr_left
      intro g _
      unfold sumAg
      rw [List.map_cons, List.sum_cons]
      ring

set_option maxRecDepth 8000 in
theorem valU3_eq (tab : List ℚ) (R0t : ℚ) (os : List Orb) :
    valU3 tab R0t os = sumA0 tab R0t os :: div120.map (sumAg tab R0t os) := by
  unfold valU3
  have hz : zeroV = (0 : ℚ) :: div120.map (fun _ => (0 : ℚ)) := rfl
  rw [hz, foldl_vec]
  simp

set_option maxRecDepth 8000 in
/-- The certified vertex bound is at most the evaluator's value at any `α` of the enlarged simplex. -/
theorem lagBound_ge_U3 (tab : List ℚ) (htab : tab.length = 120) (htab0 : ∀ c, 0 ≤ tab.getD c 0) (R0t δ : ℚ)
    (os : List Orb) (hos : ∀ o ∈ os, 0 < o.s ∧ o.n.length = 120) (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g)
    (hαs : (div120.map α).sum ≤ R0t + δ) :
    boundU3 R0t δ (valU3 tab R0t os) ≤ lagBound (parOf (teffA tab α) 8 0) os := by
  rw [valU3_eq]
  unfold boundU3
  simp only [List.headD_cons, List.tail_cons]
  set M := (div120.map (sumAg tab R0t os)).foldl max 0 with hM
  have hM0 : 0 ≤ M := foldl_max_ge_init _ _
  have hMg : ∀ g ∈ div120, sumAg tab R0t os g ≤ M := fun g hg =>
    le_foldl_max _ _ _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  rw [lagBound_orbs _ os (teffA_length tab α) (fun o ho => (hos o ho).2)]
  have hmu : (parOf (teffA tab α) 8 0).mu = 0 := rfl
  rw [hmu]
  simp only [zero_mul, sub_zero]
  -- Σ_o (a0 - Σ_g α_g a_g) ≤ Σ_o cnt minQ
  have hle : (os.map fun o => a0D R0t o (dotNQ o.n tab) -
      (div120.map fun g => α g * agD R0t o (dotNQ o.n tab) g).sum).sum ≤
      (os.map fun o => (o.cnt : ℚ) * minQ (parOf (teffA tab α) 8 0) o.s (ymaxQ (parOf (teffA tab α) 8 0) o.n)).sum := by
    apply List.sum_le_sum
    intro o ho
    exact orbit_minorant tab htab htab0 R0t α hα o (hos o ho).1 (hos o ho).2
  have hswap : (os.map fun o => (div120.map fun g => α g * agD R0t o (dotNQ o.n tab) g).sum).sum =
      (div120.map fun g => α g * (os.map fun o => agD R0t o (dotNQ o.n tab) g).sum).sum :=
    sum_list_swap div120 α (fun o g => agD R0t o (dotNQ o.n tab) g) os
  rw [sum_map_sub', hswap] at hle
  -- Σ_g α_g A_g ≤ M Σ_g α_g ≤ M (R0t + δ)
  have h2 : (div120.map fun g => α g * (os.map fun o => agD R0t o (dotNQ o.n tab) g).sum).sum ≤
      M * (div120.map α).sum := by
    calc (div120.map fun g => α g * (os.map fun o => agD R0t o (dotNQ o.n tab) g).sum).sum
        ≤ (div120.map fun g => α g * M).sum := by
          apply List.sum_le_sum
          intro g hg
          have := hMg g hg
          unfold sumAg at this
          exact mul_le_mul_of_nonneg_left this (hα g)
      _ = M * (div120.map α).sum := by rw [List.sum_map_mul_right, mul_comm]
  have h3 : M * (div120.map α).sum ≤ M * (R0t + δ) := mul_le_mul_of_nonneg_left hαs hM0
  unfold sumA0
  linarith

end Romanoff
