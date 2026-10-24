import Romanoff.Pintz
import RCert.Lag

/-!
# Soundness of the per-class minimum and the Lagrangian bound

`minQ_le`: for real `0 ≤ Y ≤ Ymax`, `minQ ≤ w φ(1 + Y/s) + μ Y / l` (`w = norm s / l`): the function is affine between
consecutive candidates (`φ` is affine on each `[j, j+1]`), so it is at least the smaller endpoint value.
`lagrangian_sum`: weak duality with one multiplier `μ ≥ 0` for the summed budget.
-/

namespace Romanoff

open R45

theorem rat_floor_eq (q : ℚ) : q.floor = ⌊q⌋ := rfl

theorem phiQ_eq (D : ℚ) (hD : 1 ≤ D) : ((phiQ D : ℚ) : ℝ) = phi (D : ℝ) := by
  have hD' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hfl : ((D.floor.toNat : ℕ) : ℝ) = (⌊(D : ℝ)⌋₊ : ℝ) := by
    congr 1
    rw [← Int.floor_toNat, Rat.floor_cast (α := ℝ)]
    rfl
  unfold phiQ phi
  simp only
  split_ifs with hj
  · -- D is the integer j
    have hj' : (D : ℝ) = ((D.floor.toNat : ℕ) : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hj
      push_cast at this; linarith
    rw [← hfl, ← hj']
    have hpos : (0 : ℝ) < (D : ℝ) := by linarith
    push_cast
    rw [show ((D.floor.toNat : ℕ) : ℝ) = (D : ℝ) from hj'.symm]
    field_simp
    ring
  · push_cast
    rw [← hfl]

/-- An affine function on `[a, b]` is at least the smaller endpoint value. -/
theorem affine_ge_min {A B a b Y : ℝ} (ha : a ≤ Y) (hb : Y ≤ b) :
    min (A + B * a) (A + B * b) ≤ A + B * Y := by
  rcases le_or_gt 0 B with hB | hB
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem foldl_min_le_init (f : ℚ → ℚ) : ∀ (L : List ℚ) (x : ℚ), L.foldl (fun best y => min best (f y)) x ≤ x
  | [], x => le_rfl
  | y :: L, x => (foldl_min_le_init f L (min x (f y))).trans (min_le_left _ _)

theorem foldl_min_le_mem (f : ℚ → ℚ) : ∀ (L : List ℚ) (x y : ℚ), y ∈ L →
    L.foldl (fun best y => min best (f y)) x ≤ f y
  | [], x, y, h => by simp at h
  | z :: L, x, y, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (foldl_min_le_init f L _).trans (min_le_right _ _)
    · exact foldl_min_le_mem f L _ y h

theorem minQ_le_gQ (P : Par) (s : ℕ) (ymax y : ℚ) (hy : y ∈ candsQ s ymax) : minQ P s ymax ≤ gQ P s y :=
  foldl_min_le_mem _ _ _ y hy

theorem mem_candsQ_mul {s : ℕ} (hs : 0 < s) {ymax : ℚ} {j : ℕ} (hj : (s : ℚ) * j ≤ ymax) :
    (s : ℚ) * j ∈ candsQ s ymax := by
  unfold candsQ
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
  rw [List.mem_filterMap]
  refine ⟨j, List.mem_range.mpr ?_, by simp [hj]⟩
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have h1 : (j : ℚ) ≤ ymax / s := by rw [le_div_iff₀ hs']; linarith
  have h2 : (j : ℤ) ≤ (ymax / s).floor := by rw [rat_floor_eq]; exact Int.le_floor.mpr (by exact_mod_cast h1)
  omega

/-- The real-valued function of one class. -/
noncomputable def gR (P : Par) (s : ℕ) (Y : ℝ) : ℝ :=
  (P.norm : ℝ) * (1 / (P.ell : ℝ)) * s * phi (1 + Y / s) + (1 / (P.ell : ℝ)) * P.mu * Y

theorem gQ_cast (P : Par) (s : ℕ) (hs : 0 < s) (y : ℚ) (hy : 0 ≤ y) : ((gQ P s y : ℚ) : ℝ) = gR P s y := by
  unfold gQ gR
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hys : 0 ≤ y / s := div_nonneg hy hs'.le
  have hD : (1 : ℚ) ≤ 1 + y / s := by linarith
  push_cast
  rw [phiQ_eq _ hD]
  push_cast
  ring

/-- Soundness of the per-class minimum. -/
theorem minQ_le (P : Par) (s : ℕ) (hs : 0 < s) (ymax : ℚ) (hymax : 0 ≤ ymax) (Y : ℝ) (hY0 : 0 ≤ Y)
    (hY1 : Y ≤ ymax) : ((minQ P s ymax : ℚ) : ℝ) ≤ gR P s Y := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set j := ⌊Y / s⌋₊ with hjdef
  have hj1 : (j : ℝ) ≤ Y / s := Nat.floor_le (div_nonneg hY0 hs'.le)
  have hj2 : Y / s < j + 1 := Nat.lt_floor_add_one _
  have ha : (s : ℝ) * j ≤ Y := by rw [le_div_iff₀ hs'] at hj1; linarith
  have hb : Y < (s : ℝ) * (j + 1) := by rw [div_lt_iff₀ hs'] at hj2; linarith
  -- the left endpoint `s j` is a candidate
  have hjq : (s : ℚ) * j ≤ ymax := by
    have : ((s : ℚ) * j : ℚ) = ((s : ℝ) * j : ℝ) := by push_cast; ring
    exact_mod_cast (show ((s : ℝ) * j) ≤ ymax by linarith)
  have hca := minQ_le_gQ P s ymax _ (mem_candsQ_mul hs hjq)
  -- the right endpoint: `s (j + 1)` or `Ymax`
  set b : ℚ := min ((s : ℚ) * (j + 1 : ℕ)) ymax with hbdef
  have hcb : minQ P s ymax ≤ gQ P s b := by
    apply minQ_le_gQ
    show min ((s : ℚ) * (j + 1 : ℕ)) ymax ∈ candsQ s ymax
    rcases le_total ((s : ℚ) * (j + 1 : ℕ)) ymax with h | h
    · rw [min_eq_left h]; exact mem_candsQ_mul hs h
    · rw [min_eq_right h]; exact List.mem_cons_of_mem _ (List.mem_cons_self)
  have hbY : Y ≤ (b : ℝ) := by
    rw [hbdef]; push_cast
    exact le_min (by push_cast; linarith) hY1
  have hbj : (b : ℝ) ≤ (s : ℝ) * (j + 1) := by rw [hbdef]; push_cast; exact min_le_left _ _
  have hb0 : (0 : ℚ) ≤ b := by
    rw [hbdef]; exact le_min (by positivity) hymax
  have hsj0 : (0 : ℚ) ≤ (s : ℚ) * j := by positivity
  -- affine on [s j, b]
  have hjpos : 1 ≤ j + 1 := by omega
  have haff : ∀ Z : ℝ, (s : ℝ) * j ≤ Z → Z ≤ (s : ℝ) * (j + 1) → gR P s Z =
      ((P.norm : ℝ) * (1 / (P.ell : ℝ)) * s * ((2 * ((j + 1 : ℕ) : ℝ) + 1 - 1) / (((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) + 1)))) +
      (-(P.norm : ℝ) * (1 / (P.ell : ℝ)) * s * (1 / s) / (((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) + 1)) +
        (1 / (P.ell : ℝ)) * P.mu) * Z := by
    intro Z hZ1 hZ2
    unfold gR
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ 1 + Z / s := by
      push_cast
      have : (j : ℝ) ≤ Z / s := by rw [le_div_iff₀ hs']; linarith
      linarith
    have h2 : 1 + Z / s ≤ ((j + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      have : Z / s ≤ (j : ℝ) + 1 := by rw [div_le_iff₀ hs']; linarith
      linarith
    rw [phi_eq_of_mem hjpos h1 h2]
    field_simp
    ring
  have hgY := haff Y ha hb.le
  have hga := haff ((s : ℚ) * j : ℚ) (by push_cast; linarith) (by push_cast; nlinarith)
  have hgb := haff b (by linarith) hbj
  rw [← gQ_cast P s hs _ hsj0] at hga
  rw [← gQ_cast P s hs _ hb0] at hgb
  have hmin := affine_ge_min (A := (P.norm : ℝ) * (1 / (P.ell : ℝ)) * s *
      ((2 * ((j + 1 : ℕ) : ℝ) + 1 - 1) / (((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) + 1))))
    (B := -(P.norm : ℝ) * (1 / (P.ell : ℝ)) * s * (1 / s) / (((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) + 1)) +
        (1 / (P.ell : ℝ)) * P.mu) (show ((((s : ℚ) * j : ℚ)) : ℝ) ≤ Y by push_cast; linarith) hbY
  rw [← hga, ← hgb, ← hgY] at hmin
  have hca' : ((minQ P s ymax : ℚ) : ℝ) ≤ ((gQ P s ((s : ℚ) * j) : ℚ) : ℝ) := by exact_mod_cast hca
  have hcb' : ((minQ P s ymax : ℚ) : ℝ) ≤ ((gQ P s b : ℚ) : ℝ) := by exact_mod_cast hcb
  exact (le_min hca' hcb').trans hmin

/-- Weak duality with one multiplier for the summed budget. -/
theorem lagrangian_sum {ι : Type*} (S : Finset ι) (G : ι → ℝ → ℝ) (Y ymax d : ι → ℝ) (m : ι → ℝ) (μ budget : ℝ)
    (hμ : 0 ≤ μ) (hY : ∀ k ∈ S, 0 ≤ Y k ∧ Y k ≤ ymax k) (hbud : ∑ k ∈ S, d k * Y k ≤ budget)
    (hm : ∀ k ∈ S, ∀ y, 0 ≤ y → y ≤ ymax k → m k ≤ G k y + d k * μ * y) :
    ∑ k ∈ S, m k - μ * budget ≤ ∑ k ∈ S, G k (Y k) := by
  have h1 : ∑ k ∈ S, m k ≤ ∑ k ∈ S, (G k (Y k) + d k * μ * Y k) :=
    Finset.sum_le_sum fun k hk => hm k hk (Y k) (hY k hk).1 (hY k hk).2
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ k ∈ S, d k * μ * Y k = μ * ∑ k ∈ S, d k * Y k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left hbud hμ]

end Romanoff
