import Romanoff.M4C
import Romanoff.PhiProps
import K45.Lag.Defs

/-!
# K track of the certificate value: glue for the per-chunk kernel checks

* `minQ_mu0`: with `μ = 0` the per-class minimum is the value at `Ymax` (`φ` is antitone).
* `chunkVals_eq`, `chunkOK_spec`: the kernel's one-pass triple is the triple of sums.
* `lagBound_orbs`: `lagBound P os = Σ cnt·minQ - μ C1 κ (1/l) Σ cnt·D` for an orbit list with `n` of length `per`.
* `sums_of_chunks`: chunk bounds add up over `flatten`.
-/

open Finset R45 R45.P45 R45.K45L

namespace Romanoff

/-! ## The U2 shortcut -/

theorem foldl_min_ge (f : ℚ → ℚ) (v : ℚ) :
    ∀ (L : List ℚ) (init : ℚ), v ≤ init → (∀ y ∈ L, v ≤ f y) → v ≤ L.foldl (fun b y => min b (f y)) init
  | [], init, h0, _ => by simpa using h0
  | y :: L, init, h0, h => by
    rw [List.foldl_cons]
    exact foldl_min_ge f v L _ (le_min h0 (h y List.mem_cons_self)) fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem mem_candsQ_bounds {s : ℕ} {ymax y : ℚ} (hy0 : 0 ≤ ymax) (hy : y ∈ candsQ s ymax) : 0 ≤ y ∧ y ≤ ymax := by
  unfold candsQ at hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact ⟨le_refl 0, hy0⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact ⟨hy0, le_refl _⟩
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hy
  split_ifs at hj with h
  · cases hj; exact ⟨by positivity, h⟩

theorem phiQ_antitone {D D' : ℚ} (hD : 1 ≤ D) (hDD : D ≤ D') : phiQ D' ≤ phiQ D := by
  have h1 := phiQ_eq D hD
  have h2 := phiQ_eq D' (le_trans hD hDD)
  have h3 := phi_antitone (D := (D : ℝ)) (D' := (D' : ℝ)) (by exact_mod_cast hD) (by exact_mod_cast hDD)
  rw [← h1, ← h2] at h3
  exact_mod_cast h3

/-- With `μ = 0`, `minQ` is the value at `Ymax`. -/
theorem minQ_mu0 (P : Par) (hmu : P.mu = 0) (hnorm : 0 ≤ P.norm) {s : ℕ} (hs : 0 < s) {ymax : ℚ}
    (hy : 0 ≤ ymax) : minQ P s ymax = gQ P s ymax := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hmono : ∀ y, 0 ≤ y → y ≤ ymax → gQ P s ymax ≤ gQ P s y := by
    intro y hy0 hyy
    unfold gQ
    rw [hmu]
    simp only [mul_zero, zero_mul, add_zero]
    have h1 : 1 ≤ 1 + y / (s : ℚ) := by have := div_nonneg hy0 hs'.le; linarith
    have h2 : 1 + y / (s : ℚ) ≤ 1 + ymax / s := by have := div_le_div_of_nonneg_right hyy hs'.le; linarith
    have := phiQ_antitone h1 h2
    have hc : 0 ≤ P.norm * (1 / (P.ell : ℚ)) * (s : ℚ) := by positivity
    exact mul_le_mul_of_nonneg_left this hc
  apply le_antisymm
  · exact minQ_le_gQ P s ymax ymax (List.mem_cons_of_mem _ List.mem_cons_self)
  · unfold minQ
    exact foldl_min_ge _ _ _ _ (hmono 0 (le_refl 0) hy) fun y hy' =>
      let h := mem_candsQ_bounds hy hy'
      hmono y h.1 h.2

/-! ## The one-pass triple -/

/-- `Σ cnt·gQ_U2(s, 8 κ D)`, `Σ cnt·minQ_v3(s, 8 κ D)`, `Σ cnt·D` over an orbit list. -/
def sumU (os : List Orb) : ℚ :=
  (os.map fun o => (o.cnt : ℚ) * gQ PU2 o.s (8 * kap * dotNQ o.n R45.M3.teffLit)).sum
def sumV (os : List Orb) : ℚ :=
  (os.map fun o => (o.cnt : ℚ) * minQ PV3 o.s (8 * kap * dotNQ o.n R45.M3.teffLit)).sum
def sumD (os : List Orb) : ℚ := (os.map fun o => (o.cnt : ℚ) * dotNQ o.n R45.M3.teffLit).sum

theorem chunkVals_foldl : ∀ (os : List Orb) (acc : ℚ × ℚ × ℚ),
    os.foldl (fun acc o => stepD acc o (dotNQ o.n R45.M3.teffLit)) acc =
      (acc.1 + sumU os, acc.2.1 + sumV os, acc.2.2 + sumD os)
  | [], acc => by simp [sumU, sumV, sumD]
  | o :: os, acc => by
    rw [List.foldl_cons, chunkVals_foldl os]
    simp only [stepD, sumU, sumV, sumD, List.map_cons, List.sum_cons, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

theorem chunkVals_eq (os : List Orb) : chunkVals os = (sumU os, sumV os, sumD os) := by
  unfold chunkVals
  rw [chunkVals_foldl os (0, 0, 0)]
  simp

theorem chunkOK_spec {os : List Orb} {a b c : ℚ} (h : chunkOK os a b c = true) :
    a ≤ sumU os ∧ b ≤ sumV os ∧ sumD os ≤ c := by
  unfold chunkOK tripleOK at h
  rw [chunkVals_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem sum_flatten {α : Type*} (f : α → ℚ) : ∀ (Ls : List (List α)),
    (Ls.flatten.map f).sum = (Ls.map fun L => (L.map f).sum).sum
  | [] => by simp
  | L :: Ls => by rw [List.flatten_cons, List.map_append, List.sum_append, sum_flatten f Ls, List.map_cons, List.sum_cons]

/-- Chunk bounds add up over `flatten`. -/
theorem sums_of_chunks : ∀ (Ls : List (List Orb)) (B : List (ℚ × ℚ × ℚ)), Ls.length = B.length →
    (Ls.zip B).all (fun p => chunkOK p.1 p.2.1 p.2.2.1 p.2.2.2) = true →
    (B.map (·.1)).sum ≤ sumU Ls.flatten ∧ (B.map (·.2.1)).sum ≤ sumV Ls.flatten ∧
      sumD Ls.flatten ≤ (B.map (·.2.2)).sum
  | [], [], _, _ => by simp [sumU, sumV, sumD]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | L :: Ls, b :: B, h, hall => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    have hL := chunkOK_spec hall.1
    have ih := sums_of_chunks Ls B (by simpa using h) hall.2
    simp only [sumU, sumV, sumD, sum_flatten] at ih ⊢
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    simp only [sumU, sumV, sumD] at hL
    refine ⟨by linarith [hL.1, ih.1], by linarith [hL.2.1, ih.2.1], by linarith [hL.2.2, ih.2.2]⟩

/-! ## `lagBound` of an orbit list -/

theorem foldl_ncQ (P : Par) (c : ℕ) : ∀ (os : List Orb) (a : ℚ),
    os.foldl (fun acc o => acc + (o.cnt : ℚ) / (P.ell : ℚ) * ((o.n.getD c 0 : ℕ) : ℚ)) a =
      a + (os.map fun o => (o.cnt : ℚ) / (P.ell : ℚ) * ((o.n.getD c 0 : ℕ) : ℚ)).sum :=
  foldl_add_eq_sum _

theorem sum_ncQ_teff (P : Par) (ht : P.teff.length = P.per) : ∀ (os : List Orb), (∀ o ∈ os, o.n.length = P.per) →
    ∑ c ∈ range P.per, (os.map fun o => (o.cnt : ℚ) / (P.ell : ℚ) * ((o.n.getD c 0 : ℕ) : ℚ)).sum * P.teff.getD c 0 =
      (1 / (P.ell : ℚ)) * (os.map fun o => (o.cnt : ℚ) * dotNQ o.n P.teff).sum
  | [], _ => by simp
  | o :: os, hn => by
    simp only [List.map_cons, List.sum_cons, add_mul, sum_add_distrib, mul_add]
    rw [sum_ncQ_teff P ht os (fun o' h' => hn o' (List.mem_cons_of_mem _ h'))]
    congr 1
    have hno : o.n.length = P.per := hn o List.mem_cons_self
    unfold dotNQ
    rw [dotNQ_eq o.n P.teff 0 (by rw [hno, ht]), zero_add, hno, mul_sum, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    ring

theorem lagBound_orbs (P : Par) (os : List Orb) (ht : P.teff.length = P.per) (hn : ∀ o ∈ os, o.n.length = P.per) :
    lagBound P os = (os.map fun o => (o.cnt : ℚ) * minQ P o.s (ymaxQ P o.n)).sum -
      P.mu * P.c1 * P.kap * ((1 / (P.ell : ℚ)) * (os.map fun o => (o.cnt : ℚ) * dotNQ o.n P.teff).sum) := by
  rw [lagBoundSplit P os ht]
  have h1 : orbSum P os = (os.map fun o => (o.cnt : ℚ) * minQ P o.s (ymaxQ P o.n)).sum := by
    unfold orbSum; rw [foldl_add_eq_sum, zero_add]
  have e1 : ∀ c, ncQ P os c = (os.map fun o => (o.cnt : ℚ) / (P.ell : ℚ) * ((o.n.getD c 0 : ℕ) : ℚ)).sum := by
    intro c; unfold ncQ; rw [foldl_ncQ, zero_add]
  simp only [e1]
  rw [h1, sum_ncQ_teff P ht os hn]

/-! ## The entries of `orbits` -/

theorem foldOrbits_keys (per : ℕ) (ps : List ℕ) : ∀ xc ∈ foldOrbits per ps, xc.1 < 2 ^ per := by
  unfold foldOrbits
  suffices h : ∀ (qs : List ℕ) (L : List (ℕ × ℕ)), (∀ xc ∈ L, xc.1 < 2 ^ per) →
      ∀ xc ∈ qs.foldl (fun L p => foldStep per L (optsP per p)) L, xc.1 < 2 ^ per from
    h ps _ fun xc hxc => by rw [List.mem_singleton.mp hxc]; exact Nat.two_pow_pos per
  intro qs
  induction qs with
  | nil => intro L hL; simpa using hL
  | cons p qs ih =>
    intro L hL
    rw [List.foldl_cons]
    exact ih _ (foldStep_keys per L _ hL (optsP_lt per p))

theorem orbits_entry {per : ℕ} {ps : List ℕ} {o : Orb} (ho : o ∈ orbits per ps) :
    0 < o.s ∧ o.n.length = per := by
  unfold orbits at ho
  obtain ⟨xc, hxc, hsome⟩ := List.mem_filterMap.mp ho
  have hx := foldOrbits_keys per ps xc hxc
  have hu := full_xor_lt per xc.1 hx
  dsimp only at hsome
  split_ifs at hsome with h0
  cases hsome
  refine ⟨Nat.pos_of_ne_zero fun hp => h0 ((eq_zero_iff_popcount hu).mpr hp), nShift_length per _⟩

end Romanoff
