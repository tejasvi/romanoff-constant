import Romanoff.G.S2.Row
import Romanoff.G.M4C
import Romanoff.U3.Minorant
import RCert.G.BLit
import RCert.M3G.TeffLit

/-!
# U3g/V4g stage 2: the minorant of one row (uniform budget multiplier `μ ≥ 0`)

* `lagBound_eq_wsumB`: `lagBound P (orbits 27720 ps) = Σ_{(x, c) ∈ foldOrbits} c · phiClsB P x`, where the per-class term
  `phiClsB` is `minQ(s, Ymax) - μ C1 Ymax / (CAP l)` (the budget term `μ C1 κ Σ_c N(c) T(c)` spread over the classes);
* `minQ_ge`: weak duality on the cap of one class: `minQ P s Ymax ≥ (s h - ν Ymax) / l` for `ν ≥ 0` and
  `h ≤ norm φ(D) + (μ + ν)(D - 1)` (`D ≥ 1`); `bracket_le`: such an `h` is `norm/i + λ(i - 1)` at an integer `i` with
  `norm/(i(i+1)) ≤ λ ≤ norm/((i-1)i)`;
* `mino`: `vtM μ C1 i J |U| Q(U) ≤ phiClsB P X` for every row `X` (`Ymax = 8 κ Σ_g (B_g + g α_g) S_g`, `B_g ≤ bn_g/2^32`,
  `g S_g ≤ 27720 |U|`, `Σ α ≤ R0t + δ`).
-/

open Finset R45 R45.EVG R45.U3G

namespace Romanoff.G.S2

/-! ## The budget term per class -/

/-- `μ C1 / (l CAP)`. -/
def coefB (P : Par) : ℚ := P.mu * P.c1 / ((P.ell : ℚ) * P.cap)

/-- The per-class term with the budget term: `minQ(s, Ymax) - μ C1 Ymax / (l CAP)` (`0` if `U = ∅`). -/
def phiClsB (P : Par) (x : ℕ) : ℚ :=
  if full 27720 ^^^ x = 0 then 0 else
    minQ P (popcount 27720 (full 27720 ^^^ x)) (ymaxQ P (nShift 27720 (full 27720 ^^^ x))) -
      coefB P * ymaxQ P (nShift 27720 (full 27720 ^^^ x))

theorem phiClsB_rot (P : Par) {x : ℕ} (hx : x < 2 ^ 27720) : phiClsB P (rot1 27720 x) = phiClsB P x := by
  unfold phiClsB
  have hu := full_xor_lt 27720 x hx
  rw [full_xor_rot1 (by norm_num) hx, popcount_rot1 (by norm_num) hu, nShift_rot1 (by norm_num) hu]
  have h0 : rot1 27720 (full 27720 ^^^ x) = 0 ↔ full 27720 ^^^ x = 0 := by
    rw [eq_zero_iff_popcount (rot1_lt 27720 _), eq_zero_iff_popcount hu, popcount_rot1 (by norm_num) hu]
  simp only [h0]

theorem ncQ_eq (P : Par) (os : List Orb) (c : ℕ) :
    ncQ P os c = (os.map fun o => (o.cnt : ℚ) / (P.ell : ℚ) * ((o.n.getD c 0 : ℕ) : ℚ)).sum := by
  unfold ncQ
  rw [foldl_add_eq_sum, zero_add]

theorem sum_ncQ (P : Par) (t : List ℚ) (ht : t.length = 27720) :
    ∀ os : List Orb, (∀ o ∈ os, o.n.length = 27720) →
      ∑ c ∈ range 27720, ncQ P os c * t.getD c 0 = (os.map fun o => (o.cnt : ℚ) / (P.ell : ℚ) * dotNQ o.n t).sum
  | [], _ => by simp [ncQ_eq]
  | o :: os, h => by
    have ih := sum_ncQ P t ht os (fun o' ho' => h o' (by simp [ho']))
    have ho : o.n.length = 27720 := h o (by simp)
    have e : ∑ c ∈ range 27720, (o.cnt : ℚ) / (P.ell : ℚ) * ((o.n.getD c 0 : ℕ) : ℚ) * t.getD c 0 =
        (o.cnt : ℚ) / (P.ell : ℚ) * dotNQ o.n t := by
      rw [dotNQ, dotNQ_eq o.n t 0 (by rw [ho, ht]), zero_add, ho, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      ring
    rw [List.map_cons, List.sum_cons, ← ih, ← e, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    rw [ncQ_eq, ncQ_eq, List.map_cons, List.sum_cons, add_mul]

theorem sum_orbits_budget (P : Par) (t : List ℚ) (ps : List ℕ) :
    ((orbits 27720 ps).map fun o => (o.cnt : ℚ) / (P.ell : ℚ) * dotNQ o.n t).sum =
      wsum (foldOrbits 27720 ps) (fun x => if full 27720 ^^^ x = 0 then 0 else
        1 / (P.ell : ℚ) * dotNQ (nShift 27720 (full 27720 ^^^ x)) t) := by
  unfold orbits wsum
  generalize foldOrbits 27720 ps = L
  induction L with
  | nil => simp
  | cons xc L ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h : full 27720 ^^^ xc.1 = 0
    · simp only [h, if_true, mul_zero, zero_add]
      rw [← ih]
    · simp only [h, if_false]
      rw [List.map_cons, List.sum_cons, ih]
      congr 1
      ring

theorem wsum_sub (L : List (ℕ × ℕ)) (f g : ℕ → ℚ) (a : ℚ) :
    wsum L f - a * wsum L g = wsum L (fun x => f x - a * g x) := by
  induction L with
  | nil => simp [wsum]
  | cons xc L ih =>
    rw [wsum_cons, wsum_cons, wsum_cons, ← ih]
    ring

theorem orbits_n_length (per : ℕ) (ps : List ℕ) : ∀ o ∈ orbits per ps, o.n.length = per := by
  intro o ho
  simp only [orbits, List.mem_filterMap] at ho
  obtain ⟨xc, _, hxc⟩ := ho
  by_cases h0 : full per ^^^ xc.1 = 0
  · rw [if_pos h0] at hxc
    exact absurd hxc (by simp)
  · rw [if_neg h0] at hxc
    rw [← Option.some.inj hxc]
    exact nShift_length _ _

theorem lagBound_eq_wsumB (P : Par) (hper : P.per = 27720) (ht : P.teff.length = 27720) (hcap : P.cap ≠ 0)
    (ps : List ℕ) : lagBound P (orbits 27720 ps) = wsum (foldOrbits 27720 ps) (phiClsB P) := by
  have hlen : ∀ o ∈ orbits 27720 ps, o.n.length = 27720 := orbits_n_length 27720 ps
  rw [lagBoundSplit P _ (by rw [ht, hper]), hper, sum_ncQ P P.teff ht _ hlen, orbSum_orbits, sum_orbits_budget,
    wsum_sub]
  apply wsum_congr
  intro xc _
  unfold phiClsB phiCls coefB ymaxQ
  by_cases h : full 27720 ^^^ xc.1 = 0
  · simp [h]
  · simp only [h, if_false]
    field_simp

/-! ## Weak duality on the cap of one class -/

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

/-- `norm/i + λ(i - 1) ≤ norm φ(D) + λ(D - 1)` for `D ≥ 1` if `norm/(i(i+1)) ≤ λ` and (`i = 1` or `λ ≤ norm/((i-1)i)`). -/
theorem bracket_le {nrm lam : ℚ} (hn : 0 ≤ nrm) {i : ℕ} (hi : 1 ≤ i) (h1 : nrm / ((i : ℚ) * ((i : ℚ) + 1)) ≤ lam)
    (h2 : i = 1 ∨ lam ≤ nrm / (((i : ℚ) - 1) * (i : ℚ))) {D : ℚ} (hD : 1 ≤ D) :
    nrm / (i : ℚ) + lam * ((i : ℚ) - 1) ≤ nrm * phiQ D + lam * (D - 1) := by
  have hi' : (1 : ℚ) ≤ i := by exact_mod_cast hi
  by_cases hDi : (i : ℚ) ≤ D
  · have hφ := lin_le_phiQ hi hD
    have hp : 0 < (i : ℚ) * ((i : ℚ) + 1) := by positivity
    have e1 : nrm * phiQ D ≥ nrm * ((2 * (i : ℚ) + 1 - D) / ((i : ℚ) * ((i : ℚ) + 1))) :=
      mul_le_mul_of_nonneg_left hφ hn
    have key : nrm * ((2 * (i : ℚ) + 1 - D) / ((i : ℚ) * ((i : ℚ) + 1))) + lam * (D - 1) -
        (nrm / (i : ℚ) + lam * ((i : ℚ) - 1)) = (D - i) * (lam - nrm / ((i : ℚ) * ((i : ℚ) + 1))) := by
      field_simp
      ring
    have hk : 0 ≤ (D - i) * (lam - nrm / ((i : ℚ) * ((i : ℚ) + 1))) := mul_nonneg (by linarith) (by linarith)
    linarith
  · push_neg at hDi
    have hi2 : 2 ≤ i := by
      by_contra hc
      have : i = 1 := by omega
      subst this
      norm_num at hDi
      linarith
    have h2' : lam ≤ nrm / (((i : ℚ) - 1) * (i : ℚ)) := h2.resolve_left (by omega)
    have hj : 1 ≤ i - 1 := by omega
    have hφ := lin_le_phiQ hj hD
    have hc : ((i - 1 : ℕ) : ℚ) = (i : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hc] at hφ
    have hi1 : (1 : ℚ) < i := by exact_mod_cast (show 1 < i by omega)
    have hp : 0 < ((i : ℚ) - 1) * ((i : ℚ) - 1 + 1) := by
      have : 0 < (i : ℚ) - 1 := by linarith
      positivity
    have e1 : nrm * phiQ D ≥ nrm * ((2 * ((i : ℚ) - 1) + 1 - D) / (((i : ℚ) - 1) * ((i : ℚ) - 1 + 1))) :=
      mul_le_mul_of_nonneg_left hφ hn
    have key : nrm * ((2 * ((i : ℚ) - 1) + 1 - D) / (((i : ℚ) - 1) * ((i : ℚ) - 1 + 1))) + lam * (D - 1) -
        (nrm / (i : ℚ) + lam * ((i : ℚ) - 1)) = ((i : ℚ) - D) * (nrm / (((i : ℚ) - 1) * (i : ℚ)) - lam) := by
      have : (i : ℚ) - 1 ≠ 0 := by linarith
      have hi0 : (i : ℚ) ≠ 0 := by linarith
      rw [show (i : ℚ) - 1 + 1 = i by ring]
      field_simp
      ring
    have hk : 0 ≤ ((i : ℚ) - D) * (nrm / (((i : ℚ) - 1) * (i : ℚ)) - lam) := mul_nonneg (by linarith) (by linarith)
    linarith

/-- Weak duality: `minQ P s Ymax ≥ (s h - ν Ymax) / l`. -/
theorem minQ_ge (P : Par) {s : ℕ} (hs : 0 < s) {ymax : ℚ} (hy : 0 ≤ ymax) (hell : 0 < (P.ell : ℚ)) {h ν : ℚ}
    (hν : 0 ≤ ν) (hφ : ∀ D : ℚ, 1 ≤ D → h ≤ P.norm * phiQ D + (P.mu + ν) * (D - 1)) :
    1 / (P.ell : ℚ) * ((s : ℚ) * h - ν * ymax) ≤ minQ P s ymax := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hg : ∀ y, 0 ≤ y → y ≤ ymax → 1 / (P.ell : ℚ) * ((s : ℚ) * h - ν * ymax) ≤ gQ P s y := by
    intro y hy0 hyy
    unfold gQ
    have hD : 1 ≤ 1 + y / (s : ℚ) := by have := div_nonneg hy0 hs'.le; linarith
    have h1 := hφ _ hD
    have e : (s : ℚ) * ((P.mu + ν) * (1 + y / (s : ℚ) - 1)) = (P.mu + ν) * y := by field_simp; ring
    have h2 : (s : ℚ) * h - ν * ymax ≤ P.norm * (s : ℚ) * phiQ (1 + y / (s : ℚ)) + P.mu * y := by
      have h3 : (s : ℚ) * h ≤ (s : ℚ) * (P.norm * phiQ (1 + y / (s : ℚ)) + (P.mu + ν) * (1 + y / (s : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left h1 hs'.le
      have h4 : ν * y ≤ ν * ymax := mul_le_mul_of_nonneg_left hyy hν
      nlinarith
    have h5 : 1 / (P.ell : ℚ) * ((s : ℚ) * h - ν * ymax) ≤
        1 / (P.ell : ℚ) * (P.norm * (s : ℚ) * phiQ (1 + y / (s : ℚ)) + P.mu * y) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  unfold minQ
  exact foldl_min_ge _ _ _ _ (hg 0 (le_refl 0) hy) fun y hy' =>
    let hb := mem_candsQ_bounds hy hy'
    hg y hb.1 hb.2

/-! ## The divisors in the `(τ, g_c)` order and `Q` -/

/-- `dC[i mod 24] τ_{i / 24}`, `i < 96`. -/
def gOf (i : ℕ) : ℕ := dC.getD (i % 24) 0 * tau (i / 24)

set_option maxRecDepth 100000 in
theorem divG_perm : R45.M3G.divG.Perm ((List.range 96).map gOf) := by decide +kernel

theorem divG_sum (f : ℕ → ℚ) : (R45.M3G.divG.map f).sum = ∑ t ∈ range 4, ∑ c ∈ range 24, f (dC.getD c 0 * tau t) := by
  rw [(divG_perm.map f).sum_eq, List.map_map, listSum_range_eq, show (96 : ℕ) = 4 * 24 by norm_num,
    sum_range_mul_split 24 _ 4]
  refine sum_congr rfl fun t _ => sum_congr rfl fun c hc => ?_
  have hc' := mem_range.mp hc
  simp only [Function.comp_apply, gOf]
  rw [show (24 * t + c) % 24 = c by omega, show (24 * t + c) / 24 = t by omega]

set_option maxRecDepth 100000 in
theorem bn_ok : ∀ i < 96, 0 ≤ BLit (gOf i) ∧ BLit (gOf i) ≤ (bnC.getD i 0 : ℚ) / 2 ^ 32 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gOf_dvd : ∀ i < 96, 0 < gOf i ∧ gOf i ∣ 27720 := by decide +kernel

theorem R0tG_eq : R0tG = R45.M3G.R0tLit := rfl

/-- `Σ_{g ∈ divG} (B_g + g α_g) S_g ≤ Q / 2^32 + 27720 s (R0t + δ)`. -/
theorem dot_bound (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g) (hαs : (R45.M3G.divG.map α).sum ≤ R45.M3G.R0tLit + delta) (X : ℕ) :
    (R45.M3G.divG.map fun g => (BLit g + (g : ℚ) * α g) * (SP 27720 X g : ℚ)).sum ≤
      (Qs X : ℚ) / 2 ^ 32 + 27720 * (cntP 27720 X 1 0 : ℚ) * (R45.M3G.R0tLit + delta) := by
  rw [divG_sum]
  have h1 : ∀ t ∈ range 4, ∀ c ∈ range 24,
      (BLit (dC.getD c 0 * tau t) + ((dC.getD c 0 * tau t : ℕ) : ℚ) * α (dC.getD c 0 * tau t)) *
        (SP 27720 X (dC.getD c 0 * tau t) : ℚ) ≤
      (bnC.getD (24 * t + c) 0 : ℚ) / 2 ^ 32 * (SP 27720 X (dC.getD c 0 * tau t) : ℚ) +
        α (dC.getD c 0 * tau t) * (27720 * (cntP 27720 X 1 0 : ℚ)) := by
    intro t ht c hc
    have ht' := mem_range.mp ht
    have hc' := mem_range.mp hc
    have hi : 24 * t + c < 96 := by omega
    have hg : gOf (24 * t + c) = dC.getD c 0 * tau t := by
      unfold gOf; rw [show (24 * t + c) % 24 = c by omega, show (24 * t + c) / 24 = t by omega]
    obtain ⟨_, hb⟩ := bn_ok _ hi
    obtain ⟨hg0, hgd⟩ := gOf_dvd _ hi
    rw [hg] at hb hg0 hgd
    have hS : ((dC.getD c 0 * tau t : ℕ) : ℚ) * (SP 27720 X (dC.getD c 0 * tau t) : ℚ) ≤ 27720 * (cntP 27720 X 1 0 : ℚ) := by
      exact_mod_cast SP_le 27720 X hgd hg0 (by norm_num)
    have hS0 : (0 : ℚ) ≤ (SP 27720 X (dC.getD c 0 * tau t) : ℚ) := Nat.cast_nonneg _
    calc (BLit (dC.getD c 0 * tau t) + ((dC.getD c 0 * tau t : ℕ) : ℚ) * α (dC.getD c 0 * tau t)) *
          (SP 27720 X (dC.getD c 0 * tau t) : ℚ)
        = BLit (dC.getD c 0 * tau t) * (SP 27720 X (dC.getD c 0 * tau t) : ℚ) +
            α (dC.getD c 0 * tau t) * (((dC.getD c 0 * tau t : ℕ) : ℚ) * (SP 27720 X (dC.getD c 0 * tau t) : ℚ)) := by
          ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hb hS0) (mul_le_mul_of_nonneg_left hS (hα _))
  refine (sum_le_sum fun t ht => sum_le_sum fun c hc => h1 t ht c hc).trans ?_
  simp only [sum_add_distrib]
  have e1 : ∑ t ∈ range 4, ∑ c ∈ range 24, (bnC.getD (24 * t + c) 0 : ℚ) / 2 ^ 32 *
      (SP 27720 X (dC.getD c 0 * tau t) : ℚ) = (Qs X : ℚ) / 2 ^ 32 := by
    unfold Qs; push_cast; rw [sum_div]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun c _ => ?_
    ring
  have e2 : ∑ t ∈ range 4, ∑ c ∈ range 24, α (dC.getD c 0 * tau t) * (27720 * (cntP 27720 X 1 0 : ℚ)) =
      27720 * (cntP 27720 X 1 0 : ℚ) * (R45.M3G.divG.map α).sum := by
    rw [divG_sum, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    ring
  rw [e1, e2]
  have hc : (0 : ℚ) ≤ 27720 * (cntP 27720 X 1 0 : ℚ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hαs hc)

/-! ## The minorant of one row -/

theorem normG_nonneg : (0 : ℚ) ≤ PG.norm := by
  unfold PG.norm PG.ellN PG.philN PG.per R45.D45.log2hi
  norm_num [PG.ellPO]

theorem kapG_nonneg : (0 : ℚ) ≤ PG.kap := by
  unfold PG.kap PG.pell PG.per R45.D45.C0up R45.D45.log2lo
  norm_num [PG.ellPO]

theorem ellG_pos : (0 : ℚ) < (PG.ellN : ℚ) := by
  unfold PG.ellN; norm_num [PG.ellPO]

theorem SP_zero_of (X : ℕ) (h : cntP 27720 X 1 0 = 0) {g : ℕ} (hg0 : 0 < g) : SP 27720 X g = 0 := by
  have h1 := sum_cntP 27720 X hg0
  rw [h] at h1
  unfold SP
  apply sum_eq_zero
  intro a ha
  have : cntP 27720 X g a = 0 := (sum_eq_zero_iff.mp h1) a ha
  rw [this]; rfl

theorem Qs_zero_of (X : ℕ) (h : cntP 27720 X 1 0 = 0) : Qs X = 0 := by
  unfold Qs
  apply sum_eq_zero; intro t _; apply sum_eq_zero; intro c hc
  rw [SP_zero_of X h (Nat.mul_pos (dC_facts c (mem_range.mp hc)).1 (tau_pos t)), mul_zero]

set_option maxRecDepth 100000 in
theorem pOf_ell (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).ell = PG.ellN := rfl
theorem pOf_norm (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).norm = PG.norm := rfl
theorem pOf_mu (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).mu = mu := rfl
theorem pOf_c1 (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).c1 = c1 := rfl
theorem pOf_cap (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).cap = 8 := rfl
theorem pOf_kap (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).kap = PG.kap := rfl
theorem pOf_teff (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).teff = t := rfl
theorem pOf_per (t : List ℚ) (c1 mu : ℚ) : (PG.parOf t c1 mu).per = 27720 := rfl

theorem BLit_nonneg : ∀ g ∈ R45.M3G.divG, 0 ≤ BLit g := by decide +kernel

/-- The algebra of the minorant (all quantities abstracted). -/
theorem mino_alg {E k R sN Qn Ds M h ν co cm : ℚ} (hE : 0 < E) (hk : 0 ≤ k) (hν : 0 ≤ ν) (hc : 0 ≤ cm)
    (hco : co = 8 * ν + cm) (hM : 1 / E * (sN * h - ν * (8 * k * Ds)) ≤ M)
    (hD : Ds ≤ Qn / 2 ^ 32 + 27720 * sN * R) :
    1 / E * ((h - co * k * 27720 * R) * sN - co * k * Qn / 2 ^ 32) ≤ M - cm / (E * 8) * (8 * k * Ds) := by
  have hco0 : 0 ≤ co := by rw [hco]; positivity
  have h1 : co * k * Ds ≤ co * k * (Qn / 2 ^ 32 + 27720 * sN * R) := mul_le_mul_of_nonneg_left hD (mul_nonneg hco0 hk)
  have e1 : 1 / E * (sN * h - ν * (8 * k * Ds)) - cm / (E * 8) * (8 * k * Ds) = 1 / E * (sN * h - co * k * Ds) := by
    rw [hco]; field_simp; ring
  have e2 : 1 / E * ((h - co * k * 27720 * R) * sN - co * k * Qn / 2 ^ 32) ≤ 1 / E * (sN * h - co * k * Ds) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

/-- The minorant of one row: `vtM μ C1 i J |U| Q(U) ≤ phiClsB P X` for `P = parOf (teffA (tabB BLit) α) C1 μ`. -/
theorem mino (mu c1 : ℚ) (hmu : 0 ≤ mu) (hc1 : 0 ≤ c1) (α : ℕ → ℚ) (hα : ∀ g, 0 ≤ α g)
    (hαs : (R45.M3G.divG.map α).sum ≤ R45.M3G.R0tLit + delta) {X : ℕ} (hX : X < 2 ^ 27720) {i J : ℕ} (hi : 1 ≤ i)
    (hb1 : PG.norm / ((i : ℚ) * ((i : ℚ) + 1)) ≤ lamJ mu J)
    (hb2 : i = 1 ∨ lamJ mu J ≤ PG.norm / (((i : ℚ) - 1) * (i : ℚ))) :
    vtM mu c1 i J (cntP 27720 X 1 0) (Qs X) ≤ phiClsB (PG.parOf (teffA (tabB BLit) α) c1 mu) X := by
  have hlam : mu ≤ lamJ mu J := le_max_left _ _
  have hu_lt := full_xor_lt 27720 X hX
  by_cases hs : cntP 27720 X 1 0 = 0
  · have hu : full 27720 ^^^ X = 0 := (eq_zero_iff_popcount hu_lt).mpr (by rw [popcount_fx, hs])
    rw [hs, Qs_zero_of X hs]
    unfold phiClsB vtM
    rw [if_pos hu]
    simp
  · have hs0 : 0 < cntP 27720 X 1 0 := Nat.pos_of_ne_zero hs
    have hu : full 27720 ^^^ X ≠ 0 := fun h0 => hs (by rw [← popcount_fx, (eq_zero_iff_popcount hu_lt).mp h0])
    unfold phiClsB
    rw [if_neg hu, popcount_fx]
    have hD : dotNQ (nShift 27720 (full 27720 ^^^ X)) (teffA (tabB BLit) α) =
        (R45.M3G.divG.map fun g => (BLit g + (g : ℚ) * α g) * (SP 27720 X g : ℚ)).sum := by
      rw [dotNQ_teffA_tabB _ (nShift_length _ _) BLit α]
      refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
      rw [ngOf_nShift X (divG_dvd hg) (divG_pos hg)]
    have hY : ymaxQ (PG.parOf (teffA (tabB BLit) α) c1 mu) (nShift 27720 (full 27720 ^^^ X)) =
        8 * PG.kap * (R45.M3G.divG.map fun g => (BLit g + (g : ℚ) * α g) * (SP 27720 X g : ℚ)).sum := by
      rw [ymaxQ, pOf_cap, pOf_kap, pOf_teff, hD]
    have hDs0 : 0 ≤ (R45.M3G.divG.map fun g => (BLit g + (g : ℚ) * α g) * (SP 27720 X g : ℚ)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (add_nonneg (BLit_nonneg g hg) (mul_nonneg (Nat.cast_nonneg _) (hα g))) (Nat.cast_nonneg _)
    have hymax0 : 0 ≤ ymaxQ (PG.parOf (teffA (tabB BLit) α) c1 mu) (nShift 27720 (full 27720 ^^^ X)) := by
      rw [hY]; exact mul_nonneg (mul_nonneg (by norm_num) kapG_nonneg) hDs0
    have hM := minQ_ge (PG.parOf (teffA (tabB BLit) α) c1 mu) hs0 hymax0 (by rw [pOf_ell]; exact ellG_pos)
      (h := hJ mu i J) (ν := lamJ mu J - mu) (by linarith) (fun D hD1 => by
        rw [pOf_norm, pOf_mu, show mu + (lamJ mu J - mu) = lamJ mu J by ring]
        exact bracket_le normG_nonneg hi hb1 hb2 hD1)
    rw [hY, pOf_ell] at hM
    rw [hY]
    unfold vtM coefB
    rw [pOf_mu, pOf_c1, pOf_ell, pOf_cap, R0tG_eq]
    exact mino_alg ellG_pos kapG_nonneg (by linarith) (mul_nonneg hmu hc1) (by unfold cpJ; ring) hM
      (dot_bound α hα hαs X)

end Romanoff.G.S2
