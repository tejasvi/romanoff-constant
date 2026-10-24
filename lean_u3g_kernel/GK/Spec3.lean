import GK.Checks

/-!
# k45g, proofs part 3: the row values of a fibered core row are the native evaluator's

For a mask `M` of (19, 73, 37) with `Fib M` and a signature `σ` with `sigOKb M σ = true`, the native `Rrow vt Y` of the core row
`Y = repB 120 360 R ∪ M` equals `sigVal vt (nRg R) (zrRow R) σ` (`Rrow_eq_sigVal`), given the pattern check `patsOK = true`.
-/

open Finset R45 R45.EVG Romanoff.G.S2

namespace R45.GK

attribute [local irreducible] R45.GK.pats R45.GK.sigs R45.GK.sigF R45.GK.o41r

/-! ## Small list facts -/

theorem dotL_append (A B C D : List ℕ) (h : A.length = C.length) : dotL (A ++ B) (C ++ D) = dotL A C + dotL B D := by
  induction A generalizing C with
  | nil => cases C <;> simp_all [dotL_nil_left]
  | cons a A ih => cases C with
    | nil => simp at h
    | cons c C => simp only [List.cons_append, dotL_cons_cons, ih C (by simpa using h)]; ring

theorem dotL_map_range' (f : ℕ → ℕ) : ∀ (L : List ℕ) (s : ℕ),
    dotL ((List.range' s L.length).map f) L = ∑ k ∈ range L.length, f (s + k) * L.getD k 0
  | [], s => by simp [dotL_nil_left]
  | x :: L, s => by
    rw [List.length_cons, List.range'_succ, List.map_cons, dotL_cons_cons, dotL_map_range' f L (s + 1), sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [show s + (k + 1) = s + 1 + k by ring]

theorem dotL_map_range (f : ℕ → ℕ) (L : List ℕ) (n : ℕ) (hL : L.length = n) :
    dotL ((List.range n).map f) L = ∑ k ∈ range n, f k * L.getD k 0 := by
  subst hL
  rw [List.range_eq_range', dotL_map_range' f L 0]
  simp

theorem sumL_zipWith_dotL (A B : List (List ℕ)) (n : ℕ) (hA : A.length = n) (hB : B.length = n) :
    sumL (List.zipWith dotL A B) = ∑ t ∈ range n, dotL (A.getD t []) (B.getD t []) := by
  subst hA
  induction A generalizing B with
  | nil => simp [sumL]
  | cons a A ih =>
    cases B with
    | nil => simp at hB
    | cons b B =>
      simp only [List.zipWith_cons_cons, sumL, List.length_cons, sum_range_succ']
      rw [ih B (by simpa using hB)]
      simp [add_comm]

/-! ## The divisors of 360 split into `9 ∤ g` (H0) and `9 | g` (3 H1) -/

def c0L : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 18, 21]
def c1L : List ℕ := [7, 11, 15, 17, 19, 20, 22, 23]

theorem sum24_split {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ c ∈ range 24, F c = ∑ q ∈ range 16, F (c0L.getD q 0) + ∑ q ∈ range 8, F (c1L.getD q 0) := by
  simp only [sum_range_succ, sum_range_zero, c0L, c1L, List.getD_cons_succ, List.getD_cons_zero, zero_add]
  abel

theorem c0_facts : ∀ q < 16, dC.getD (c0L.getD q 0) 0 = H0.getD q 0 ∧ H0.getD q 0 % 9 ≠ 0 ∧
    Nat.gcd (H0.getD q 0) 120 = H0.getD q 0 ∧ ∀ t < 4, bnC.getD (24 * t + c0L.getD q 0) 0 = (bn0.getD t []).getD q 0 := by
  decide

theorem c1_facts : ∀ q < 8, dC.getD (c1L.getD q 0) 0 = 3 * H1.getD q 0 ∧ (3 * H1.getD q 0) % 9 = 0 ∧
    Nat.gcd (3 * H1.getD q 0) 120 = H1.getD q 0 ∧ H1.getD q 0 % 3 = 0 ∧
    ∀ t < 4, bnC.getD (24 * t + c1L.getD q 0) 0 = (bn1.getD t []).getD q 0 := by
  decide

theorem dC_mem : ∀ c < 24, dC.getD c 0 ∈ dCl := by decide

theorem H0_len : H0.length = 16 := rfl
theorem H1_len : H1.length = 8 := rfl
theorem bn0_len : ∀ t < 4, (bn0.getD t []).length = 16 := by decide
theorem bn1_len : ∀ t < 4, (bn1.getD t []).length = 8 := by decide

/-! ## `T^R_h(a, b)` vanishes for `3 | h` and `a ≢ b (mod 3)` -/

theorem TR_zero (R h a b : ℕ) (h3 : h % 3 = 0) (hab : a % 3 ≠ b % 3) : TR R h a b = 0 := by
  rw [TR_eq]
  refine sum_eq_zero fun m _ => sum_eq_zero fun m' _ => ?_
  rw [if_neg]
  intro hc
  have h3' : 3 ∣ h := Nat.dvd_of_mod_eq_zero h3
  have := congrArg (· % 3) hc
  simp only [Nat.mod_mod_of_dvd _ h3'] at this
  omega

/-! ## Helpers on the evaluator's lists -/

theorem getD_map_range (f : ℕ → ℕ) {n a : ℕ} (ha : a < n) : ((List.range n).map f).getD a 0 = f a := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha)]; simp

theorem dotL_map_list (A H : List ℕ) (g : ℕ → ℕ) (h : A.length = H.length) :
    dotL A (H.map g) = ∑ q ∈ range A.length, A.getD q 0 * g (H.getD q 0) := by
  induction A generalizing H with
  | nil => simp [dotL_nil_left]
  | cons a A ih =>
    cases H with
    | nil => simp at h
    | cons x H =>
      rw [List.map_cons, dotL_cons_cons, ih H (by simpa using h), List.length_cons, sum_range_succ']
      simp [add_comm]

/-- `Σ_{h ∈ H0} bn0[t]_h T^R_h(a, b)`. -/
def S0 (R t a b : ℕ) : ℕ := ∑ q ∈ range 16, (bn0.getD t []).getD q 0 * TR R (H0.getD q 0) a b
/-- `Σ_{h ∈ H1} bn1[t]_h T^R_h(a, b)`. -/
def S1 (R t a b : ℕ) : ℕ := ∑ q ∈ range 8, (bn1.getD t []).getD q 0 * TR R (H1.getD q 0) a b

theorem S1_zero (R t a b : ℕ) (hab : a % 3 ≠ b % 3) : S1 R t a b = 0 := by
  unfold S1
  refine sum_eq_zero fun q hq => ?_
  rw [TR_zero R _ a b (c1_facts q (mem_range.mp hq)).2.2.2.1 hab, mul_zero]

theorem zr_entry (R : ℕ) {t k : ℕ} (ht : t < 4) (hk : k < 10) :
    ((zrRow R).getD t []).getD k [] =
      (pairs9 (puL.getD k 0) (pvL.getD k 0)).map (fun ab => S0 R t ab.1 ab.2) ++
        (pairsZ (puL.getD k 0) (pvL.getD k 0)).map (fun ab => S1 R t ab.1 ab.2) := by
  have e0 : ∀ ab : ℕ × ℕ, dotL (bn0.getD t []) (H0.map fun h => TR R h ab.1 ab.2) = S0 R t ab.1 ab.2 := by
    intro ab; rw [dotL_map_list _ _ _ (by rw [bn0_len t ht, H0_len]), bn0_len t ht]; rfl
  have e1 : ∀ ab : ℕ × ℕ, dotL (bn1.getD t []) (H1.map fun h => TR R h ab.1 ab.2) = S1 R t ab.1 ab.2 := by
    intro ab; rw [dotL_map_list _ _ _ (by rw [bn1_len t ht, H1_len]), bn1_len t ht]; rfl
  interval_cases t <;> interval_cases k <;>
    simp only [zrRow, trList, List.zip, List.zipWith, List.map, List.getD_cons_succ, List.getD_cons_zero, puL, pvL,
      bn0, bn1, List.append_cancel_left_eq] <;> simp only [← e0, ← e1] <;> rfl

/-! ## The `s` value of a pattern -/

theorem s_eq (R M : ℕ) (hM : Fib M) (σ : Sig) (hfwg : σ.fwg = fwgOfT ((List.range 12).map (fwE M))) (P : ℕ)
    (hpf : (pats.getD P patD).pf = (List.range 4).map fun u => pfA.getD (4 * P + u) 0) :
    sOf ((csOf (repB 120 360 R ||| M)).map fun c => (c.getD 0 #[]).getD 0 0) P =
      dotL (pats.getD P patD).pf (List.zipWith dotL σ.fwg (nRg R)) := by
  rw [sOf_eq, hpf, hfwg]
  rw [sum_congr rfl fun u hu => by rw [n4_spec _ u (mem_range.mp hu), cnt4_fib R M hM (mem_range.mp hu)]]
  simp only [fwgOfT, nRg, List.map, List.zipWith, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    dotL_cons_cons, dotL_nil_left, sum_range_succ, sum_range_zero, zero_add, add_zero,
    getD_map_range (fwE M) (show (0 : ℕ) < 12 by norm_num), List.getD_cons_succ, List.getD_cons_zero]
  simp only [getD_map_range (fwE M) (by norm_num : (1 : ℕ) < 12), getD_map_range (fwE M) (by norm_num : (2 : ℕ) < 12),
    getD_map_range (fwE M) (by norm_num : (3 : ℕ) < 12), getD_map_range (fwE M) (by norm_num : (4 : ℕ) < 12),
    getD_map_range (fwE M) (by norm_num : (5 : ℕ) < 12), getD_map_range (fwE M) (by norm_num : (6 : ℕ) < 12),
    getD_map_range (fwE M) (by norm_num : (7 : ℕ) < 12), getD_map_range (fwE M) (by norm_num : (8 : ℕ) < 12),
    getD_map_range (fwE M) (by norm_num : (9 : ℕ) < 12), getD_map_range (fwE M) (by norm_num : (10 : ℕ) < 12),
    getD_map_range (fwE M) (by norm_num : (11 : ℕ) < 12), fwE_eq]
  ring

/-! ## The `Z` values of a fibered core row -/

theorem fw_get (M : ℕ) {a : ℕ} (ha : a < 12) : ((List.range 12).map (fwE M)).getD a 0 = fwM M a := by
  rw [getD_map_range _ ha, fwE_eq]

theorem puL_eq : ∀ k < 10, puL.getD k 0 = pu.getD k 0 ∧ pvL.getD k 0 = pv.getD k 0 := by decide

theorem Zsum_split (R M t u v : ℕ) (ht : t < 4) :
    ∑ c ∈ range 24, bnC.getD (24 * t + c) 0 * ∑ i ∈ range 3, ∑ j ∈ range 3,
        WtM M (dC.getD c 0) (u + 4 * i) (v + 4 * j) * TR R (Nat.gcd (dC.getD c 0) 120) (u + 4 * i) (v + 4 * j) =
      ∑ i ∈ range 3, ∑ j ∈ range 3, (fwM M (u + 4 * i) * fwM M (v + 4 * j) * S0 R t (u + 4 * i) (v + 4 * j) +
        w1M M (u + 4 * i) (v + 4 * j) * S1 R t (u + 4 * i) (v + 4 * j)) := by
  rw [sum24_split]
  have h0 : ∀ q ∈ range 16, bnC.getD (24 * t + c0L.getD q 0) 0 * ∑ i ∈ range 3, ∑ j ∈ range 3,
      WtM M (dC.getD (c0L.getD q 0) 0) (u + 4 * i) (v + 4 * j) *
        TR R (Nat.gcd (dC.getD (c0L.getD q 0) 0) 120) (u + 4 * i) (v + 4 * j) =
      ∑ i ∈ range 3, ∑ j ∈ range 3, fwM M (u + 4 * i) * fwM M (v + 4 * j) *
        ((bn0.getD t []).getD q 0 * TR R (H0.getD q 0) (u + 4 * i) (v + 4 * j)) := by
    intro q hq
    obtain ⟨e1, e2, e3, e4⟩ := c0_facts q (mem_range.mp hq)
    rw [e1, e3, e4 t ht, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold WtM
    rw [if_neg e2]; ring
  have h1 : ∀ q ∈ range 8, bnC.getD (24 * t + c1L.getD q 0) 0 * ∑ i ∈ range 3, ∑ j ∈ range 3,
      WtM M (dC.getD (c1L.getD q 0) 0) (u + 4 * i) (v + 4 * j) *
        TR R (Nat.gcd (dC.getD (c1L.getD q 0) 0) 120) (u + 4 * i) (v + 4 * j) =
      ∑ i ∈ range 3, ∑ j ∈ range 3, w1M M (u + 4 * i) (v + 4 * j) *
        ((bn1.getD t []).getD q 0 * TR R (H1.getD q 0) (u + 4 * i) (v + 4 * j)) := by
    intro q hq
    obtain ⟨e1, e2, e3, _, e5⟩ := c1_facts q (mem_range.mp hq)
    rw [e1, e3, e5 t ht, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold WtM
    rw [if_pos e2]; ring
  rw [sum_congr rfl h0, sum_congr rfl h1, sum_comm, sum_comm (s := range 8)]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm, sum_comm (s := range 8), ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  unfold S0 S1
  rw [mul_sum, mul_sum]

theorem Z_eq (R M : ℕ) (hM : Fib M) (σ : Sig) (hc : σ.c = cOfT M ((List.range 12).map (fwE M))) {t k : ℕ} (ht : t < 4)
    (hk : k < 10) :
    (zOf (tOf (csOf (repB 120 360 R ||| M)))).getD (10 * t + k) 0 = dotL (σ.c.getD k []) (((zrRow R).getD t []).getD k []) := by
  rw [zOf_spec _ ht hk]
  rw [sum_congr rfl fun c hc' => by rw [tOf_spec _ (mem_range.mp hc') hk,
    Tc_fib R M hM (dC_mem c (mem_range.mp hc')) (pu_lt k hk) (pv_lt k hk)]]
  rw [Zsum_split R M t _ _ ht, zr_entry R ht hk, hc]
  obtain ⟨hu, hv⟩ := puL_eq k hk
  rw [← hu, ← hv]
  interval_cases k <;>
    simp only [cOfT, puL, pvL, List.zip, List.zipWith, List.map, List.getD_cons_succ, List.getD_cons_zero, pairs9, pairsZ,
      List.cons_append, List.nil_append, dotL_cons_cons, dotL_nil_left, sum_range_succ, sum_range_zero, zero_add, add_zero,
      fw_get M (show (0 : ℕ) < 12 by norm_num), fw_get M (show (1 : ℕ) < 12 by norm_num),
      fw_get M (show (2 : ℕ) < 12 by norm_num), fw_get M (show (3 : ℕ) < 12 by norm_num),
      fw_get M (show (4 : ℕ) < 12 by norm_num), fw_get M (show (5 : ℕ) < 12 by norm_num),
      fw_get M (show (6 : ℕ) < 12 by norm_num), fw_get M (show (7 : ℕ) < 12 by norm_num),
      fw_get M (show (8 : ℕ) < 12 by norm_num), fw_get M (show (9 : ℕ) < 12 by norm_num),
      fw_get M (show (10 : ℕ) < 12 by norm_num), fw_get M (show (11 : ℕ) < 12 by norm_num), w1E_eq] <;>
    norm_num [S1_zero] <;> ring

end R45.GK
