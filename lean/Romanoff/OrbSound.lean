import Romanoff.FoldSound
import Romanoff.LagSound

/-!
# The orbit sums of the evaluator are sums over all classes `k mod l`

`popcount` and `nShift` are rotation invariant, and so is the complement in `per` bits; hence the per-class quantity
`Φ(ex) = [U ≠ 0] minQ(|U|, Ymax(n_U))`, `U = full ^^^ ex`, is rotation invariant, and the orbit sum of `lagBound` is
`Σ_{k < l} Φ(exmask k)` (`FoldSound`).  The same holds for `N(c)`.
-/

namespace Romanoff

open R45 Finset

theorem foldl_count_eq_card (per : ℕ) (P : ℕ → Bool) :
    ∀ n a, (List.range n).foldl (fun acc e => if P e then acc + 1 else acc) a = a + ((range n).filter fun e => P e).card
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_count_eq_card per P n a,
      Finset.range_add_one, Finset.filter_insert]
    by_cases hP : P n
    · simp only [hP, if_true]
      rw [card_insert_of_notMem (by simp)]; omega
    · simp only [hP, if_false, Bool.false_eq_true]

theorem popcount_eq (per x : ℕ) : popcount per x = ((range per).filter fun e => x.testBit e).card := by
  unfold popcount
  rw [foldl_count_eq_card per (fun e => x.testBit e) per 0, zero_add]

/-- `e ↦ e - 1 mod per` is a bijection of `range per`. -/
theorem card_filter_pred_shift {per : ℕ} (hper : 0 < per) (Q : ℕ → Prop) [DecidablePred Q] :
    ((range per).filter fun e => Q ((e + per - 1) % per)).card = ((range per).filter Q).card := by
  apply card_nbij (fun e => (e + per - 1) % per)
  · intro e he
    simp only [mem_coe, mem_filter, mem_range] at he ⊢
    exact ⟨Nat.mod_lt _ hper, he.2⟩
  · intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_range] at ha hb
    simp only at hab
    have h1 : (a + per - 1) % per = (a + (per - 1)) % per := by congr 1; omega
    have h2 : (b + per - 1) % per = (b + (per - 1)) % per := by congr 1; omega
    rw [h1, h2] at hab
    have := Nat.ModEq.add_right_cancel' (per - 1) hab
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at this
  · intro b hb
    simp only [mem_coe, mem_filter, mem_range] at hb
    refine ⟨(b + 1) % per, ?_, ?_⟩
    · simp only [mem_coe, mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ hper, ?_⟩
      have : ((b + 1) % per + per - 1) % per = b := by
        rcases Nat.lt_or_ge (b + 1) per with h | h
        · rw [Nat.mod_eq_of_lt h, show b + 1 + per - 1 = b + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb.1]
        · have : b + 1 = per := by omega
          rw [this, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
      rw [this]; exact hb.2
    · simp only
      rcases Nat.lt_or_ge (b + 1) per with h | h
      · rw [Nat.mod_eq_of_lt h, show b + 1 + per - 1 = b + per by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb.1]
      · have : b + 1 = per := by omega
        rw [this, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]; omega

theorem popcount_rot1 {per : ℕ} (hper : 0 < per) {x : ℕ} (hx : x < 2 ^ per) : popcount per (rot1 per x) = popcount per x := by
  rw [popcount_eq, popcount_eq]
  have : ((range per).filter fun e => (rot1 per x).testBit e = true) =
      (range per).filter fun e => x.testBit ((e + per - 1) % per) = true := by
    apply filter_congr
    intro e he
    rw [rot1_testBit hper hx]
    simp [mem_range.mp he]
  rw [this, card_filter_pred_shift hper (fun e => x.testBit e = true)]

theorem nShift_getD (per u c : ℕ) (hc : c < per) :
    (nShift per u).getD c 0 = ((range per).filter fun e => u.testBit e && u.testBit ((e + c) % per)).card := by
  unfold nShift
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range,
    foldl_count_eq_card per _ per 0, zero_add]

theorem nShift_length (per u : ℕ) : (nShift per u).length = per := by simp [nShift]

theorem nShift_rot1 {per : ℕ} (hper : 0 < per) {u : ℕ} (hu : u < 2 ^ per) : nShift per (rot1 per u) = nShift per u := by
  apply List.ext_getElem (by simp [nShift_length])
  intro c h1 h2
  rw [nShift_length] at h1
  have e1 := nShift_getD per (rot1 per u) c h1
  have e2 := nShift_getD per u c h1
  rw [List.getD_eq_getElem _ _ (by rw [nShift_length]; exact h1)] at e1
  rw [List.getD_eq_getElem _ _ (by rw [nShift_length]; exact h1)] at e2
  rw [e1, e2]
  have : ((range per).filter fun e => ((rot1 per u).testBit e && (rot1 per u).testBit ((e + c) % per)) = true) =
      (range per).filter fun e => (u.testBit ((e + per - 1) % per) && u.testBit (((e + per - 1) % per + c) % per)) = true := by
    apply filter_congr
    intro e he
    rw [rot1_testBit hper hu, rot1_testBit hper hu]
    simp only [mem_range.mp he, Nat.mod_lt _ hper, decide_true, Bool.true_and]
    have : ((e + c) % per + per - 1) % per = ((e + per - 1) % per + c) % per := by
      rw [show (e + c) % per + per - 1 = (e + c) % per + (per - 1) by omega,
        show e + per - 1 = e + (per - 1) by omega]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mod ((e + (per - 1)) % per), Nat.mod_mod, ← Nat.add_mod]
      congr 1; ring
    simp [this, Nat.mod_lt _ hper]
  rw [this]
  exact card_filter_pred_shift hper (fun e => (u.testBit e && u.testBit ((e + c) % per)) = true)

theorem testBit_full (per e : ℕ) : (full per).testBit e = decide (e < per) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem full_xor_rot1 {per : ℕ} (hper : 0 < per) {x : ℕ} (hx : x < 2 ^ per) :
    full per ^^^ rot1 per x = rot1 per (full per ^^^ x) := by
  have hxor : full per ^^^ x < 2 ^ per :=
    Nat.xor_lt_two_pow (by rw [full_eq]; exact Nat.sub_lt (Nat.two_pow_pos per) one_pos) hx
  apply Nat.eq_of_testBit_eq
  intro e
  rw [Nat.testBit_xor, rot1_testBit hper hx, rot1_testBit hper hxor, Nat.testBit_xor, testBit_full, testBit_full]
  by_cases he : e < per
  · simp [he, Nat.mod_lt _ hper]
  · simp [he]

/-! ## The per-class contribution and the orbit sums -/

theorem eq_zero_iff_popcount {per u : ℕ} (hu : u < 2 ^ per) : u = 0 ↔ popcount per u = 0 := by
  rw [popcount_eq, card_eq_zero, filter_eq_empty_iff]
  constructor
  · rintro rfl e _; simp
  · intro h
    apply Nat.eq_of_testBit_eq
    intro e
    rw [Nat.zero_testBit]
    by_cases he : e < per
    · simpa using h (mem_range.mpr he)
    · exact testBit_eq_false_of_lt_pow hu (by omega)

theorem full_xor_lt (per x : ℕ) (hx : x < 2 ^ per) : full per ^^^ x < 2 ^ per :=
  Nat.xor_lt_two_pow (by rw [full_eq]; exact Nat.sub_lt (Nat.two_pow_pos per) one_pos) hx

/-- The per-class contribution of an exclusion mask `x` (`U = full ^^^ x`; `0` if `U = ∅`). -/
def phiCls (P : Par) (per x : ℕ) : ℚ :=
  if full per ^^^ x = 0 then 0 else minQ P (popcount per (full per ^^^ x)) (ymaxQ P (nShift per (full per ^^^ x)))

theorem phiCls_rot {per : ℕ} (hper : 0 < per) (P : Par) {x : ℕ} (hx : x < 2 ^ per) :
    phiCls P per (rot1 per x) = phiCls P per x := by
  unfold phiCls
  have hu := full_xor_lt per x hx
  rw [full_xor_rot1 hper hx, popcount_rot1 hper hu, nShift_rot1 hper hu]
  have h0 : rot1 per (full per ^^^ x) = 0 ↔ full per ^^^ x = 0 := by
    rw [eq_zero_iff_popcount (rot1_lt per _), eq_zero_iff_popcount hu, popcount_rot1 hper hu]
  simp only [h0]

/-- The orbit sum of the evaluator. -/
def orbSum (P : Par) (os : List Orb) : ℚ := os.foldl (fun acc o => acc + (o.cnt : ℚ) * minQ P o.s (ymaxQ P o.n)) 0

theorem foldl_add_eq_sum {α : Type*} (f : α → ℚ) : ∀ (L : List α) (a : ℚ),
    L.foldl (fun acc o => acc + f o) a = a + (L.map f).sum
  | [], a => by simp
  | x :: L, a => by rw [List.foldl_cons, foldl_add_eq_sum f L, List.map_cons, List.sum_cons]; ring

theorem orbSum_orbits (P : Par) (per : ℕ) (ps : List ℕ) :
    orbSum P (orbits per ps) = wsum (foldOrbits per ps) (phiCls P per) := by
  unfold orbSum orbits wsum
  rw [foldl_add_eq_sum, zero_add]
  generalize foldOrbits per ps = L
  induction L with
  | nil => simp
  | cons xc L ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h : full per ^^^ xc.1 = 0
    · have h1 : phiCls P per xc.1 = 0 := by unfold phiCls; rw [ite_eq_left h]
      rw [h1, mul_zero, zero_add, ← ih]
      dsimp only
      rw [ite_eq_left h]
    · have h1 : phiCls P per xc.1 = minQ P (popcount per (full per ^^^ xc.1)) (ymaxQ P (nShift per (full per ^^^ xc.1))) := by
        unfold phiCls; rw [ite_eq_right h]
      rw [h1, ← ih]
      dsimp only
      rw [ite_eq_right h, List.map_cons, List.sum_cons]

/-- The orbit sum of `lagBound` is the sum over all classes `k < l`. -/
theorem orbSum_eq_sum_classes {per : ℕ} (hper : 0 < per) (P : Par) (ps : List ℕ) (hg : GoodPrimes per ps)
    (hd : DistinctPrimes ps) :
    orbSum P (orbits per ps) = ∑ k ∈ range ps.prod, phiCls P per (exmaskL per ps 0 k) := by
  rw [orbSum_orbits, sum_exmaskL per _ ps hd 0]
  unfold foldOrbits
  rw [wsum_foldl hper (fun x hx => phiCls_rot hper P hx) ps hg [(0, 1)]
    (fun xc hxc => by rw [List.mem_singleton.mp hxc]; exact Nat.two_pow_pos per)]
  rw [wsum_cons, wsum_nil]
  push_cast
  ring

end Romanoff
