import Romanoff.U3.Minorant
import Romanoff.E.Spec
import RCert.E.U3E

/-!
# U3e: the tables at period 3960 (alpha-form tail, divisor form) and the linearity of `Σ_c n(c) teff(c)`

* `divE` lists the divisors of 3960 (`mem_divE`, `divE_dvd`, `divisors3960_eq'`).
* `dotNQ_teffA_tabB`: for `tab = tabB B` (divisor form), `Σ_c n(c) (tab(c) + Σ_{g ∣ c} g α_g) = Σ_g (B_g + g α_g) N_g`
  with `N_g = Σ_{c, g ∣ c} n(c)` (the divisor lemma).
-/

open Finset R45 R45.U3E

namespace Romanoff.E

theorem divE_nodup : R45.M3E.divE.Nodup := by decide

theorem divE_complete : (List.range 3961).all
    (fun g => (g == 0) || (3960 % g != 0) || R45.M3E.divE.contains g) = true := by
  decide +kernel

theorem mem_divE (g : ℕ) (hg : g ∣ 3960) : g ∈ R45.M3E.divE := by
  have hle : g ≤ 3960 := Nat.le_of_dvd (by norm_num) hg
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have h := List.all_eq_true.mp divE_complete g (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with (h0 | h1) | h2
  · omega
  · exact absurd (Nat.mod_eq_zero_of_dvd hg) h1
  · simpa using h2

theorem divE_sound : R45.M3E.divE.all (fun g => 3960 % g == 0) = true := by decide

theorem divE_dvd {g : ℕ} (hg : g ∈ R45.M3E.divE) : g ∣ 3960 := by
  have := List.all_eq_true.mp divE_sound g hg
  simp only [beq_iff_eq] at this
  exact Nat.dvd_of_mod_eq_zero this

theorem divE_pos {g : ℕ} (hg : g ∈ R45.M3E.divE) : 0 < g := Nat.pos_of_dvd_of_pos (divE_dvd hg) (by norm_num)

theorem divisors3960_eq' : Nat.divisors 3960 = R45.M3E.divE.toFinset := by
  ext g
  simp only [Nat.mem_divisors, List.mem_toFinset]
  constructor
  · rintro ⟨h, -⟩; exact mem_divE g h
  · intro h; exact ⟨divE_dvd h, by norm_num⟩

/-! ## The tables -/

theorem teffA_length (tab : List ℚ) (α : ℕ → ℚ) : (teffA tab α).length = 3960 := by
  unfold teffA; simp

theorem teffA_getD (tab : List ℚ) (α : ℕ → ℚ) {c : ℕ} (hc : c < 3960) :
    (teffA tab α).getD c 0 = tab.getD c 0 + tailA α c := by
  unfold teffA
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

theorem tailA_eq (α : ℕ → ℚ) (c : ℕ) :
    tailA α c = (R45.M3E.divE.map fun g => if c % g = 0 then (g : ℚ) * α g else 0).sum := by
  unfold tailA
  rw [filter_map_sum]
  simp only [beq_iff_eq]

theorem tabB_length (B : ℕ → ℚ) : (tabB B).length = 3960 := by
  unfold tabB; simp

theorem tabB_getD (B : ℕ → ℚ) {c : ℕ} (hc : c < 3960) :
    (tabB B).getD c 0 = (R45.M3E.divE.map fun g => if c % g = 0 then B g else 0).sum := by
  unfold tabB
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  show ((R45.M3E.divE.filter fun g => c % g == 0).map B).sum = _
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

theorem ngOf_eq (n : List ℕ) (hn : n.length = 3960) (g : ℕ) :
    ((ngOf n g : ℕ) : ℚ) = ∑ c ∈ range 3960, if c % g = 0 then ((n.getD c 0 : ℕ) : ℚ) else 0 := by
  unfold ngOf
  rw [ngAux_eq g n 0, hn]
  simp only [Nat.zero_add]

/-- The divisor lemma: `Σ_c n(c) (tabB B (c) + Σ_{g ∣ c} g α_g) = Σ_{g ∈ divE} (B_g + g α_g) N_g`. -/
theorem dotNQ_teffA_tabB (n : List ℕ) (hn : n.length = 3960) (B α : ℕ → ℚ) :
    dotNQ n (teffA (tabB B) α) = (R45.M3E.divE.map fun g => (B g + (g : ℚ) * α g) * (ngOf n g : ℚ)).sum := by
  unfold dotNQ
  rw [dotNQ_eq n _ 0 (by rw [hn, teffA_length]), zero_add, hn]
  have h1 : ∀ c ∈ range 3960, ((n.getD c 0 : ℕ) : ℚ) * (teffA (tabB B) α).getD c 0 =
      ((n.getD c 0 : ℕ) : ℚ) *
        (R45.M3E.divE.map fun g => if c % g = 0 then B g + (g : ℚ) * α g else 0).sum := by
    intro c hc
    have hc' := mem_range.mp hc
    rw [teffA_getD _ α hc', tabB_getD B hc', tailA_eq, ← List.sum_map_add]
    congr 2
    apply List.map_congr_left
    intro g _
    split_ifs <;> ring
  rw [sum_congr rfl h1, sum_mul_list_swap R45.M3E.divE (fun c => ((n.getD c 0 : ℕ) : ℚ))
    (fun g c => if c % g = 0 then B g + (g : ℚ) * α g else 0)]
  apply congrArg
  apply List.map_congr_left
  intro g _
  rw [ngOf_eq n hn, mul_sum]
  apply sum_congr rfl
  intro c _
  split_ifs <;> ring

end Romanoff.E
