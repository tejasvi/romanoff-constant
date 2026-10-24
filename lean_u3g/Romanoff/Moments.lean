import Romanoff.Defs
import Romanoff.Pintz

/-!
# Moments of the representation function in residue classes (exact, for each `N`)

`rep n = #{a ≥ 1 : 2^a < n, n - 2^a prime}`; `cls l N k = {1 ≤ n ≤ N : n ≡ k (mod l)}`; `S1 = Σ rep`, `S2 = Σ rep²`
over a class.  `count N = Σ_k #{n ∈ cls l N k : rep n > 0}`, Pintz per class, and `S2 = S1 + Σ_{a₁ ≠ a₂} X(a₁, a₂)`
with `X(a₁, a₂) = #{n ∈ cls : a₁, a₂ both represent n}` (symmetric in `a₁, a₂`).  The modulus `l` is a parameter here,
so that no proof can unfold the 11-digit `ell`.
-/

open Finset

namespace Romanoff

/-- The exponents `a ≥ 1` with `2^a < n` and `n - 2^a` prime. -/
def repSet (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter fun a => 2 ^ a < n ∧ (n - 2 ^ a).Prime

/-- `r(n) = #{(p, a) : n = p + 2^a, p prime, a ≥ 1}`. -/
def rep (n : ℕ) : ℕ := (repSet n).card

theorem isRomanoff_iff_rep_pos (n : ℕ) : IsRomanoff n ↔ 0 < rep n := by
  rw [rep, Finset.card_pos, isRomanoff_iff]
  constructor
  · rintro ⟨a, ha, h1, h2⟩; exact ⟨a, mem_filter.mpr ⟨ha, h1, h2⟩⟩
  · rintro ⟨a, ha⟩; exact ⟨a, (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩

/-- The class `{1 ≤ n ≤ N : n ≡ k (mod l)}` (`k < l`). -/
def cls (l N k : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter fun n => n % l = k

theorem count_eq_sum_nat (l N : ℕ) (hl : 0 < l) :
    count N = ∑ k ∈ range l, ((cls l N k).filter fun n => 0 < rep n).card := by
  unfold count cls
  rw [card_eq_sum_card_fiberwise (f := fun n => n % l) (t := range l)
    (fun n _ => mem_range.mpr (Nat.mod_lt _ hl))]
  refine sum_congr rfl fun k _ => ?_
  simp only [filter_filter]
  exact congrArg card (filter_congr fun n _ => by rw [isRomanoff_iff_rep_pos]; tauto)

theorem count_eq_sum (l N : ℕ) (hl : 0 < l) :
    (count N : ℝ) = ∑ k ∈ range l, (((cls l N k).filter fun n => 0 < rep n).card : ℝ) := by
  rw [count_eq_sum_nat l N hl, Nat.cast_sum]

/-- `S1(k) = Σ_{n ∈ cls} r(n)`. -/
def S1 (l N k : ℕ) : ℕ := ∑ n ∈ cls l N k, rep n

/-- `S2(k) = Σ_{n ∈ cls} r(n)²`. -/
def S2 (l N k : ℕ) : ℕ := ∑ n ∈ cls l N k, rep n ^ 2

/-- Pintz in one class: `φ(D) S1 ≤ #{n ∈ cls : r(n) > 0}` whenever `S2 ≤ D S1`, `D ≥ 1`. -/
theorem class_count_ge (l N k : ℕ) {D : ℝ} (hD : 1 ≤ D) (h2 : (S2 l N k : ℝ) ≤ D * S1 l N k) :
    phi D * S1 l N k ≤ (((cls l N k).filter fun n => 0 < rep n).card : ℝ) := by
  have := pintz_phi (cls l N k) rep hD (by unfold S1 S2 at h2; push_cast at h2; exact h2)
  unfold S1; push_cast; exact this

/-- `X(a₁, a₂) = #{n ∈ cls l N k : a₁ and a₂ both represent n}`. -/
def X (l N k a1 a2 : ℕ) : ℕ := ((cls l N k).filter fun n => a1 ∈ repSet n ∧ a2 ∈ repSet n).card

theorem X_comm (l N k a1 a2 : ℕ) : X l N k a1 a2 = X l N k a2 a1 := by
  unfold X; congr 1; ext n; simp only [mem_filter]; tauto

theorem repSet_subset_log (N : ℕ) {n : ℕ} (hn : n ≤ N) : repSet n ⊆ Icc 1 (Nat.log 2 N) := by
  intro a ha
  rw [repSet, mem_filter, mem_Icc] at ha
  refine mem_Icc.mpr ⟨ha.1.1, ?_⟩
  have h1 : 2 ^ a ≤ N := by omega
  exact Nat.le_log_of_pow_le (by norm_num) h1

/-- `r(n)² = r(n) + #{(a₁, a₂) ∈ repSet², a₁ ≠ a₂}`. -/
theorem rep_sq (n L : ℕ) (hL : repSet n ⊆ Icc 1 L) :
    rep n ^ 2 = rep n + ∑ a1 ∈ Icc 1 L, ∑ a2 ∈ (Icc 1 L).erase a1,
      (if a1 ∈ repSet n ∧ a2 ∈ repSet n then 1 else 0) := by
  have h1 : ∀ a1 ∈ Icc 1 L, ∑ a2 ∈ (Icc 1 L).erase a1, (if a1 ∈ repSet n ∧ a2 ∈ repSet n then 1 else 0) =
      if a1 ∈ repSet n then rep n - 1 else 0 := by
    intro a1 _
    split_ifs with ha1
    · rw [sum_boole, rep]
      have : ((Icc 1 L).erase a1).filter (fun a2 => a1 ∈ repSet n ∧ a2 ∈ repSet n) = (repSet n).erase a1 := by
        ext a2
        simp only [mem_filter, mem_erase, ha1, true_and]
        constructor
        · rintro ⟨⟨hne, _⟩, h⟩; exact ⟨hne, h⟩
        · rintro ⟨hne, h⟩; exact ⟨⟨hne, hL h⟩, h⟩
      rw [this, card_erase_of_mem ha1]; simp
    · exact sum_eq_zero fun a2 _ => by simp [ha1]
  rw [sum_congr rfl h1, ← sum_filter, sum_const]
  have : (Icc 1 L).filter (fun a1 => a1 ∈ repSet n) = repSet n := by
    ext a; simp only [mem_filter]; constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hL h, h⟩
  rw [this, smul_eq_mul, ← rep]
  rcases Nat.eq_zero_or_pos (rep n) with h | h
  · rw [h]; simp
  · have : rep n * (rep n - 1) = rep n ^ 2 - rep n := by
      rw [Nat.mul_sub, mul_one, sq]
    rw [this]; have : rep n ≤ rep n ^ 2 := by nlinarith
    omega

/-- `S2 = S1 + Σ_{a₁ ≠ a₂ ≤ L} X(a₁, a₂)`, `L = ⌊log₂ N⌋`. -/
theorem S2_eq (l N k : ℕ) :
    S2 l N k = S1 l N k + ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1, X l N k a1 a2 := by
  unfold S2 S1 X
  have hL : ∀ n ∈ cls l N k, repSet n ⊆ Icc 1 (Nat.log 2 N) := fun n hn =>
    repSet_subset_log N (mem_Icc.mp (mem_filter.mp hn).1).2
  rw [sum_congr rfl fun n hn => rep_sq n (Nat.log 2 N) (hL n hn), sum_add_distrib]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun a1 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun a2 _ => ?_
  rw [sum_boole, Nat.cast_id]

/-- `S1 = Σ_{a ≤ L} #{n ∈ cls : a represents n}`. -/
theorem S1_eq (l N k : ℕ) :
    S1 l N k = ∑ a ∈ Icc 1 (Nat.log 2 N), ((cls l N k).filter fun n => a ∈ repSet n).card := by
  unfold S1 rep
  have hL : ∀ n ∈ cls l N k, repSet n ⊆ Icc 1 (Nat.log 2 N) := fun n hn =>
    repSet_subset_log N (mem_Icc.mp (mem_filter.mp hn).1).2
  have : ∀ n ∈ cls l N k, (repSet n).card = ∑ a ∈ Icc 1 (Nat.log 2 N), if a ∈ repSet n then 1 else 0 := by
    intro n hn
    rw [sum_boole, Nat.cast_id]
    congr 1; ext a; simp only [mem_filter]
    exact ⟨fun h => ⟨hL n hn h, h⟩, fun h => h.2⟩
  rw [sum_congr rfl this, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_boole, Nat.cast_id]

/-- Summing `X` over all classes gives the pair count without congruence condition. -/
theorem sum_X (l N a1 a2 : ℕ) (hl : 0 < l) :
    ∑ k ∈ range l, X l N k a1 a2 = ((Icc 1 N).filter fun n => a1 ∈ repSet n ∧ a2 ∈ repSet n).card := by
  unfold X cls
  rw [card_eq_sum_card_fiberwise (f := fun n => n % l) (t := range l)
    (fun n _ => mem_range.mpr (Nat.mod_lt _ hl))]
  refine sum_congr rfl fun k _ => ?_
  simp only [filter_filter]
  exact congrArg card (filter_congr fun n _ => by tauto)

end Romanoff
