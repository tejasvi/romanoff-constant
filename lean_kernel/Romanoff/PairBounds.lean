import Romanoff.Sing

/-!
# The pair counts `X_k(a₁, a₂)` against the pair-counting functions of the hypotheses

For `a₁ < a₂` and `h = 2^{a₂} - 2^{a₁}` (so `0 < h < N` when `a₂ ≤ ⌊log₂ N⌋`), `n ↦ p₂ = n - 2^{a₂}` maps the integers counted
by `X_k(a₁, a₂)` injectively to the primes `p₂ ≤ N` with `p₂ + h ≤ N` prime and `p₂ ≡ k - 2^{a₂} (mod l)`:
* `X_k(a₁, a₂) ≤ pairCountMod N h (k - 2^{a₂} mod l) l` (ESP (28) applies when `a₂ mod per ∈ U_k`);
* `Σ_k X_k(a₁, a₂) ≤ pairCount N h` (JT Prop. 2);
* if `a mod per ∉ U_k` for `a ∈ {a₁, a₂}`, then `n - 2^a` is a prime dividing `l`, so `X_k(a₁, a₂) ≤ |ps|`.
-/

open Finset

namespace Romanoff

/-- The residue of `k - 2^a` modulo `l`. -/
def resid (l k a : ℕ) : ℕ := (k + l - 2 ^ a % l) % l

theorem card_pairs_le_pairCountMod {S : Finset ℕ} {N a1 a2 kk l : ℕ} (h12 : a1 < a2) (hS : ∀ n ∈ S, n ≤ N)
    (hres : ∀ n ∈ S, a2 ∈ repSet n → (n - 2 ^ a2) % l = kk % l) :
    (S.filter fun n => a1 ∈ repSet n ∧ a2 ∈ repSet n).card ≤
      pairCountMod N ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) kk l := by
  unfold pairCountMod
  have hpow : 2 ^ a1 < 2 ^ a2 := Nat.pow_lt_pow_right (by norm_num) h12
  refine card_le_card_of_injOn (fun n => n - 2 ^ a2) ?_ ?_
  · intro n hn
    obtain ⟨hnS, h1, h2⟩ := mem_filter.mp hn
    have hnN := hS n hnS
    rw [repSet, mem_filter] at h1 h2
    have hsum : n - 2 ^ a2 + (2 ^ a2 - 2 ^ a1) = n - 2 ^ a1 := by omega
    have hz : ((n - 2 ^ a2 : ℕ) : ℤ) + ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) = ((n - 2 ^ a1 : ℕ) : ℤ) := by
      rw [← hsum]; push_cast; ring
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (le_trans (Nat.sub_le _ _) hnN)), h2.2.2,
      hres n hnS (by rw [repSet, mem_filter]; exact h2), ?_, ?_, ?_⟩
    · rw [hz]; positivity
    · rw [hz, Int.toNat_natCast]; exact le_trans (Nat.sub_le _ _) hnN
    · rw [hz, Int.toNat_natCast]; exact h1.2.2
  · intro n hn m hm hnm
    have h2n := (mem_filter.mp (mem_filter.mp hn).2.2).2.1
    have h2m := (mem_filter.mp (mem_filter.mp hm).2.2).2.1
    simp only at hnm
    omega

/-- `(n - 2^a) ≡ k - 2^a (mod l)` for `n ≡ k`. -/
theorem sub_mod_resid {l k n a : ℕ} (hl : 0 < l) (hk : k < l) (hn : n % l = k) (ha : 2 ^ a ≤ n) :
    (n - 2 ^ a) % l = resid l k a % l := by
  unfold resid
  rw [Nat.mod_mod]
  set r := 2 ^ a % l with hr
  have hrl : r < l := Nat.mod_lt _ hl
  have h1 : k + l - r + r ≡ n - 2 ^ a + r [MOD l] := by
    rw [Nat.sub_add_cancel (by omega)]
    have e1 : k + l ≡ k [MOD l] := Nat.add_modEq_right
    have e2 : k ≡ n [MOD l] := by unfold Nat.ModEq; rw [hn, Nat.mod_eq_of_lt hk]
    have e4 : n - 2 ^ a + 2 ^ a ≡ n - 2 ^ a + r [MOD l] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
    rw [Nat.sub_add_cancel ha] at e4
    exact e1.trans (e2.trans e4)
  exact (Nat.ModEq.add_right_cancel' r h1).symm

theorem coprime_list_prod {k : ℕ} : ∀ {ps : List ℕ}, (∀ p ∈ ps, p.Prime ∧ ¬ p ∣ k) → Nat.Coprime k ps.prod
  | [], _ => by simp
  | p :: ps, h => by
    rw [List.prod_cons]
    exact Nat.Coprime.mul_right ((Nat.coprime_comm.mp ((h p (by simp)).1.coprime_iff_not_dvd.mpr (h p (by simp)).2)))
      (coprime_list_prod fun q hq => h q (by simp [hq]))

/-- The residue `k - 2^a` is a unit mod `l` when `a mod per ∈ U_k`. -/
theorem resid_coprime {per : ℕ} (hper : 0 < per) {ps : List ℕ} (hg : GoodPrimes per ps) (hd : DistinctPrimes ps)
    {k a : ℕ} (ha : a % per ∈ Uset per ps k) : Nat.Coprime (resid ps.prod k a) ps.prod := by
  have hl : 0 < ps.prod := prod_pos_of_primes ps hd.2
  rw [mem_Uset_mod hper hg] at ha
  refine coprime_list_prod fun p hp => ⟨hd.2 p hp, fun hdvd => ?_⟩
  have hpl : p ∣ ps.prod := dvd_prod_of_mem hp
  unfold resid at hdvd
  rw [Nat.dvd_mod_iff hpl] at hdvd
  set r := 2 ^ a % ps.prod
  have hrl : r < ps.prod := Nat.mod_lt _ hl
  -- `k + l - r ≡ 0 (mod p)`, so `k ≡ r ≡ 2^a (mod p)`
  have h0 : k + ps.prod - r ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
  have h1 : k + ps.prod ≡ r [MOD p] := by
    have := Nat.ModEq.add_right r h0
    rwa [Nat.sub_add_cancel (by omega), zero_add] at this
  have h2 : k ≡ r [MOD p] := by
    have e : k + ps.prod ≡ k [MOD p] := by
      have := Nat.ModEq.add_left k ((Nat.modEq_zero_iff_dvd).mpr hpl)
      rwa [add_zero] at this
    exact e.symm.trans h1
  have h3 : r ≡ 2 ^ a [MOD p] := Nat.mod_mod_of_dvd _ hpl
  exact ha p hp (h2.trans h3).symm

/-- ESP form: `X_k(a₁, a₂) ≤ pairCountMod N h (k - 2^{a₂} mod l) l`. -/
theorem X_le_pairCountMod {l N k a1 a2 : ℕ} (hl : 0 < l) (hk : k < l) (h12 : a1 < a2) :
    X l N k a1 a2 ≤ pairCountMod N ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) (resid l k a2) l := by
  unfold X
  refine card_pairs_le_pairCountMod h12 (fun n hn => (mem_Icc.mp (mem_filter.mp hn).1).2) ?_
  intro n hn h2
  have hnk := (mem_filter.mp hn).2
  have hlt := (mem_filter.mp h2).2.1
  exact sub_mod_resid hl hk hnk hlt.le

/-- JT form: `Σ_k X_k(a₁, a₂) ≤ pairCount N h`. -/
theorem sum_X_le_pairCount {l N a1 a2 : ℕ} (hl : 0 < l) (h12 : a1 < a2) :
    ∑ k ∈ range l, X l N k a1 a2 ≤ pairCount N ((2 ^ a2 - 2 ^ a1 : ℕ) : ℤ) := by
  rw [sum_X l N a1 a2 hl]
  unfold pairCount
  exact card_pairs_le_pairCountMod h12 (fun n hn => (mem_Icc.mp hn).2) fun n _ _ => by simp only [Nat.mod_one]

/-- If an exponent of the pair is not in `U_k`, at most `|ps|` integers are counted. -/
theorem X_le_length_of_not_mem {per : ℕ} (hper : 0 < per) {ps : List ℕ} (hg : GoodPrimes per ps)
    (hd : DistinctPrimes ps) {N k a1 a2 : ℕ} (ha : a1 % per ∉ Uset per ps k ∨ a2 % per ∉ Uset per ps k) :
    X ps.prod N k a1 a2 ≤ ps.length := by
  have key : ∀ a, a % per ∉ Uset per ps k → ∀ n ∈ cls ps.prod N k, a ∈ repSet n → n - 2 ^ a ∈ ps.toFinset := by
    intro a ha n hn hrep
    rw [mem_Uset_mod hper hg] at ha
    obtain ⟨p, hp, hpe⟩ : ∃ p ∈ ps, 2 ^ a % p = k % p := by
      by_contra hcon; exact ha fun p hp he => hcon ⟨p, hp, he⟩
    have hnk : n % ps.prod = k := (mem_filter.mp hn).2
    obtain ⟨_, hlt, hprime⟩ := mem_filter.mp hrep
    have hnp : n % p = k % p := by rw [← hnk, Nat.mod_mod_of_dvd _ (dvd_prod_of_mem hp)]
    have hdvd : p ∣ n - 2 ^ a := (Nat.modEq_iff_dvd' hlt.le).mp (by unfold Nat.ModEq; rw [hpe, hnp])
    rw [← (Nat.prime_dvd_prime_iff_eq (hd.2 p hp) hprime).mp hdvd]
    exact List.mem_toFinset.mpr hp
  unfold X
  rcases ha with ha | ha
  · refine (card_le_card_of_injOn (fun n => n - 2 ^ a1) (fun n hn => ?_) ?_).trans (List.toFinset_card_le ps)
    · exact key a1 ha n (mem_filter.mp hn).1 (mem_filter.mp hn).2.1
    · intro n hn m hm hnm
      have h1 := (mem_filter.mp (mem_filter.mp hn).2.1).2.1
      have h2 := (mem_filter.mp (mem_filter.mp hm).2.1).2.1
      simp only at hnm; omega
  · refine (card_le_card_of_injOn (fun n => n - 2 ^ a2) (fun n hn => ?_) ?_).trans (List.toFinset_card_le ps)
    · exact key a2 ha n (mem_filter.mp hn).1 (mem_filter.mp hn).2.2
    · intro n hn m hm hnm
      have h1 := (mem_filter.mp (mem_filter.mp hn).2.2).2.1
      have h2 := (mem_filter.mp (mem_filter.mp hm).2.2).2.1
      simp only at hnm; omega

end Romanoff
