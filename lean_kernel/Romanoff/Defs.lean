import Mathlib

/-!
# Romanov's constant (Tao page 45a): definitions, named hypotheses and the target statements

`IsRomanoff n`: `n = p + 2^a` with `p` prime and `a ≥ 1`.  `dens N = #{1 ≤ n ≤ N : IsRomanoff n} / N`.
Targets: `0.109406 ≤ liminf dens` from (I1) ESP (28), (I3) PNT mod `l`, (I5) Platt–Trudgian's `R0 < 1.93656`
(unconditional), and `0.117953 ≤ liminf dens` with (I2) Johnston–Trudgian Prop. 2 in addition (conditional on
Lichtman, arXiv:2309.08522, Theorems 1.2 and 1.7).  Pintz's inequality (I4) is proved, not assumed.
-/

open Filter Finset

namespace Romanoff

/-! ## The set and its density -/

/-- `n = p + 2^a` with `p` prime and `a ≥ 1`. -/
def IsRomanoff (n : ℕ) : Prop := ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ n = p + 2 ^ a

theorem isRomanoff_iff (n : ℕ) :
    IsRomanoff n ↔ ∃ a ∈ Finset.Icc 1 n, 2 ^ a < n ∧ (n - 2 ^ a).Prime := by
  constructor
  · rintro ⟨p, a, hp, ha, rfl⟩
    have h2 := hp.two_le
    have hlt : a < 2 ^ a := Nat.lt_two_pow_self
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha, by omega⟩, by omega, ?_⟩
    rwa [Nat.add_sub_cancel]
  · rintro ⟨a, ha, hlt, hp⟩
    exact ⟨n - 2 ^ a, a, hp, (Finset.mem_Icc.mp ha).1, by omega⟩

instance : DecidablePred IsRomanoff := fun n => decidable_of_iff _ (isRomanoff_iff n).symm

/-- `#{1 ≤ n ≤ N : n = p + 2^a}`. -/
def count (N : ℕ) : ℕ := ((Finset.Icc 1 N).filter IsRomanoff).card

/-- `N⁻¹ #{1 ≤ n ≤ N : n = p + 2^a}` (`= 0` at `N = 0`). -/
noncomputable def dens (N : ℕ) : ℝ := (count N : ℝ) / N

theorem dens_nonneg (N : ℕ) : 0 ≤ dens N := by unfold dens; positivity

theorem dens_le_one (N : ℕ) : dens N ≤ 1 := by
  unfold dens count
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    have := Finset.card_filter_le (Finset.Icc 1 N) IsRomanoff
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this

/-- The lower density is at least `c` (junk-free form). -/
def LowerDensityGe (c : ℝ) : Prop := ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, c - ε ≤ dens N

theorem dens_isBoundedUnder_le : IsBoundedUnder (· ≤ ·) atTop dens :=
  isBoundedUnder_of ⟨1, fun N => dens_le_one N⟩

theorem dens_isBoundedUnder_ge : IsBoundedUnder (· ≥ ·) atTop dens :=
  isBoundedUnder_of ⟨0, fun N => dens_nonneg N⟩

/-- The two forms agree (`0 ≤ dens ≤ 1`, so `liminf` is the genuine one). -/
theorem lowerDensityGe_iff (c : ℝ) : LowerDensityGe c ↔ c ≤ liminf dens atTop := by
  constructor
  · intro h
    refine le_of_forall_sub_le (fun ε hε => ?_)
    exact le_liminf_of_le dens_isBoundedUnder_le.isCoboundedUnder_ge (h ε hε)
  · intro h ε hε
    have hlt : c - ε < liminf dens atTop := by linarith
    exact eventually_lt_of_lt_liminf hlt dens_isBoundedUnder_ge |>.mono fun N hN => hN.le

/-! ## The modulus, the constants and the counting functions -/

/-- The primes of the modulus `l` (all with `ord_p(2) | 120`). -/
def ellPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 31, 41, 241]

/-- `l = 3·5·7·11·13·17·31·41·241 = 78187414305`. -/
def ell : ℕ := ellPrimes.prod

/-- An upper bound for the twin prime constant `C0 = ∏_{p > 2} (1 - (p-1)^{-2}) = 0.6601618158468695739…`. -/
noncomputable def C0up : ℝ := 66016181584686958 / 10 ^ 17

/-- `∏_{p | n, p > 2} (p-1)/(p-2)`. -/
noncomputable def sing (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / (p - 2)

/-- `#{p₂ ≤ N prime : p₂ ≡ k (mod l), p₂ + h prime, p₂ + h ≤ N}`: the pairs `(p₁, p₂)` of primes `≤ N` with
`p₁ - p₂ = h` and `p₂ ≡ k (mod l)`. -/
def pairCountMod (N : ℕ) (h : ℤ) (k l : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p₂ => p₂.Prime ∧ p₂ % l = k % l ∧
    0 ≤ (p₂ : ℤ) + h ∧ ((p₂ : ℤ) + h).toNat ≤ N ∧ ((p₂ : ℤ) + h).toNat.Prime).card

/-- `#{(p₁, p₂) primes ≤ N : p₁ - p₂ = h}`. -/
def pairCount (N : ℕ) (h : ℤ) : ℕ := pairCountMod N h 0 1

/-- `π(N; l, a) = #{p ≤ N prime : p ≡ a (mod l)}`. -/
def primeCountMod (N l a : ℕ) : ℕ := ((Finset.range (N + 1)).filter fun p => p.Prime ∧ p % l = a % l).card

/-- `f(m) = ∏_{p | m} 1/(p-2)`. -/
noncomputable def fm (m : ℕ) : ℝ := ∏ p ∈ m.primeFactors, 1 / ((p : ℝ) - 2)

/-! ## Named hypotheses (the analytic inputs) -/

/-- (I1) Elsholtz–Schlage-Puchta, Math. Z. 288 (2018), eq. (28) (Selberg's sieve with Bombieri–Vinogradov, the
maximum over residues inside the sum), for the fixed modulus `l`, with `C0` replaced by `C0up ≥ C0`: uniformly in
`0 < h < N` and in `k` coprime to `l` (JT §4.2 quote "all h < N"; P19 eq. (ESP)).  Negative shifts are handled in the
proof by the symmetry of the pair counts. -/
def ESP28 (l : ℕ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, 0 < h → h < N → ∀ k : ℕ, Nat.Coprime k l →
    (pairCountMod N h k l : ℝ) ≤
      (8 + ε) * C0up * N / ((Nat.totient l : ℝ) * Real.log N ^ 2) * sing (l * h.natAbs)

/-- (I2) Johnston–Trudgian, arXiv:2605.17825, Prop. 2, from Lichtman, arXiv:2309.08522, Theorems 1.2 and 1.7
(residue-uniform level of distribution): uniformly in `0 < h < N`, with `C0` replaced by `C0up ≥ C0`. -/
def JTProp2 : Prop :=
  ∀ ε > (0 : ℝ), ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ h : ℤ, 0 < h → h < N →
    (pairCount N h : ℝ) ≤ (67814 / 10000 + ε) * C0up * N / Real.log N ^ 2 * sing h.natAbs

/-- (I3) The prime number theorem in progressions to the fixed modulus `l`. -/
def PNTAP (l : ℕ) : Prop :=
  ∀ a : ℕ, Nat.Coprime a l →
    Tendsto (fun N : ℕ => (primeCountMod N l a : ℝ) * Nat.totient l * Real.log N / N) atTop (nhds 1)

/-- (I5) Platt–Trudgian, J. Number Theory 153 (2015), p. 55 (from Pintz 2006, Lemma 2'', and Wrench's bound for
`C0`), quoted by Johnston–Trudgian (17): `R0 = Σ_{m odd squarefree} f(m)/ord_m(2) < 1.93656`, as BOUNDED PARTIAL SUMS
(summability and the vanishing of the tails are what the proof uses; a `tsum` statement would be true by junk value
if the series diverged). -/
def R0Bound : Prop :=
  ∀ S : Finset ℕ, (∀ m ∈ S, Odd m ∧ Squarefree m) →
    ∑ m ∈ S, fm m / (orderOf (2 : ZMod m) : ℝ) ≤ 193656 / 100000

/-! ## Targets -/

/-- U2 (unconditional): `0.109406 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
def U2Statement : Prop := (109406 / 1000000 : ℝ) ≤ liminf dens atTop

/-- v3 (conditional on JT Prop. 2): `0.117953 ≤ liminf N⁻¹ #{n ≤ N : n = p + 2^a}`. -/
def V3Statement : Prop := (117953 / 1000000 : ℝ) ≤ liminf dens atTop

end Romanoff
