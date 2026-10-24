import Romanoff.SingSeries
import Romanoff.ETail
import Romanoff.FirstMoment
import Romanoff.LPFinite
import RCert.Params45

/-!
# M4 interface: shared definitions and the frozen statements of the remaining layers (as `Prop`s)

At `per = 120`, `ps = ellPrimes`, `l = ell`:
* `XU l N k = Σ_{a₁ ≠ a₂ ≤ L} X_k(a₁, a₂)` (`L = ⌊log₂ N⌋`), so `S2 = S1 + XU`;
* `WU L k = Σ_{a₁ ≠ a₂ ≤ L, a₁, a₂ mod 120 ∈ U_k} S'(2^{max} - 2^{min})`;
* `TK teff k = Σ_c n_k(c) teff(c)` (the evaluator's per-class cap is `8 κ TK`).

Each layer proves one `Prop` below (`theorem … : WUBound`, etc.), so its statement cannot drift:
(A) `WUBound`; (B) `XUESPBound`, `SumXUJTBound`; (C) `OrbSumLink`, `NcQLink`, `LagBoundSplit`, `DataFacts`.
-/

open Finset R45

namespace Romanoff

theorem distinctPrimes_ell : DistinctPrimes ellPrimes := by
  refine ⟨by decide, fun p hp => ?_⟩
  simp only [ellPrimes, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem goodPrimes_ell : GoodPrimes 120 ellPrimes := by
  intro p hp
  simp only [ellPrimes, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## Shared definitions -/

/-- `Σ_{a₁ ≠ a₂ ≤ ⌊log₂ N⌋} X_k(a₁, a₂)`. -/
def XU (l N k : ℕ) : ℕ := ∑ a1 ∈ Icc 1 (Nat.log 2 N), ∑ a2 ∈ (Icc 1 (Nat.log 2 N)).erase a1, X l N k a1 a2

/-- `W_k(L) = Σ_{a₁ ≠ a₂ ≤ L, a₁, a₂ mod 120 ∈ U_k} S'(2^{max} - 2^{min})`. -/
noncomputable def WU (L k : ℕ) : ℝ :=
  ∑ a1 ∈ Icc 1 L, ∑ a2 ∈ (Icc 1 L).erase a1,
    if a1 % 120 ∈ Uset 120 ellPrimes k ∧ a2 % 120 ∈ Uset 120 ellPrimes k then singP ellPrimes (hsh a1 a2) else 0

/-- `T_k = Σ_{c < 120} n_k(c) teff(c)`. -/
noncomputable def TK (teff : List ℚ) (k : ℕ) : ℝ :=
  ∑ c ∈ range 120, (nC 120 ellPrimes k c : ℝ) * ((teff.getD c 0 : ℚ) : ℝ)

/-! ## (A) The singular series per class -/

def WUBound : Prop :=
  ∀ teff : List ℚ, TBound teff → ∀ L k : ℕ,
    WU L k ≤ ((L : ℝ) / 120 + 1) * ((L : ℝ) / 120) * TK teff k +
      ((L : ℝ) / 120 + 1) * ((Uset 120 ellPrimes k).card : ℝ) ^ 2 * EL ell L

/-! ## (B) The pair sums at one `N` from the hypotheses -/

/-- Per class, from ESP (28) at `N`: the pairs with both exponents in `U_k` by (28) and `sing (l h) = P_l S'(h)`
(negative shifts by `X_comm`), the other pairs by `X ≤ |ps| = 9`. -/
def XUESPBound : Prop :=
  ∀ (N : ℕ) (ε : ℝ), 0 < ε →
    (∀ h : ℤ, 0 < h → h < N → ∀ k : ℕ, Nat.Coprime k ell →
      (pairCountMod N h k ell : ℝ) ≤
        (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * sing (ell * h.natAbs)) →
    ∀ k < ell, (XU ell N k : ℝ) ≤ 9 * (Nat.log 2 N : ℝ) ^ 2 +
      (8 + ε) * C0up * N / ((Nat.totient ell : ℝ) * Real.log N ^ 2) * Pl ellPrimes * WU (Nat.log 2 N) k

/-- Summed over the classes, from JT Prop. 2 at `N`: `Σ_k X_k(a₁, a₂) ≤ pairCount N h` and
`sing h = (∏_p 1/(p-2)) #{k : a₁, a₂ mod 120 ∈ U_k} S'(h)` (`sing_shift`). -/
def SumXUJTBound : Prop :=
  ∀ (N : ℕ) (ε : ℝ), 0 < ε →
    (∀ h : ℤ, 0 < h → h < N →
      (pairCount N h : ℝ) ≤ (67814 / 10000 + ε) * C0up * N / Real.log N ^ 2 * sing h.natAbs) →
    ∑ k ∈ range ell, (XU ell N k : ℝ) ≤
      (67814 / 10000 + ε) * C0up * N / Real.log N ^ 2 * (∏ p ∈ ellPrimes.toFinset, 1 / ((p : ℝ) - 2)) *
        ∑ k ∈ range ell, WU (Nat.log 2 N) k

/-! ## (C) The evaluator against the classes, and the data -/

/-- The orbit sum of the evaluator is the sum of the per-class minima over the classes with `U_k ≠ ∅`. -/
def OrbSumLink : Prop :=
  ∀ P : Par, P.teff.length = 120 →
    ((orbSum P (orbits 120 ellPrimes) : ℚ) : ℝ) =
      ∑ k ∈ (range ell).filter (fun k => (Uset 120 ellPrimes k).Nonempty),
        ((minQ P (Uset 120 ellPrimes k).card
          (P.cap * P.kap * ∑ c ∈ range 120, (nC 120 ellPrimes k c : ℚ) * P.teff.getD c 0) : ℚ) : ℝ)

/-- `N(c) = (1/l) Σ_{k < l} n_k(c)`. -/
def NcQLink : Prop :=
  ∀ (P : Par) (c : ℕ), c < 120 →
    ncQ P (orbits 120 ellPrimes) c = (1 / (P.ell : ℚ)) * ∑ k ∈ range ell, (nC 120 ellPrimes k c : ℚ)

/-- `lagBound = orbit sum - μ C1 κ Σ_c N(c) teff(c)`. -/
def LagBoundSplit : Prop :=
  ∀ (P : Par) (os : List Orb), P.teff.length = P.per →
    lagBound P os = orbSum P os - P.mu * P.c1 * P.kap * ∑ c ∈ range P.per, ncQ P os c * P.teff.getD c 0

/-- The evaluator's constants against the statement's. -/
def DataFacts : Prop :=
  R45.P45.ellN = ell ∧ R45.P45.philN = Nat.totient ell ∧ ((R45.P45.pell : ℚ) : ℝ) = Pl ellPrimes ∧
    ((R45.D45.C0up : ℚ) : ℝ) = C0up ∧ ((R45.D45.log2lo : ℚ) : ℝ) = 693147180559945309 / 10 ^ 18 ∧
    ((R45.D45.log2hi : ℚ) : ℝ) = 693147180559945310 / 10 ^ 18

end Romanoff
