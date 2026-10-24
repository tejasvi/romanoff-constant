import Romanoff.G.S2.Value

/-!
# U3g/V4g stage 2: periodic extension of masks (120 → 360 → 27720)

`repB p n x` is the `n`-bit mask with bit `e` equal to bit `e mod p` of `x`.
* `maskP_rep`: for `2^p ≡ 1 (mod q)`, `maskP n q r = repB p n (maskP p q r)`;
* `repB_or`, `repB_trans`, `repB_rot` (120 → 27720);
* `tupleSum_lift`: the tuple sums over primes with `2^p ≡ 1` commute with `repB p n`;
* `wsum_tupleSum`: the BASE fold at any period is the tuple sum of a rotation-invariant function.
-/

open Finset R45 R45.EVG

namespace Romanoff.G.S2

theorem repB_lt (p n x : ℕ) : repB p n x < 2 ^ n :=
  lt_two_pow_of_testBit fun i hi => by
    rw [repB_testBit] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.1

theorem repB_or (p n a b : ℕ) : repB p n (a ||| b) = repB p n a ||| repB p n b := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [Nat.testBit_or, repB_testBit, repB_testBit, repB_testBit, Nat.testBit_or]
  cases decide (e < n) <;> simp

theorem repB_zero (p n : ℕ) : repB p n 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [repB_testBit]
  simp

theorem repB_trans {p p' n : ℕ} (hp : p ∣ p') (hp' : 0 < p') (x : ℕ) : repB p' n (repB p p' x) = repB p n x := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [repB_testBit, repB_testBit, repB_testBit, Nat.mod_mod_of_dvd _ hp]
  simp [Nat.mod_lt _ hp']

theorem maskP_rep {n p q r : ℕ} (hp : 0 < p) (hq : 1 < q) (h2 : 2 ^ p % q = 1) :
    maskP n q r = repB p n (maskP p q r) := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [maskP_testBit, repB_testBit, maskP_testBit, pow_mod_period hq h2 e]
  simp [Nat.mod_lt _ hp]

theorem repB_rot {x : ℕ} (hx : x < 2 ^ 120) : repB 120 27720 (rot1 120 x) = rot1 27720 (repB 120 27720 x) := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [repB_testBit, rot1_testBit (by norm_num) hx, rot1_testBit (by norm_num) (repB_lt _ _ _), repB_testBit]
  have h1 : (e % 120 + 120 - 1) % 120 = (e + 27720 - 1) % 27720 % 120 := by omega
  by_cases he : e < 27720
  · have h2 : (e + 27719) % 120 = (e + 119) % 120 := by omega
    simp [he, Nat.mod_lt _ (show 0 < 120 by norm_num), Nat.mod_lt _ (show 0 < 27720 by norm_num), h1, h2]
  · simp [he]

/-! ## Tuple sums -/

theorem tupleSum_append (per : ℕ) (G : ℕ → ℚ) :
    ∀ (ps qs : List ℕ) (acc : ℕ), tupleSum per (ps ++ qs) acc G = tupleSum per ps acc (fun x => tupleSum per qs x G)
  | [], qs, acc => rfl
  | p :: ps, qs, acc => by
    simp only [List.cons_append, tupleSum]
    exact sum_congr rfl fun r _ => tupleSum_append per G ps qs _

theorem tupleSum_lift {p n : ℕ} (hp : 0 < p) (G : ℕ → ℚ) :
    ∀ (ps : List ℕ), (∀ q ∈ ps, 1 < q ∧ 2 ^ p % q = 1) →
      ∀ a, tupleSum n ps (repB p n a) G = tupleSum p ps a (fun x => G (repB p n x))
  | [], _, a => rfl
  | q :: ps, h, a => by
    simp only [tupleSum]
    obtain ⟨hq, h2⟩ := h q (by simp)
    refine sum_congr rfl fun r _ => ?_
    rw [maskP_rep (n := n) hp hq h2, ← repB_or]
    exact tupleSum_lift hp G ps (fun q' hq' => h q' (by simp [hq'])) _

theorem wsum_tupleSum {per : ℕ} (hper : 0 < per) {G : ℕ → ℚ} (hG : ∀ x, x < 2 ^ per → G (rot1 per x) = G x)
    (ps : List ℕ) (hps : GoodPrimes per ps) : wsum (foldOrbits per ps) G = tupleSum per ps 0 G := by
  unfold foldOrbits
  rw [wsum_foldl hper hG ps hps [(0, 1)] (fun xc hxc => by rw [List.mem_singleton.mp hxc]; exact Nat.two_pow_pos _)]
  simp [wsum]

end Romanoff.G.S2
