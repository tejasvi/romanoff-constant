import Romanoff.Bits

/-!
# Soundness of the pattern fold modulo rotation

`wsum L H = Σ_{(x, c) ∈ L} c H(x)`.  For `H` invariant under rotation (on `per`-bit masks):
`wsum (foldOrbits per ps) H = Σ_{k < ∏ ps} H(exmask k)`, the exclusion mask of `k` being the union of `maskP per p (k % p)`
over the primes `p ∈ ps` (distinct odd primes with `2^per ≡ 1 mod p`).
-/

namespace Romanoff

open R45 Finset

/-- `Σ_{(x, c) ∈ L} c H(x)`. -/
def wsum (L : List (ℕ × ℕ)) (H : ℕ → ℚ) : ℚ := (L.map fun xc => (xc.2 : ℚ) * H xc.1).sum

theorem wsum_nil (H : ℕ → ℚ) : wsum [] H = 0 := rfl

theorem wsum_cons (a : ℕ × ℕ) (L : List (ℕ × ℕ)) (H : ℕ → ℚ) : wsum (a :: L) H = (a.2 : ℚ) * H a.1 + wsum L H := by
  simp [wsum]

theorem wsum_append (L M : List (ℕ × ℕ)) (H : ℕ → ℚ) : wsum (L ++ M) H = wsum L H + wsum M H := by
  simp [wsum, List.map_append, List.sum_append]

theorem wsum_perm {L M : List (ℕ × ℕ)} (h : L.Perm M) (H : ℕ → ℚ) : wsum L H = wsum M H := by
  unfold wsum; exact (h.map _).sum_eq

/-! ## The options of one prime -/

theorem listSum_range_eq (f : ℕ → ℚ) (n : ℕ) : ((List.range n).map f).sum = ∑ r ∈ range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem listSum_filter (f : ℕ → ℚ) (P : ℕ → Bool) (n : ℕ) :
    (((List.range n).filter P).map f).sum = ∑ r ∈ (range n).filter (fun r => P r = true), f r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases hP : P n = true
    · simp only [List.filter_cons, List.filter_nil, hP, if_true, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      rw [sum_insert (by simp)]; ring
    · simp only [List.filter_cons, List.filter_nil, hP, if_false, List.map_nil, List.sum_nil, add_zero, Bool.false_eq_true]

/-- Grouping: `Σ_{r < p} H(mask r) = Σ_{(m, c) ∈ opts} c H(m)`. -/
theorem wsum_optsP (per p : ℕ) (H : ℕ → ℚ) : wsum (optsP per p) H = ∑ r ∈ range p, H (maskP per p r) := by
  unfold optsP
  rw [wsum_append, wsum_cons, wsum_nil, add_zero]
  have h1 : wsum (((List.range p).filter fun r => maskP per p r != 0).map fun r => (maskP per p r, 1)) H =
      ∑ r ∈ (range p).filter (fun r => (maskP per p r != 0) = true), H (maskP per p r) := by
    unfold wsum
    rw [List.map_map]
    rw [show ((fun xc : ℕ × ℕ => (xc.2 : ℚ) * H xc.1) ∘ fun r => (maskP per p r, 1)) = fun r => H (maskP per p r) by
      funext r; simp]
    exact listSum_filter _ _ p
  have h2 : ((((List.range p).filter fun r => maskP per p r == 0).length : ℕ) : ℚ) * H 0 =
      ∑ r ∈ (range p).filter (fun r => (maskP per p r == 0) = true), H (maskP per p r) := by
    have hl : (((List.range p).filter fun r => maskP per p r == 0).length : ℚ) =
        (((List.range p).filter fun r => maskP per p r == 0).map fun _ => (1 : ℚ)).sum := by simp
    rw [hl, listSum_filter, sum_mul, one_mul]
    refine sum_congr rfl fun r hr => ?_
    simp only [mem_filter, beq_iff_eq] at hr
    rw [hr.2]
  rw [h1, h2]
  rw [← sum_filter_add_sum_filter_not (range p) (fun r => (maskP per p r != 0) = true)]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext r; simp

/-- Multiplication by 2 permutes the residues mod an odd prime. -/
theorem sum_range_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ → ℚ) :
    ∑ r ∈ range p, f (2 * r % p) = ∑ r ∈ range p, f r := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hp0 : 0 < p := hp.pos
  have hinj : Set.InjOn (fun r => 2 * r % p) (range p : Set ℕ) := by
    intro a ha b hb hab
    have h : 2 * a ≡ 2 * b [MOD p] := hab
    have := Nat.ModEq.cancel_left_of_coprime (by rwa [Nat.coprime_comm] at hcop) h
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] at this
  have himg : (range p).image (fun r => 2 * r % p) = range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨r, _, rfl⟩ := mem_image.mp hy
      exact mem_range.mpr (Nat.mod_lt _ hp0)
    · rw [card_image_of_injOn hinj]
  rw [← sum_image (f := f) hinj, himg]

/-- The option table is rotation invariant. -/
theorem wsum_optsP_rot {per p : ℕ} (hper : 0 < per) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ^ per % p = 1)
    (H : ℕ → ℚ) : wsum (optsP per p) (fun m => H (rot1 per m)) = wsum (optsP per p) H := by
  rw [wsum_optsP, wsum_optsP]
  rw [← sum_range_two_mul hp hp2 (fun r => H (maskP per p r))]
  refine sum_congr rfl fun r hr => ?_
  rw [maskP_two_mul hper hp hp2 h2 (mem_range.mp hr)]

/-! ## Normalization and one step -/

theorem wsum_combine (H : ℕ → ℚ) : ∀ L : List (ℕ × ℕ), wsum (combine L) H = wsum L H
  | [] => by simp [combine]
  | [a] => by simp [combine]
  | a :: b :: L => by
    unfold combine
    split_ifs with h
    · rw [wsum_combine H ((a.1, a.2 + b.2) :: L), wsum_cons, wsum_cons, wsum_cons]
      have : b.1 = a.1 := (beq_iff_eq.mp h).symm
      simp only [this]; push_cast; ring
    · rw [wsum_cons, wsum_combine H (b :: L), wsum_cons a (b :: L)]
termination_by L => L.length

theorem wsum_normalize (L : List (ℕ × ℕ)) (H : ℕ → ℚ) : wsum (R45.normalize L) H = wsum L H := by
  unfold R45.normalize
  rw [wsum_combine, wsum_perm (List.mergeSort_perm _ _)]

theorem wsum_flatMap (L : List (ℕ × ℕ)) (f : ℕ × ℕ → List (ℕ × ℕ)) (H : ℕ → ℚ) :
    wsum (L.flatMap f) H = (L.map fun xc => wsum (f xc) H).sum := by
  induction L with
  | nil => simp [wsum]
  | cons a L ih => rw [List.flatMap_cons, wsum_append, ih, List.map_cons, List.sum_cons]

theorem wsum_eq_sum_map (L : List (ℕ × ℕ)) (H : ℕ → ℚ) : wsum L H = (L.map fun xc => (xc.2 : ℚ) * H xc.1).sum := rfl

/-- One step: `wsum (step L) H = Σ_{(x,c) ∈ L} c Σ_{(m,d) ∈ opts} d H(canon (x ∣ m))`. -/
theorem wsum_foldStep (per : ℕ) (L opts : List (ℕ × ℕ)) (H : ℕ → ℚ) :
    wsum (foldStep per L opts) H = wsum L (fun x => wsum opts (fun m => H (canon per (x ||| m)))) := by
  unfold foldStep
  rw [wsum_normalize, wsum_flatMap, wsum_eq_sum_map L]
  congr 1
  refine List.map_congr_left fun xc _ => ?_
  unfold wsum
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun mc _ => ?_
  simp only [Function.comp_apply]
  push_cast; ring

/-! ## The fold over the primes -/

theorem wsum_congr {L : List (ℕ × ℕ)} {f g : ℕ → ℚ} (h : ∀ xc ∈ L, f xc.1 = g xc.1) : wsum L f = wsum L g := by
  unfold wsum
  congr 1
  exact List.map_congr_left fun xc hxc => by rw [h xc hxc]

theorem combine_keys (P : ℕ → Prop) : ∀ L : List (ℕ × ℕ), (∀ xc ∈ L, P xc.1) → ∀ xc ∈ combine L, P xc.1
  | [], _ => by simp [combine]
  | [a], h => by simpa [combine] using h
  | a :: b :: L, h => by
    unfold combine
    split_ifs with hab
    · intro xc hxc
      refine combine_keys P ((a.1, a.2 + b.2) :: L) (fun yc hyc => ?_) xc hxc
      rcases List.mem_cons.mp hyc with rfl | hyc
      · exact h a (by simp)
      · exact h yc (by simp [hyc])
    · intro xc hxc
      rcases List.mem_cons.mp hxc with rfl | hxc
      · exact h xc (by simp)
      · exact combine_keys P (b :: L) (fun yc hyc => h yc (by
          rcases List.mem_cons.mp hyc with rfl | hyc
          · simp
          · simp [hyc])) xc hxc
termination_by L => L.length

theorem normalize_keys (P : ℕ → Prop) (L : List (ℕ × ℕ)) (h : ∀ xc ∈ L, P xc.1) :
    ∀ xc ∈ R45.normalize L, P xc.1 := by
  unfold R45.normalize
  exact combine_keys P _ fun xc hxc => h xc ((List.mergeSort_perm _ _).mem_iff.mp hxc)

theorem optsP_lt (per p : ℕ) : ∀ mc ∈ optsP per p, mc.1 < 2 ^ per := by
  intro mc hmc
  unfold optsP at hmc
  rcases List.mem_append.mp hmc with h | h
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp h
    exact maskP_lt per p r
  · simp only [List.mem_singleton] at h
    rw [h]; exact Nat.two_pow_pos per

theorem foldStep_keys (per : ℕ) (L opts : List (ℕ × ℕ)) (hL : ∀ xc ∈ L, xc.1 < 2 ^ per)
    (ho : ∀ mc ∈ opts, mc.1 < 2 ^ per) : ∀ xc ∈ foldStep per L opts, xc.1 < 2 ^ per := by
  unfold foldStep
  refine normalize_keys (fun x => x < 2 ^ per) _ (fun xc hxc => ?_)
  obtain ⟨yc, hyc, hxc'⟩ := List.mem_flatMap.mp hxc
  obtain ⟨mc, hmc, rfl⟩ := List.mem_map.mp hxc'
  exact canon_lt (Nat.or_lt_two_pow (hL yc hyc) (ho mc hmc))

/-- Odd primes with `2^per ≡ 1`. -/
def GoodPrimes (per : ℕ) (ps : List ℕ) : Prop := ∀ p ∈ ps, p.Prime ∧ p ≠ 2 ∧ 2 ^ per % p = 1

/-- `Σ_{r_1 < p_1} … Σ_{r_n < p_n} G(acc ∪ mask r_1 ∪ … ∪ mask r_n)`. -/
def tupleSum (per : ℕ) : List ℕ → ℕ → (ℕ → ℚ) → ℚ
  | [], acc, G => G acc
  | p :: ps, acc, G => ∑ r ∈ range p, tupleSum per ps (acc ||| maskP per p r) G

theorem tupleSum_rot {per : ℕ} (hper : 0 < per) {G : ℕ → ℚ} (hG : ∀ x, x < 2 ^ per → G (rot1 per x) = G x) :
    ∀ (ps : List ℕ), GoodPrimes per ps → ∀ x, x < 2 ^ per → tupleSum per ps (rot1 per x) G = tupleSum per ps x G
  | [], _, x, hx => by simp [tupleSum, hG x hx]
  | p :: ps, hps, x, hx => by
    obtain ⟨hp, hp2, h2⟩ := hps p (by simp)
    have hps' : GoodPrimes per ps := fun q hq => hps q (by simp [hq])
    simp only [tupleSum]
    rw [← sum_range_two_mul hp hp2 (fun r => tupleSum per ps (rot1 per x ||| maskP per p r) G)]
    refine sum_congr rfl fun r hr => ?_
    rw [maskP_two_mul hper hp hp2 h2 (mem_range.mp hr), ← rot1_or hper hx (maskP_lt per p r),
      tupleSum_rot hper hG ps hps' _ (Nat.or_lt_two_pow hx (maskP_lt per p r))]

/-- The fold computes the tuple sum of every rotation-invariant function. -/
theorem wsum_foldl {per : ℕ} (hper : 0 < per) {G : ℕ → ℚ} (hG : ∀ x, x < 2 ^ per → G (rot1 per x) = G x) :
    ∀ (ps : List ℕ), GoodPrimes per ps → ∀ (L : List (ℕ × ℕ)), (∀ xc ∈ L, xc.1 < 2 ^ per) →
      wsum (ps.foldl (fun L p => foldStep per L (optsP per p)) L) G = wsum L (fun x => tupleSum per ps x G)
  | [], _, L, _ => by simp [tupleSum]
  | p :: ps, hps, L, hL => by
    have hps' : GoodPrimes per ps := fun q hq => hps q (by simp [hq])
    rw [List.foldl_cons, wsum_foldl hper hG ps hps' _ (foldStep_keys per L _ hL (optsP_lt per p)),
      wsum_foldStep]
    apply wsum_congr
    intro xc hxc
    have hx := hL xc hxc
    simp only [tupleSum]
    rw [← wsum_optsP per p (fun m => tupleSum per ps (xc.1 ||| m) G)]
    apply wsum_congr
    intro mc hmc
    exact canon_inv (G := fun y => tupleSum per ps y G) (fun y hy => tupleSum_rot hper hG ps hps' y hy)
      (Nat.or_lt_two_pow hx (optsP_lt per p mc hmc))

/-! ## The Chinese remainder theorem -/

/-- The exclusion mask of `k`: `acc ∪ ⋃_{p ∈ ps} maskP per p (k % p)`. -/
def exmaskL (per : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], acc, _ => acc
  | p :: ps, acc, k => exmaskL per ps (acc ||| maskP per p (k % p)) k

theorem exmaskL_mod (per : ℕ) : ∀ (ps : List ℕ) (acc k m : ℕ), (∀ q ∈ ps, q ∣ m) →
    exmaskL per ps acc (k % m) = exmaskL per ps acc k
  | [], acc, k, m, _ => rfl
  | q :: ps, acc, k, m, h => by
    simp only [exmaskL]
    rw [Nat.mod_mod_of_dvd k (h q (by simp)), exmaskL_mod per ps _ k m fun q' hq' => h q' (by simp [hq'])]

theorem sum_range_mul_crt {p m : ℕ} (hcop : Nat.Coprime p m) (hp : 0 < p) (hm : 0 < m) (F : ℕ → ℕ → ℚ) :
    ∑ k ∈ range (p * m), F (k % p) (k % m) = ∑ a ∈ range p, ∑ b ∈ range m, F a b := by
  rw [← sum_product (range p) (range m) (fun ab => F ab.1 ab.2)]
  have hinj : Set.InjOn (fun k => (k % p, k % m)) (range (p * m) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hab.1, hab.2⟩
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] at h
  have himg : (range (p * m)).image (fun k => (k % p, k % m)) = range p ×ˢ range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨k, _, rfl⟩ := mem_image.mp hy
      exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp), mem_range.mpr (Nat.mod_lt _ hm)⟩
    · rw [card_image_of_injOn hinj, card_product, card_range, card_range, card_range]
  rw [← himg, sum_image hinj]

/-- Distinct primes. -/
def DistinctPrimes (ps : List ℕ) : Prop := ps.Nodup ∧ ∀ p ∈ ps, p.Prime

theorem coprime_prod {p : ℕ} (hp : p.Prime) : ∀ (ps : List ℕ), (∀ q ∈ ps, q.Prime ∧ q ≠ p) → Nat.Coprime p ps.prod
  | [], _ => by simp
  | q :: ps, h => by
    rw [List.prod_cons]
    refine Nat.Coprime.mul_right ?_ (coprime_prod hp ps fun q' hq' => h q' (by simp [hq']))
    exact (Nat.coprime_primes hp (h q (by simp)).1).mpr (h q (by simp)).2.symm

/-- `Σ_{k < ∏ ps} G(exmask k) = tupleSum`. -/
theorem sum_exmaskL (per : ℕ) (G : ℕ → ℚ) :
    ∀ (ps : List ℕ), DistinctPrimes ps → ∀ acc, ∑ k ∈ range ps.prod, G (exmaskL per ps acc k) = tupleSum per ps acc G
  | [], _, acc => by simp [exmaskL, tupleSum]
  | p :: ps, ⟨hnd, hpr⟩, acc => by
    have hp := hpr p (by simp)
    have hnd' := (List.nodup_cons.mp hnd)
    have hps : DistinctPrimes ps := ⟨hnd'.2, fun q hq => hpr q (by simp [hq])⟩
    have hcop : Nat.Coprime p ps.prod :=
      coprime_prod hp ps fun q hq => ⟨hpr q (by simp [hq]), fun h => hnd'.1 (h ▸ hq)⟩
    have hm : 0 < ps.prod := List.prod_pos fun q hq => (hpr q (by simp [hq])).pos
    rw [List.prod_cons]
    simp only [exmaskL, tupleSum]
    have h1 : ∀ k, G (exmaskL per ps (acc ||| maskP per p (k % p)) k) =
        G (exmaskL per ps (acc ||| maskP per p (k % p)) (k % ps.prod)) := by
      intro k
      rw [exmaskL_mod per ps _ k ps.prod fun q hq => List.dvd_prod hq]
    rw [sum_congr rfl fun k _ => h1 k]
    rw [sum_range_mul_crt (F := fun a b => G (exmaskL per ps (acc ||| maskP per p a) b)) hcop hp.pos hm]
    exact sum_congr rfl fun a _ => sum_exmaskL per G ps hps (acc ||| maskP per p a)

end Romanoff
