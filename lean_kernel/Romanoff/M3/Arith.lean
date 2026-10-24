import Romanoff.TBoundSpec
import RCert.M3.Check

/-!
# M3 soundness, part 1: modular powers, trial division, Pratt certificates, exact orders

`powMod_eq`: `powMod b e m = b ^ e % m`; `tdPrime_sound`; `pratt_sound`: every Pratt record is prime (strong induction
on `n`, Mathlib's `lucas_primality`); `grp_sound`: every prime of a checked group has exact order `t`
(`orderOf_eq_of_pow_and_pow_div_prime`).
-/

namespace Romanoff.M3

open R45.M3

/-! ## Modular powers -/

theorem powModAux_eq (m : ℕ) (hm : 0 < m) :
    ∀ (fuel b e acc : ℕ), acc < m → e < 2 ^ fuel → powModAux m fuel b e acc = acc * b ^ e % m
  | 0, b, e, acc, hacc, he => by
    have : e = 0 := by simpa using he
    subst this
    simp [powModAux, Nat.mod_eq_of_lt hacc]
  | fuel + 1, b, e, acc, hacc, he => by
    unfold powModAux
    by_cases he0 : e = 0
    · subst he0; simp [Nat.mod_eq_of_lt hacc]
    · rw [ite_eq_right he0]
      have hacc' : (if e % 2 = 1 then acc * b % m else acc) < m := by
        split_ifs
        · exact Nat.mod_lt _ hm
        · exact hacc
      have he' : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he; omega
      rw [powModAux_eq m hm fuel _ _ _ hacc' he']
      have hbb : b * b % m ≡ b * b [MOD m] := Nat.mod_modEq _ _
      have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2
      · rw [if_neg (by omega)]
        have key : acc * (b * b % m) ^ (e / 2) ≡ acc * (b * b) ^ (e / 2) [MOD m] :=
          (Nat.ModEq.refl acc).mul (hbb.pow _)
        have hpow : (b * b) ^ (e / 2) = b ^ e := by
          rw [← sq, ← pow_mul]; congr 1; omega
        rw [hpow] at key
        exact key
      · rw [if_pos h2]
        have key : acc * b % m * (b * b % m) ^ (e / 2) ≡ acc * b * (b * b) ^ (e / 2) [MOD m] :=
          (Nat.mod_modEq _ _).mul (hbb.pow _)
        have hpow : acc * b * (b * b) ^ (e / 2) = acc * b ^ e := by
          rw [← sq, ← pow_mul, mul_assoc, ← pow_succ']; congr 2; omega
        rw [hpow] at key
        exact key

theorem powMod_eq (b e m : ℕ) (hm : 0 < m) : powMod b e m = b ^ e % m := by
  unfold powMod
  rw [powModAux_eq m hm _ _ _ _ (Nat.mod_lt _ hm) Nat.lt_log2_self]
  have : 1 % m * (b % m) ^ e ≡ 1 * b ^ e [MOD m] := (Nat.mod_modEq 1 m).mul ((Nat.mod_modEq b m).pow e)
  rw [one_mul] at this
  exact this

/-- `(a : ZMod n) ^ k = 1 ↔ a ^ k % n = 1` for `n ≥ 2`. -/
theorem zmod_pow_eq_one_iff (n a k : ℕ) (hn : 2 ≤ n) : (a : ZMod n) ^ k = 1 ↔ a ^ k % n = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : 1 < n)]

/-! ## Trial division -/

theorem tdLoop_sound (n : ℕ) : ∀ (fuel d : ℕ), tdLoop n fuel d = true → ∀ k, d ≤ k → k * k ≤ n → n % k ≠ 0
  | 0, d, h => by simp [tdLoop] at h
  | fuel + 1, d, h => by
    unfold tdLoop at h
    intro k hk hkk
    by_cases h1 : n < d * d
    · exfalso; have := Nat.mul_le_mul hk hk; omega
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hk with rfl | hk'
        · exact h2
        · exact tdLoop_sound n fuel (d + 1) h k hk' hkk

theorem tdPrime_sound (n : ℕ) (h : tdPrime n = true) : n.Prime := by
  unfold tdPrime at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h.1, fun k hk hks hdvd => ?_⟩
  have hkk : k * k ≤ n := Nat.le_sqrt.mp hks
  exact tdLoop_sound n n 2 h.2 k hk hkk (Nat.mod_eq_zero_of_dvd hdvd)

/-! ## Factor lists -/

theorem prime_mem_of_dvd_prodPow : ∀ (fs : List (ℕ × ℕ)), (∀ x ∈ fs, x.1.Prime) →
    ∀ q : ℕ, q.Prime → q ∣ prodPow fs → ∃ e, (q, e) ∈ fs
  | [], _, q, hq, h => by
    simp [prodPow] at h; exact absurd h hq.one_lt.ne'
  | (r, e) :: fs, hfs, q, hq, h => by
    simp only [prodPow] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · have hr : r.Prime := hfs (r, e) (by simp)
      have : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h1)
      exact ⟨e, by simp [this]⟩
    · obtain ⟨e', he'⟩ := prime_mem_of_dvd_prodPow fs (fun x hx => hfs x (by simp [hx])) q hq h1
      exact ⟨e', by simp [he']⟩

theorem dvd_prodPow : ∀ (fs : List (ℕ × ℕ)) (q e : ℕ), (q, e) ∈ fs → 1 ≤ e → q ∣ prodPow fs
  | [], q, e, h, _ => by simp at h
  | (r, e') :: fs, q, e, h, he => by
    simp only [prodPow]
    rcases List.mem_cons.mp h with h1 | h1
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact Dvd.dvd.mul_right (dvd_pow_self q (by omega)) _
    · exact Dvd.dvd.mul_left (dvd_prodPow fs q e h1 he) _

/-! ## Sorting and membership (natural numbers) -/

theorem mem_mergeNat : ∀ (xs ys : List ℕ) (z : ℕ), z ∈ mergeNat xs ys ↔ z ∈ xs ∨ z ∈ ys
  | [], ys, z => by simp [mergeNat]
  | x :: xs, ys, z => by
    simp only [mergeNat]
    induction ys with
    | nil => simp [mergeNat.mergeNatIns, mem_mergeNat xs [] z]
    | cons y ys ih =>
      unfold mergeNat.mergeNatIns
      split_ifs with h1 h2
      · simp [mem_mergeNat xs (y :: ys) z]; tauto
      · simp only [List.mem_cons, ih]; tauto
      · have : x = y := by omega
        subst this
        simp [mem_mergeNat xs ys z]; tauto

theorem mem_mergePairsNat : ∀ (ls : List (List ℕ)) (z : ℕ), (∃ l ∈ mergePairsNat ls, z ∈ l) ↔ ∃ l ∈ ls, z ∈ l
  | l1 :: l2 :: ls, z => by
    simp only [mergePairsNat, List.mem_cons, exists_eq_or_imp, mem_mergeNat, mem_mergePairsNat ls z]
    tauto
  | [], z => by simp [mergePairsNat]
  | [l], z => by simp [mergePairsNat]

theorem mem_foldl_mergeNat : ∀ (ls : List (List ℕ)) (acc : List ℕ) (z : ℕ),
    z ∈ ls.foldl mergeNat acc ↔ z ∈ acc ∨ ∃ l ∈ ls, z ∈ l
  | [], acc, z => by simp
  | l :: ls, acc, z => by
    simp only [List.foldl_cons, mem_foldl_mergeNat ls _ z, mem_mergeNat, List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_mergeAllNat : ∀ (fuel : ℕ) (ls : List (List ℕ)) (z : ℕ), z ∈ mergeAllNat fuel ls ↔ ∃ l ∈ ls, z ∈ l
  | _, [], z => by simp [mergeAllNat]
  | _, [l], z => by simp [mergeAllNat]
  | 0, l1 :: l2 :: ls, z => by
    simp only [mergeAllNat, mem_foldl_mergeNat]; simp
  | fuel + 1, l1 :: l2 :: ls, z => by
    simp only [mergeAllNat]
    rw [mem_mergeAllNat fuel _ z, mem_mergePairsNat]

theorem mem_sortNat (l : List ℕ) (z : ℕ) : z ∈ sortNat l ↔ z ∈ l := by
  unfold sortNat
  rw [mem_mergeAllNat]
  simp

theorem subSorted_sound : ∀ (xs ys : List ℕ), subSorted xs ys = true → ∀ x ∈ xs, x ∈ ys
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [subSorted] at h
  | x :: xs, y :: ys, h => by
    unfold subSorted at h
    split_ifs at h with h1 h2
    · subst h1
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · exact List.mem_cons_of_mem _ (subSorted_sound xs ys h z hz)
    · intro z hz; exact List.mem_cons_of_mem _ (subSorted_sound (x :: xs) ys h z hz)

theorem sortedLT_nodup : ∀ (l : List ℕ), sortedLT l = true → l.Nodup ∧ ∀ x ∈ l, ∀ y ∈ l, x ≤ y ∨ y ≤ x
  | [], _ => by simp
  | [_], _ => by simp
  | x :: y :: l, h => by
    simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn, _⟩ := sortedLT_nodup (y :: l) h.2
    refine ⟨List.nodup_cons.mpr ⟨?_, hn⟩, fun a _ b _ => le_total a b⟩
    intro hx
    have key : ∀ (l : List ℕ) (y : ℕ), sortedLT (y :: l) = true → ∀ z ∈ y :: l, y ≤ z := by
      intro l
      induction l with
      | nil => intro y _ z hz; simp at hz; omega
      | cons w l ih =>
        intro y hy z hz
        simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at hy
        rcases List.mem_cons.mp hz with rfl | hz
        · exact le_rfl
        · exact le_trans (Nat.le_of_lt hy.1) (ih w hy.2 z hz)
    have := key l y h.2 x hx
    omega

/-- Strictly increasing lists have no duplicates. -/
theorem sortedLT_nodup' (l : List ℕ) (h : sortedLT l = true) : l.Nodup := (sortedLT_nodup l h).1

/-- In a strictly increasing list every later element is larger than the head. -/
theorem sortedLT_head_lt : ∀ (l : List ℕ) (y : ℕ), sortedLT (y :: l) = true → ∀ z ∈ l, y < z
  | [], _, _, z, hz => by simp at hz
  | w :: l, y, h, z, hz => by
    simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact lt_trans h.1 (sortedLT_head_lt l w h.2 z hz)

/-! ## Pratt certificates -/

theorem bigFactor_mem (recs : List PRec) (h : prattOK recs = true) (r : PRec) (hr : r ∈ recs) (q e : ℕ)
    (hq : (q, e) ∈ r.fs) (hbig : SMALL ≤ q) : q ∈ recs.map (·.n) := by
  unfold prattOK at h
  simp only [Bool.and_eq_true] at h
  apply subSorted_sound _ _ h.2 q
  rw [mem_sortNat]
  unfold bigOnly
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  exact ⟨⟨r, hr, (q, e), hq, rfl⟩, hbig⟩

theorem recOK_spec (r : PRec) (h : recOK r = true) :
    3 ≤ r.n ∧ prodPow r.fs = r.n - 1 ∧ powMod r.a (r.n - 1) r.n = 1 ∧
      ∀ qe ∈ r.fs, 1 ≤ qe.2 ∧ powMod r.a ((r.n - 1) / qe.1) r.n ≠ 1 ∧ (qe.1 < SMALL → tdPrime qe.1 = true) := by
  unfold recOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun qe hqe => ?_⟩
  have := h4 qe hqe
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨ha, hb⟩, hc⟩ := this
  refine ⟨ha, hb, fun hs => ?_⟩
  simpa [hs] using hc

theorem pratt_sound (recs : List PRec) (h : prattOK recs = true) : ∀ r ∈ recs, r.n.Prime := by
  have hall : ∀ r ∈ recs, recOK r = true := by
    unfold prattOK at h; simp only [Bool.and_eq_true, List.all_eq_true] at h; exact h.1.2
  suffices H : ∀ k, ∀ r ∈ recs, r.n = k → r.n.Prime from fun r hr => H r.n r hr rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r hr hrk
    obtain ⟨h3, hprod, hpow, hfs⟩ := recOK_spec r (hall r hr)
    have hfac : ∀ qe ∈ r.fs, qe.1.Prime := by
      intro qe hqe
      obtain ⟨he, _, hsm⟩ := hfs qe hqe
      by_cases hs : qe.1 < SMALL
      · exact tdPrime_sound _ (hsm hs)
      · have hmem := bigFactor_mem recs h r hr qe.1 qe.2 hqe (by omega)
        obtain ⟨r', hr', hr'n⟩ := List.mem_map.mp hmem
        have hdvd : qe.1 ∣ r.n - 1 := hprod ▸ dvd_prodPow r.fs qe.1 qe.2 hqe he
        have hlt : qe.1 < k := by
          have := Nat.le_of_dvd (by omega) hdvd; omega
        exact hr'n ▸ ih qe.1 hlt r' hr' hr'n
    have hn2 : 2 ≤ r.n := by omega
    apply lucas_primality r.n (r.a : ZMod r.n)
    · rw [zmod_pow_eq_one_iff _ _ _ hn2, ← powMod_eq _ _ _ (by omega), hpow]
    · intro q hq hqd
      obtain ⟨e, he⟩ := prime_mem_of_dvd_prodPow r.fs hfac q hq (hprod ▸ hqd)
      obtain ⟨_, hne, _⟩ := hfs (q, e) he
      rw [Ne, zmod_pow_eq_one_iff _ _ _ hn2, ← powMod_eq _ _ _ (by omega)]
      exact hne

/-! ## Certified primes and exact orders -/

theorem primeOK_sound (recs : List PRec) (hp : prattOK recs = true) (ps : List ℕ)
    (h : primeOK (recs.map (·.n)) ps = true) : ∀ p ∈ ps, p.Prime := by
  unfold primeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro p hp'
  by_cases hs : p < SMALL
  · have := h.1 p hp'; simp only [hs, if_true] at this; exact tdPrime_sound p this
  · have hmem : p ∈ recs.map (·.n) := by
      apply subSorted_sound _ _ h.2 p
      rw [mem_sortNat]; unfold bigOnly; simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hp', by omega⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmem
    exact pratt_sound recs hp r hr

theorem grpOK_spec (g : Grp) (h : grpOK g = true) :
    1 ≤ g.t ∧ prodPow g.tfac = g.t ∧ (∀ re ∈ g.tfac, 1 ≤ re.2 ∧ tdPrime re.1 = true) ∧ sortedLT g.ps = true ∧
      ∀ p ∈ g.ps, 3 ≤ p ∧ powMod 2 g.t p = 1 ∧ ∀ re ∈ g.tfac, powMod 2 (g.t / re.1) p ≠ 1 := by
  unfold grpOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun re hre => ?_, h4, fun p hp => ?_⟩
  · have := h3 re hre; simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  · have := h5 p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

/-- Every prime of a checked group has exact order `t`. -/
theorem grp_ordm (g : Grp) (h : grpOK g = true) (p : ℕ) (hp : p ∈ g.ps) (hpr : p.Prime) : ordm p = g.t := by
  obtain ⟨ht, hprod, hfac, _, hps⟩ := grpOK_spec g h
  obtain ⟨hp3, hpow, hdiv⟩ := hps p hp
  have hp2 : 2 ≤ p := by omega
  unfold ordm
  have h2 : ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
  · rw [← h2, zmod_pow_eq_one_iff _ _ _ hp2, ← powMod_eq _ _ _ (by omega), hpow]
  · intro r hr hrd
    obtain ⟨e, he⟩ := prime_mem_of_dvd_prodPow g.tfac (fun re hre => tdPrime_sound _ (hfac re hre).2) r hr
      (hprod ▸ hrd)
    rw [← h2, Ne, zmod_pow_eq_one_iff _ _ _ hp2, ← powMod_eq _ _ _ (by omega)]
    exact hdiv (r, e) he

end Romanoff.M3
