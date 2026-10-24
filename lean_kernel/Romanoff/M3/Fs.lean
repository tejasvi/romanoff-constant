import Romanoff.M3.Arith

/-!
# M3 soundness, part 2: the subset-sum functional

For a list `xs` of pairs `(p, t)` (distinct primes `p ≥ 3` with `ordm p = t`) and `φ : ℕ → ℝ`,
`Fs xs φ = Σ_{s ⊆ xs} f(s) φ(lcm of the orders in s)`, `f(s) = ∏_{p ∈ s} 1/(p-2)`, defined by the recursion
`Fs (x :: xs) φ = Fs xs φ + f(x) Fs xs (φ ∘ lcm t_x)`.

* `sum_prodSet`: `Fs xs φ = Σ_{m ∈ prodSet xs} fm m φ(ordm m)` (`prodSet xs` = the products of the sublists);
* `mem_prodSet`: every squarefree `m` with all prime factors in `xs` is in `prodSet xs`;
* `Fs_group`: a group of primes of one order `t` acts through `∏ (1 + f(p)) - 1`;
* linearity, monotonicity, `Fs xs 1 = ∏ (1 + f(p))`.
-/

namespace Romanoff.M3

open R45.M3

/-- `1 / (p - 2)`. -/
noncomputable def fp (p : ℕ) : ℝ := 1 / ((p : ℝ) - 2)

theorem fp_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ fp p := by
  unfold fp
  apply div_nonneg zero_le_one
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

/-- The subset-sum functional. -/
noncomputable def Fs : List (ℕ × ℕ) → (ℕ → ℝ) → ℝ
  | [], φ => φ 1
  | x :: xs, φ => Fs xs φ + fp x.1 * Fs xs (fun L => φ (Nat.lcm x.2 L))

theorem Fs_nonneg : ∀ (xs : List (ℕ × ℕ)), (∀ x ∈ xs, 3 ≤ x.1) → ∀ (φ : ℕ → ℝ), (∀ L, 0 ≤ φ L) → 0 ≤ Fs xs φ
  | [], _, φ, hφ => hφ 1
  | x :: xs, hx, φ, hφ => by
    have hx' : ∀ y ∈ xs, 3 ≤ y.1 := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    exact add_nonneg (Fs_nonneg xs hx' φ hφ)
      (mul_nonneg (fp_nonneg (hx x (by simp))) (Fs_nonneg xs hx' _ fun L => hφ _))

theorem Fs_mono : ∀ (xs : List (ℕ × ℕ)), (∀ x ∈ xs, 3 ≤ x.1) → ∀ (φ ψ : ℕ → ℝ), (∀ L, φ L ≤ ψ L) →
    Fs xs φ ≤ Fs xs ψ
  | [], _, φ, ψ, h => h 1
  | x :: xs, hx, φ, ψ, h => by
    have hx' : ∀ y ∈ xs, 3 ≤ y.1 := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    exact add_le_add (Fs_mono xs hx' φ ψ h)
      (mul_le_mul_of_nonneg_left (Fs_mono xs hx' _ _ fun L => h _) (fp_nonneg (hx x (by simp))))

theorem Fs_add : ∀ (xs : List (ℕ × ℕ)) (φ ψ : ℕ → ℝ), Fs xs (fun L => φ L + ψ L) = Fs xs φ + Fs xs ψ
  | [], φ, ψ => rfl
  | x :: xs, φ, ψ => by
    simp only [Fs]
    rw [Fs_add xs φ ψ, Fs_add xs (fun L => φ (Nat.lcm x.2 L)) (fun L => ψ (Nat.lcm x.2 L))]
    ring

theorem Fs_smul : ∀ (xs : List (ℕ × ℕ)) (c : ℝ) (φ : ℕ → ℝ), Fs xs (fun L => c * φ L) = c * Fs xs φ
  | [], c, φ => rfl
  | x :: xs, c, φ => by
    simp only [Fs]
    rw [Fs_smul xs c φ, Fs_smul xs c (fun L => φ (Nat.lcm x.2 L))]
    ring

theorem Fs_sub (xs : List (ℕ × ℕ)) (φ ψ : ℕ → ℝ) : Fs xs (fun L => φ L - ψ L) = Fs xs φ - Fs xs ψ := by
  have h := Fs_add xs (fun L => φ L - ψ L) ψ
  simp only [sub_add_cancel] at h
  linarith

theorem Fs_zero (xs : List (ℕ × ℕ)) : Fs xs (fun _ => 0) = 0 := by
  have := Fs_smul xs 0 (fun _ => 0)
  simpa using this

theorem Fs_congr (xs : List (ℕ × ℕ)) (φ ψ : ℕ → ℝ) (h : ∀ L, φ L = ψ L) : Fs xs φ = Fs xs ψ := by
  rw [show φ = ψ from funext h]

theorem Fs_one : ∀ (xs : List (ℕ × ℕ)), Fs xs (fun _ => 1) = (xs.map fun x => 1 + fp x.1).prod
  | [] => by simp [Fs]
  | x :: xs => by
    simp only [Fs, List.map_cons, List.prod_cons]
    rw [Fs_one xs]
    ring

/-- `Fs` of `φ ∘ lcm L'` vanishes when `L' > LMAX` and `φ` vanishes at `0` and above `LMAX`. -/
theorem Fs_lcm_big (xs : List (ℕ × ℕ)) (ψ : ℕ → ℝ) (hψ : ∀ L, (L = 0 ∨ LMAX < L) → ψ L = 0) (L' : ℕ)
    (hL' : LMAX < L') : Fs xs (fun L => ψ (Nat.lcm L' L)) = 0 := by
  rw [Fs_congr xs _ (fun _ => 0), Fs_zero]
  intro L
  apply hψ
  by_cases hL : L = 0
  · left; simp [hL]
  · right
    have hpos : 0 < Nat.lcm L' L := Nat.lcm_pos (by omega) (Nat.pos_of_ne_zero hL)
    exact lt_of_lt_of_le hL' (Nat.le_of_dvd hpos (Nat.dvd_lcm_left L' L))

/-! ## Groups of primes of one order -/

/-- `∏ (1 + f(p)) - 1`. -/
noncomputable def eG (ps : List ℕ) : ℝ := (ps.map fun p => 1 + fp p).prod - 1

theorem Fs_group (t : ℕ) : ∀ (ps : List ℕ) (rest : List (ℕ × ℕ)) (φ : ℕ → ℝ),
    Fs (ps.map (fun p => (p, t)) ++ rest) φ = Fs rest φ + eG ps * Fs rest (fun L => φ (Nat.lcm t L))
  | [], rest, φ => by simp [eG]
  | p :: ps, rest, φ => by
    simp only [List.map_cons, List.cons_append, Fs]
    rw [Fs_group t ps rest φ, Fs_group t ps rest (fun L => φ (Nat.lcm t L))]
    have h : (fun L => φ (Nat.lcm t (Nat.lcm t L))) = (fun L => φ (Nat.lcm t L)) := by
      funext L; rw [← Nat.lcm_assoc, Nat.lcm_self]
    rw [h]
    simp only [eG, List.map_cons, List.prod_cons]
    ring

theorem eG_nonneg : ∀ (ps : List ℕ), (∀ p ∈ ps, 3 ≤ p) → 0 ≤ eG ps
  | [], _ => by simp [eG]
  | p :: ps, h => by
    have h1 := eG_nonneg ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h2 := fp_nonneg (h p (by simp))
    simp only [eG, List.map_cons, List.prod_cons] at h1 ⊢
    nlinarith

/-- The flattened prime list of a list of groups. -/
def flatG (gs : List Grp) : List (ℕ × ℕ) := gs.flatMap fun g => g.ps.map fun p => (p, g.t)

theorem flatG_cons (g : Grp) (gs : List Grp) : flatG (g :: gs) = g.ps.map (fun p => (p, g.t)) ++ flatG gs := by
  simp [flatG]

theorem Fs_one_flatG : ∀ (gs : List Grp), Fs (flatG gs) (fun _ => 1) = (gs.map fun g => 1 + eG g.ps).prod
  | [] => by simp [flatG, Fs]
  | g :: gs => by
    rw [flatG_cons, Fs_group, Fs_one_flatG gs]
    simp only [List.map_cons, List.prod_cons]
    ring

/-! ## Number theory: `fm` and `ordm` of products -/

theorem fm_one : fm 1 = 1 := by simp [fm]

theorem ordm_one : ordm 1 = 1 := by
  unfold ordm
  have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  exact Subsingleton.orderOf_eq _

theorem fm_mul_prime (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hpm : ¬ p ∣ m) : fm (p * m) = fp p * fm m := by
  unfold fm fp
  rw [Nat.primeFactors_mul hp.ne_zero hm, hp.primeFactors, ← Finset.insert_eq,
    Finset.prod_insert (by simp [Nat.mem_primeFactors, hpm])]

theorem ordm_mul (a b : ℕ) (h : Nat.Coprime a b) : ordm (a * b) = Nat.lcm (ordm a) (ordm b) := by
  unfold ordm
  rw [← MulEquiv.orderOf_eq (ZMod.chineseRemainder h).toMulEquiv]
  show orderOf ((ZMod.chineseRemainder h) (2 : ZMod (a * b))) = _
  rw [map_ofNat, Prod.orderOf, Prod.fst_ofNat, Prod.snd_ofNat]

theorem fm_nonneg (m : ℕ) : 0 ≤ fm m := by
  unfold fm
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  rcases Nat.eq_or_lt_of_le hp2 with h | h
  · subst h; norm_num
  · apply div_nonneg zero_le_one
    have : (3 : ℝ) ≤ p := by exact_mod_cast h
    linarith

/-! ## Products of sublists -/

/-- The products of the sublists of the primes of `xs`. -/
def prodSet : List (ℕ × ℕ) → Finset ℕ
  | [] => {1}
  | x :: xs => prodSet xs ∪ (prodSet xs).image (x.1 * ·)

/-- Hypotheses on a prime list. -/
def PList (xs : List (ℕ × ℕ)) : Prop :=
  (∀ x ∈ xs, x.1.Prime ∧ 3 ≤ x.1 ∧ ordm x.1 = x.2) ∧ (xs.map Prod.fst).Nodup

theorem PList.tail {x : ℕ × ℕ} {xs : List (ℕ × ℕ)} (h : PList (x :: xs)) : PList xs :=
  ⟨fun y hy => h.1 y (List.mem_cons_of_mem _ hy), (List.nodup_cons.mp (by simpa using h.2)).2⟩

theorem PList.head {x : ℕ × ℕ} {xs : List (ℕ × ℕ)} (h : PList (x :: xs)) :
    x.1.Prime ∧ 3 ≤ x.1 ∧ ordm x.1 = x.2 := h.1 x (by simp)

theorem PList.not_mem {x : ℕ × ℕ} {xs : List (ℕ × ℕ)} (h : PList (x :: xs)) : x.1 ∉ xs.map Prod.fst :=
  (List.nodup_cons.mp (by simpa using h.2)).1

theorem PList.three {xs : List (ℕ × ℕ)} (h : PList xs) : ∀ x ∈ xs, 3 ≤ x.1 := fun x hx => (h.1 x hx).2.1

theorem prodSet_spec : ∀ (xs : List (ℕ × ℕ)), PList xs →
    ∀ m ∈ prodSet xs, m ≠ 0 ∧ Squarefree m ∧ ∀ q ∈ m.primeFactors, q ∈ xs.map Prod.fst
  | [], _, m, hm => by
    simp only [prodSet, Finset.mem_singleton] at hm
    subst hm
    simp
  | x :: xs, hx, m, hm => by
    have hp := hx.head.1
    simp only [prodSet, Finset.mem_union, Finset.mem_image] at hm
    rcases hm with hm | ⟨m', hm', rfl⟩
    · obtain ⟨h0, hsq, hpf⟩ := prodSet_spec xs hx.tail m hm
      exact ⟨h0, hsq, fun q hq => by simp only [List.map_cons, List.mem_cons]; exact Or.inr (hpf q hq)⟩
    · obtain ⟨h0, hsq, hpf⟩ := prodSet_spec xs hx.tail m' hm'
      have hndvd : ¬ x.1 ∣ m' := fun hd => hx.not_mem (hpf x.1 (Nat.mem_primeFactors.mpr ⟨hp, hd, h0⟩))
      refine ⟨Nat.mul_ne_zero hp.ne_zero h0, ?_, ?_⟩
      · exact Nat.squarefree_mul_iff.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd, hp.squarefree, hsq⟩
      · intro q hq
        rw [Nat.primeFactors_mul hp.ne_zero h0, hp.primeFactors, Finset.mem_union, Finset.mem_singleton] at hq
        simp only [List.map_cons, List.mem_cons]
        rcases hq with rfl | hq
        · exact Or.inl rfl
        · exact Or.inr (hpf q hq)

theorem mem_prodSet : ∀ (xs : List (ℕ × ℕ)), PList xs → ∀ m, Squarefree m →
    (∀ q ∈ m.primeFactors, q ∈ xs.map Prod.fst) → m ∈ prodSet xs
  | [], _, m, hm, hpf => by
    have hpf' : m.primeFactors = ∅ := Finset.eq_empty_of_forall_notMem (fun q hq => by simpa using hpf q hq)
    rcases Nat.primeFactors_eq_empty.mp hpf' with h | h
    · subst h; exact absurd hm not_squarefree_zero
    · subst h; simp [prodSet]
  | x :: xs, hx, m, hm, hpf => by
    have hp := hx.head.1
    simp only [prodSet, Finset.mem_union, Finset.mem_image]
    by_cases hd : x.1 ∣ m
    · right
      obtain ⟨m', rfl⟩ := hd
      have hm0 : m' ≠ 0 := by rintro rfl; simp at hm
      have hcop : Nat.Coprime x.1 m' := (Nat.squarefree_mul_iff.mp hm).1
      refine ⟨m', mem_prodSet xs hx.tail m' (Nat.squarefree_mul_iff.mp hm).2.2 ?_, rfl⟩
      intro q hq
      have hq' : q ∈ (x.1 * m').primeFactors := by
        rw [Nat.primeFactors_mul hp.ne_zero hm0]; exact Finset.mem_union_right _ hq
      have := hpf q hq'
      simp only [List.map_cons, List.mem_cons] at this
      rcases this with h | h
      · exfalso
        have hqd : q ∣ m' := (Nat.mem_primeFactors.mp hq).2.1
        rw [h] at hqd
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hqd
      · exact h
    · left
      apply mem_prodSet xs hx.tail m hm
      intro q hq
      have := hpf q hq
      simp only [List.map_cons, List.mem_cons] at this
      rcases this with h | h
      · rw [h] at hq; exact absurd (Nat.mem_primeFactors.mp hq).2.1 hd
      · exact h

/-- The products with one more prime `q ∉ xs` of order `t`: `Σ = f(q) Fs xs (φ ∘ lcm t)`. -/
theorem sum_image_prodSet (q t : ℕ) (hq : q.Prime) (hqt : ordm q = t) (xs : List (ℕ × ℕ)) (hx : PList xs)
    (hqx : q ∉ xs.map Prod.fst) (φ : ℕ → ℝ)
    (IH : ∀ ψ : ℕ → ℝ, ∑ m ∈ prodSet xs, fm m * ψ (ordm m) = Fs xs ψ) :
    ∑ m ∈ (prodSet xs).image (q * ·), fm m * φ (ordm m) = fp q * Fs xs (fun L => φ (Nat.lcm t L)) := by
  rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq.pos h), ← IH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨h0, _, hpf⟩ := prodSet_spec xs hx m hm
  have hndvd : ¬ q ∣ m := fun hd => hqx (hpf q (Nat.mem_primeFactors.mpr ⟨hq, hd, h0⟩))
  rw [fm_mul_prime q m hq h0 hndvd, ordm_mul q m ((Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd), hqt]
  ring

theorem disjoint_prodSet_image (q : ℕ) (hq : q.Prime) (xs : List (ℕ × ℕ)) (hx : PList xs)
    (hqx : q ∉ xs.map Prod.fst) : Disjoint (prodSet xs) ((prodSet xs).image (q * ·)) := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hm'
  obtain ⟨h0, _, hpf⟩ := prodSet_spec xs hx _ hm
  exact hqx (hpf q (Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_right q m', h0⟩))

theorem sum_prodSet : ∀ (xs : List (ℕ × ℕ)), PList xs →
    ∀ φ : ℕ → ℝ, ∑ m ∈ prodSet xs, fm m * φ (ordm m) = Fs xs φ
  | [], _, φ => by simp [prodSet, Fs, fm_one, ordm_one]
  | x :: xs, hx, φ => by
    obtain ⟨hp, _, hord⟩ := hx.head
    simp only [prodSet, Fs]
    rw [Finset.sum_union (disjoint_prodSet_image x.1 hp xs hx.tail hx.not_mem), sum_prodSet xs hx.tail φ,
      sum_image_prodSet x.1 x.2 hp hord xs hx.tail hx.not_mem φ (sum_prodSet xs hx.tail)]

/-- Sums over any finite set of squarefree numbers with all prime factors in `xs` are at most `Fs xs φ`. -/
theorem sum_le_Fs (xs : List (ℕ × ℕ)) (hx : PList xs) (φ : ℕ → ℝ) (hφ : ∀ L, 0 ≤ φ L) (S : Finset ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ ∀ q ∈ m.primeFactors, q ∈ xs.map Prod.fst) :
    ∑ m ∈ S, fm m * φ (ordm m) ≤ Fs xs φ := by
  rw [← sum_prodSet xs hx φ]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm; exact mem_prodSet xs hx m (hS m hm).1 (hS m hm).2
  · intro m _ _; exact mul_nonneg (fm_nonneg m) (hφ _)

end Romanoff.M3
