import Romanoff.M3.Sums

/-!
# M3 soundness, part 5: the classes and `TBound`

For `S` (odd, squarefree, coprime to `ell`) split `m ∈ S` into
(a') all prime factors in the `gA` primes, (b') one `gB` prime `q` and `m / q` with all prime factors in the `gA` primes,
(c') the rest.  (a') `≤ Fs gA phic_c ≤ (T_a + prune)/SC`, (b') `≤ Σ_q f(q) Fs gA (phic_c ∘ lcm t_q) ≤ T_b / SC`,
(c') `≤ gcd(c, 120) Σ fm/ordm ≤ gcd(c, 120) R0tail` by `R0Bound` applied to (c') together with the disjoint sets
`prodSet (gA ++ gE)` and `q · prodSet (gA ++ gE)` (`q` in `gB`), whose sums are bounded below from the R0 table.
-/

namespace Romanoff.M3

open R45.M3

/-! ## The facts behind `certOK` -/

theorem certOK_spec (D : Data) (h : certOK D = true) :
    prattOK D.recs = true ∧ (∀ g ∈ D.groups, grpOK g = true) ∧
      primeOK (D.recs.map (·.n)) (D.groups.flatMap (·.ps)) = true ∧
      sortedLT (D.gA.map (·.t)) = true ∧ sortedLT (D.gE.map (·.t)) = true ∧ sortedLT (D.gB.map (·.1.t)) = true ∧
      (∀ g ∈ D.gE, g.t ∉ D.gA.map (·.t)) ∧ (∀ g ∈ D.gE, ∀ p ∈ g.ps, p ∈ ellPs) ∧
      (∀ g ∈ D.gA ++ D.gE, g.t ≤ 300) ∧ (∀ g ∈ D.gB, 300 < g.1.t ∧ g.1.t ≤ 1200) := by
  unfold certOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, List.all_eq_true.mp h2, h3, h4, h5, h6, fun g hg => ?_, fun g hg p hp => ?_, fun g hg => ?_,
    fun g hg => ?_⟩
  · have := List.all_eq_true.mp h7 g hg
    simpa using this
  · have := List.all_eq_true.mp (List.all_eq_true.mp h8 g hg) p hp
    simpa using this
  · have := List.all_eq_true.mp h9 g hg
    simpa using this
  · have := List.all_eq_true.mp h10 g hg
    simpa using this

/-- Every prime of every group: prime, `≥ 3`, of exact order `t`. -/
theorem groups_prime (D : Data) (h : certOK D = true) :
    ∀ g ∈ D.groups, ∀ p ∈ g.ps, p.Prime ∧ 3 ≤ p ∧ ordm p = g.t := by
  obtain ⟨hp, hg, hpr, -⟩ := certOK_spec D h
  intro g hgm p hpg
  have hprime : p.Prime := primeOK_sound D.recs hp _ hpr p (List.mem_flatMap.mpr ⟨g, hgm, hpg⟩)
  obtain ⟨_, _, _, _, hps⟩ := grpOK_spec g (hg g hgm)
  exact ⟨hprime, (hps p hpg).1, grp_ordm g (hg g hgm) p hpg hprime⟩

theorem groups_nodup (D : Data) (h : certOK D = true) : ∀ g ∈ D.groups, g.ps.Nodup := by
  obtain ⟨-, hg, -⟩ := certOK_spec D h
  intro g hgm
  obtain ⟨_, _, _, hs, _⟩ := grpOK_spec g (hg g hgm)
  exact sortedLT_nodup' _ hs

theorem groups_tpos (D : Data) (h : certOK D = true) : ∀ g ∈ D.groups, 1 ≤ g.t := by
  obtain ⟨-, hg, -⟩ := certOK_spec D h
  intro g hgm
  exact (grpOK_spec g (hg g hgm)).1

/-- A list of groups with distinct orders, all primes of exact order `t`, gives a `PList`. -/
theorem plist_flatG (gs : List Grp) (hpr : ∀ g ∈ gs, ∀ p ∈ g.ps, p.Prime ∧ 3 ≤ p ∧ ordm p = g.t)
    (hnd : ∀ g ∈ gs, g.ps.Nodup) (ht : (gs.map (·.t)).Nodup) : PList (flatG gs) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [flatG, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨g, hg, p, hp, rfl⟩ := hx
    exact hpr g hg p hp
  · have hmap : (flatG gs).map Prod.fst = gs.flatMap (·.ps) := by
      simp [flatG, List.map_flatMap, Function.comp_def]
    rw [hmap, List.nodup_flatMap]
    refine ⟨hnd, ?_⟩
    have hpw : gs.Pairwise (fun a b => a.t ≠ b.t) := List.pairwise_map.mp ht
    refine hpw.imp_of_mem (fun {a b} ha hb hab => ?_)
    intro p hpa hpb
    exact hab ((hpr a ha p hpa).2.2.symm.trans (hpr b hb p hpb).2.2)

/-! ## Odd squarefree products -/

theorem odd_of_primeFactors (m : ℕ) (hm : m ≠ 0) (h : ∀ q ∈ m.primeFactors, 3 ≤ q) : Odd m := by
  rw [Nat.odd_iff]
  by_contra h2
  have h2' : 2 ∣ m := by omega
  have := h 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2', hm⟩)
  omega

/-! ## Covering by a list of predicates -/

theorem sum_le_cover {α : Type*} (S : Finset ℕ) (L : List α) (P : α → ℕ → Prop) [∀ x, DecidablePred (P x)]
    (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) (hcov : ∀ m ∈ S, ∃ x ∈ L, P x m) :
    ∑ m ∈ S, g m ≤ (L.map fun x => ∑ m ∈ S.filter (P x), g m).sum := by
  induction L generalizing S with
  | nil =>
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun m hm => by simpa using hcov m hm)
    simp [this]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← Finset.sum_filter_add_sum_filter_not S (P x)]
    have h1 := ih (S.filter (fun m => ¬ P x m)) (by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨y, hy, hpy⟩ := hcov m hm.1
      rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd hpy hm.2
      · exact ⟨y, hy, hpy⟩)
    have h2 : (L.map fun y => ∑ m ∈ (S.filter fun m => ¬ P x m).filter (P y), g m).sum ≤
        (L.map fun y => ∑ m ∈ S.filter (P y), g m).sum := by
      apply List.sum_le_sum
      intro y _
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm; simp only [Finset.mem_filter] at hm ⊢; exact ⟨hm.1.1, hm.2⟩
      · intro m _ _; exact hg m
    linarith

/-! ## The main theorem -/

section
variable (D : Data) (hD : certOK D = true)

/-- The `gA` primes, the R0 primes `gA ++ gE`, the class-B pairs. -/
def PA : List (ℕ × ℕ) := flatG D.gA
def PR : List (ℕ × ℕ) := flatG (D.gA ++ D.gE)
def LB : List (ℕ × ℕ) := flatG (D.gB.map (·.1))

include hD

omit hD in
theorem groups_mem_A (g : Grp) (hg : g ∈ D.gA) : g ∈ D.groups := by
  simp [Data.groups, hg]

omit hD in
theorem groups_mem_E (g : Grp) (hg : g ∈ D.gE) : g ∈ D.groups := by
  simp [Data.groups, hg]

omit hD in
theorem groups_mem_B (g : Grp) (hg : g ∈ D.gB.map (·.1)) : g ∈ D.groups := by
  simp only [Data.groups, List.mem_append]; exact Or.inr hg

theorem nodup_tA : (D.gA.map (·.t)).Nodup := sortedLT_nodup' _ (certOK_spec D hD).2.2.2.1

theorem nodup_tAE : ((D.gA ++ D.gE).map (·.t)).Nodup := by
  obtain ⟨-, -, -, hsA, hsE, -, hEA, -⟩ := certOK_spec D hD
  rw [List.map_append, List.nodup_append]
  refine ⟨sortedLT_nodup' _ hsA, sortedLT_nodup' _ hsE, ?_⟩
  intro a ha b hb hab
  subst hab
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
  exact hEA g hg ha

theorem nodup_tB : ((D.gB.map (·.1)).map (·.t)).Nodup := by
  obtain ⟨-, -, -, -, -, hsB, -⟩ := certOK_spec D hD
  rw [List.map_map]
  exact sortedLT_nodup' _ hsB

theorem plist_PA : PList (PA D) :=
  plist_flatG _ (fun g hg => groups_prime D hD g (groups_mem_A D g hg))
    (fun g hg => groups_nodup D hD g (groups_mem_A D g hg)) (nodup_tA D hD)

theorem plist_PR : PList (PR D) := by
  refine plist_flatG _ (fun g hg => groups_prime D hD g ?_) (fun g hg => groups_nodup D hD g ?_) (nodup_tAE D hD)
  · rcases List.mem_append.mp hg with h | h
    · exact groups_mem_A D g h
    · exact groups_mem_E D g h
  · rcases List.mem_append.mp hg with h | h
    · exact groups_mem_A D g h
    · exact groups_mem_E D g h

theorem plist_LB : PList (LB D) :=
  plist_flatG _ (fun g hg => groups_prime D hD g (groups_mem_B D g hg))
    (fun g hg => groups_nodup D hD g (groups_mem_B D g hg)) (nodup_tB D hD)

/-- A class-B prime is not an R0 prime (orders `> 300` vs `≤ 300`). -/
theorem LB_not_PR (x : ℕ × ℕ) (hx : x ∈ LB D) : x.1 ∉ (PR D).map Prod.fst := by
  intro hmem
  obtain ⟨-, -, -, -, -, -, -, -, hT, hB⟩ := certOK_spec D hD
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
  have h1 := ((plist_PR D hD).1 y hy).2.2
  have h2 := ((plist_LB D hD).1 x hx).2.2
  simp only [PR, flatG, List.mem_flatMap, List.mem_map] at hy
  obtain ⟨g, hg, p, hp, rfl⟩ := hy
  simp only [LB, flatG, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨g', hg', q, hq, rfl⟩ := hx
  simp only at hyx h1 h2
  subst hyx
  obtain ⟨gx, hgx, rfl⟩ := hg'
  have := hT g hg
  have := (hB gx hgx).1
  omega

omit hD in
theorem PA_sub_PR (q : ℕ) (hq : q ∈ (PA D).map Prod.fst) : q ∈ (PR D).map Prod.fst := by
  simp only [PA, PR, flatG_append, List.map_append, List.mem_append]; exact Or.inl hq

/-- The `gE` primes divide `ell`. -/
theorem PR_ell (q : ℕ) (hq : q ∈ (PR D).map Prod.fst) (hn : q ∉ (PA D).map Prod.fst) : q ∣ ell := by
  obtain ⟨-, -, -, -, -, -, -, hE, -⟩ := certOK_spec D hD
  simp only [PR, PA, flatG_append, List.map_append, List.mem_append] at hq
  rcases hq with hq | hq
  · exact absurd hq hn
  · simp only [flatG, List.mem_map, List.mem_flatMap] at hq
    obtain ⟨_, ⟨g, hg, p, hp, rfl⟩, rfl⟩ := hq
    have := hE g hg p hp
    simp only [ellPs, List.mem_cons, List.not_mem_nil, or_false] at this
    unfold ell ellPrimes
    dsimp only
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end

end Romanoff.M3
