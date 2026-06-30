import Linglib.Core.Order.ComparativeProbability.Systems
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

/-!
# Representability of Epistemic Systems

[kraft-pratt-seidenberg-1959] [holliday-icard-2013]

FA systems on small domains (|W| ≤ 4) are representable by finitely additive
probability measures (**Theorem 8a**, [kraft-pratt-seidenberg-1959]).
For every |W| ≥ 5 this fails: padding the KPS counterexample with null atoms
gives a non-representable FA system at each cardinality (**Theorem 8b**).

## Contents

1. **`Representable`**: the representability predicate.
2. **KPS counterexample** (Fin 5): non-representable FA system (`kpsSystemFA`,
   `kps_not_representable`); null-atom padding (`padFA`,
   `exists_nonrepresentable_fin`) extends it to every `Fin n` with `n ≥ 5`.
3. **Shared infrastructure**: injection pullback (`comapFA`), null element
   reduction (`null_elem_reduce`), transport/permutation (`transportFA`,
   `perm_repr`)
4. **Small-cardinality proofs**: Fin 0 (`no_fa_empty`), Fin 1
   (`representable_fin1`), Fin 2 (`representable_fin2`).  Fin 3 and Fin 4 are
   derived from Scott cancellation in `CancellationFin4.lean`
   (`representable_fin3`, `representable_fin4`).
-/

namespace ComparativeProbability

/-- An FA system is **representable** when some finitely additive probability
    measure induces exactly its comparison relation. -/
def Representable {W : Type*} (sys : EpistemicSystemFA W) : Prop :=
  ∃ m : FinAddMeasure W, ∀ A B, sys.ge A B ↔ m.inducedGe A B

-- ── KPS Counterexample Infrastructure ──────────────

/-- Convert a Finset (Fin 5) to a bitmask index. -/
private def finsetIdx (s : Finset (Fin 5)) : ℕ :=
  s.sum (λ i => 2 ^ i.val)

/-- The KPS rank table: maps bitmask index to rank (0–31).
    Ordering from [kraft-pratt-seidenberg-1959], Section 4.
    Elements: p=0, q=1, r=2, s=3, t=4.
    ∅ < q < r < s < qr < qs < p < pq < rs < t < qrs < rp < ps < tq < qrp < rt
    and complements in reverse (by supplementation, from axiom A). -/
private def kpsRankNat (idx : ℕ) : ℕ :=
  match idx with
  |  0 =>  0 |  1 =>  6 |  2 =>  1 |  3 =>  7
  |  4 =>  2 |  5 => 11 |  6 =>  4 |  7 => 14
  |  8 =>  3 |  9 => 12 | 10 =>  5 | 11 => 16
  | 12 =>  8 | 13 => 18 | 14 => 10 | 15 => 22
  | 16 =>  9 | 17 => 21 | 18 => 13 | 19 => 23
  | 20 => 15 | 21 => 26 | 22 => 19 | 23 => 28
  | 24 => 17 | 25 => 27 | 26 => 20 | 27 => 29
  | 28 => 24 | 29 => 30 | 30 => 25 | 31 => 31
  |  _ =>  0

/-- KPS rank of a finset. -/
private def kpsRank (s : Finset (Fin 5)) : ℕ :=
  kpsRankNat (finsetIdx s)

private theorem kps_mono_finset :
    ∀ (a b : Finset (Fin 5)), a ⊆ b → kpsRank b ≥ kpsRank a := by
  decide

private theorem kps_additive_finset :
    ∀ (a b : Finset (Fin 5)),
      (kpsRank a ≥ kpsRank b) ↔ (kpsRank (a \ b) ≥ kpsRank (b \ a)) := by
  decide

private theorem kps_bottom_finset :
    kpsRank Finset.univ ≥ kpsRank ∅ := by decide

section KPSSystem

attribute [local instance] Classical.propDecidable

private noncomputable def toFS (A : Set (Fin 5)) : Finset (Fin 5) :=
  Finset.univ.filter (λ x => x ∈ A)

private theorem toFS_mem (A : Set (Fin 5)) (x : Fin 5) :
    x ∈ toFS A ↔ x ∈ A := by
  simp only [toFS, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem toFS_univ : toFS (Set.univ : Set (Fin 5)) = Finset.univ := by
  ext x; simp only [toFS_mem, Set.mem_univ, Finset.mem_univ]

private theorem toFS_empty : toFS (∅ : Set (Fin 5)) = ∅ := by
  ext x; simp [toFS_mem]

private theorem toFS_diff (A B : Set (Fin 5)) :
    toFS (A \ B) = toFS A \ toFS B := by
  ext x; simp only [toFS_mem, Set.mem_diff, Finset.mem_sdiff]

private theorem toFS_subset (A B : Set (Fin 5)) :
    A ⊆ B ↔ toFS A ⊆ toFS B :=
  ⟨fun h x hx => by rw [toFS_mem] at hx ⊢; exact h hx,
   fun h x hx => (toFS_mem B x).mp (h ((toFS_mem A x).mpr hx))⟩

private noncomputable def kpsRankSet (A : Set (Fin 5)) : ℕ := kpsRank (toFS A)
private noncomputable def kpsGe (A B : Set (Fin 5)) : Prop := kpsRankSet A ≥ kpsRankSet B

noncomputable def kpsSystemFA : EpistemicSystemFA (Fin 5) where
  ge := kpsGe
  refl := λ A => le_refl (kpsRankSet A)
  mono := λ {A B} hAB => kps_mono_finset _ _ ((toFS_subset A B).mp hAB)
  bottom := by
    simp only [EpistemicAxiom.Bot, kpsGe, kpsRankSet, toFS_univ, toFS_empty]
    exact kps_bottom_finset
  nonTrivial := by
    simp only [EpistemicAxiom.BT, kpsGe, kpsRankSet, toFS_univ, toFS_empty]; decide
  total := λ A B => le_total (kpsRankSet B) (kpsRankSet A)
  trans := λ {_ _ _} hab hbc => le_trans hbc hab
  additive A B := by
    show kpsRank (toFS A) ≥ kpsRank (toFS B) ↔
         kpsRank (toFS (A \ B)) ≥ kpsRank (toFS (B \ A))
    rw [toFS_diff, toFS_diff]; exact kps_additive_finset (toFS A) (toFS B)

private theorem mu_pair (m : FinAddMeasure (Fin 5)) (a b : Fin 5) (hab : a ≠ b) :
    m.mu ({a, b} : Set (Fin 5)) = m.mu {a} + m.mu {b} := by
  rw [Set.insert_eq a {b}, m.additive {a} {b} (Set.disjoint_singleton.mpr hab)]

private theorem mu_triple (m : FinAddMeasure (Fin 5)) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    m.mu ({a, b, c} : Set (Fin 5)) = m.mu {a} + m.mu {b} + m.mu {c} := by
  rw [Set.insert_eq a ({b, c} : Set (Fin 5)), m.additive {a} {b, c}
    (Set.disjoint_left.mpr fun x hx hxbc => by
      rw [Set.mem_singleton_iff] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxbc
      subst hx; rcases hxbc with rfl | rfl
      exacts [absurd rfl hab, absurd rfl hac]),
    mu_pair m b c hbc, add_assoc]

theorem kps_not_representable : ¬Representable kpsSystemFA := by
  intro ⟨m, hm⟩
  set P := m.mu ({(0 : Fin 5)} : Set (Fin 5))
  set Q := m.mu ({(1 : Fin 5)} : Set (Fin 5))
  set R := m.mu ({(2 : Fin 5)} : Set (Fin 5))
  set S := m.mu ({(3 : Fin 5)} : Set (Fin 5))
  set T := m.mu ({(4 : Fin 5)} : Set (Fin 5))
  -- Ordering facts: three strict (rank <), one weak (rank ≥)
  have hord1 : ¬ kpsGe ({1, 3} : Set (Fin 5)) {0} := by
    unfold kpsGe kpsRankSet
    rw [show toFS ({1, 3} : Set (Fin 5)) = {1, 3} by ext x; simp [toFS_mem],
        show toFS ({(0 : Fin 5)} : Set (Fin 5)) = {0} by ext x; simp [toFS_mem]]; decide
  have hord2 : ¬ kpsGe ({0, 1} : Set (Fin 5)) {2, 3} := by
    unfold kpsGe kpsRankSet
    rw [show toFS ({0, 1} : Set (Fin 5)) = {0, 1} by ext x; simp [toFS_mem],
        show toFS ({2, 3} : Set (Fin 5)) = {2, 3} by ext x; simp [toFS_mem]]; decide
  have hord3 : ¬ kpsGe ({0, 3} : Set (Fin 5)) {1, 4} := by
    unfold kpsGe kpsRankSet
    rw [show toFS ({0, 3} : Set (Fin 5)) = {0, 3} by ext x; simp [toFS_mem],
        show toFS ({1, 4} : Set (Fin 5)) = {1, 4} by ext x; simp [toFS_mem]]; decide
  have hord4 : kpsGe ({0, 1, 3} : Set (Fin 5)) {2, 4} := by
    unfold kpsGe kpsRankSet
    rw [show toFS ({0, 1, 3} : Set (Fin 5)) = {0, 1, 3} by ext x; simp [toFS_mem],
        show toFS ({2, 4} : Set (Fin 5)) = {2, 4} by ext x; simp [toFS_mem]]; decide
  -- Convert to measure inequalities via the representation isomorphism
  have hmeas1 : m.mu ({1, 3} : Set _) < m.mu ({(0 : Fin 5)} : Set _) :=
    not_le.mp (λ h => hord1 ((hm _ _).mpr h))
  have hmeas2 : m.mu ({0, 1} : Set _) < m.mu ({2, 3} : Set _) :=
    not_le.mp (λ h => hord2 ((hm _ _).mpr h))
  have hmeas3 : m.mu ({0, 3} : Set _) < m.mu ({1, 4} : Set _) :=
    not_le.mp (λ h => hord3 ((hm _ _).mpr h))
  have hmeas4 : m.mu ({0, 1, 3} : Set _) ≥ m.mu ({2, 4} : Set _) :=
    (hm _ _).mp hord4
  -- Decompose pairs/triples using finite additivity
  rw [mu_pair m 1 3 (by decide)] at hmeas1
  rw [mu_pair m 0 1 (by decide), mu_pair m 2 3 (by decide)] at hmeas2
  rw [mu_pair m 0 3 (by decide), mu_pair m 1 4 (by decide)] at hmeas3
  rw [mu_triple m 0 1 3 (by decide) (by decide) (by decide),
      mu_pair m 2 4 (by decide)] at hmeas4
  -- hmeas1: Q + S < P      hmeas2: P + Q < R + S
  -- hmeas3: P + S < Q + T   hmeas4: P + Q + S ≥ R + T
  -- Summing the three strict inequalities (Scott cancellation):
  --   (Q+S) + (P+Q) + (P+S) < P + (R+S) + (Q+T)
  --   P + Q + S < R + T
  -- contradicts hmeas4.
  linarith

end KPSSystem


-- ── Theorem 8a: Per-cardinality proofs ──────────

attribute [local instance] Classical.propDecidable

-- ── Reduction Lemma ────────────────────────────────

/-- Agreement on disjoint pairs suffices for full representability (Axiom A
    reduces every comparison to a disjoint one). -/
theorem reduce_to_disjoint {W : Type*} (sys : EpistemicSystemFA W)
    (m : FinAddMeasure W)
    (h : ∀ C D : Set W, Disjoint C D → (sys.ge C D ↔ m.inducedGe C D)) :
    ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  intro A B
  rw [sys.additive A B]
  exact (h _ _ disjoint_sdiff_sdiff).trans (m.mu_qadd A B).symm

-- ── Null element reduction ────────────────────────────

/-- Removing a null element (`sys.ge ∅ {j}`) from both sides of a disjoint
    comparison preserves `ge`. -/
theorem null_removal_disjoint {W : Type*} (sys : EpistemicSystemFA W)
    (j : W) (hj : sys.ge ∅ {j})
    (C D : Set W) (hdisj : Disjoint C D) :
    sys.ge C D ↔ sys.ge (C \ {j}) (D \ {j}) := by
  have null_sub : ∀ S : Set W, sys.ge (S \ {j}) S := by
    intro S
    by_cases hj_in : j ∈ S
    · rw [sys.additive (S \ {j}) S,
        show (S \ {j}) \ S = ∅ by
          ext x; simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false]; tauto,
        show S \ (S \ {j}) = {j} by
          ext x; simp only [Set.mem_diff, Set.mem_singleton_iff]
          exact ⟨fun ⟨hx, hn⟩ => by by_contra hne; exact hn ⟨hx, hne⟩,
            by rintro rfl; exact ⟨hj_in, fun ⟨_, h⟩ => h rfl⟩⟩]
      exact hj
    · rw [Set.diff_singleton_eq_self hj_in]; exact sys.refl S
  by_cases hjC : j ∈ C
  · have hjnD : j ∉ D := Set.disjoint_left.mp hdisj hjC
    rw [Set.diff_singleton_eq_self hjnD]
    exact ⟨fun h => sys.trans _ _ _ (null_sub C) h,
           fun h => sys.trans _ _ _ (sys.mono _ _ Set.diff_subset) h⟩
  · rw [Set.diff_singleton_eq_self hjC]
    by_cases hjD : j ∈ D
    · exact ⟨fun h => sys.trans _ _ _ h (sys.mono _ _ Set.diff_subset),
             fun h => sys.trans _ _ _ h (null_sub D)⟩
    · rw [Set.diff_singleton_eq_self hjD]

/-- `Fin.succ '' (Fin.succ ⁻¹' S) = S \ {0}` for `S : Set (Fin (n+1))`. -/
private theorem succ_image_preimage {n : ℕ} (S : Set (Fin (n + 1))) :
    Fin.succ '' (Fin.succ ⁻¹' S) = S \ {(0 : Fin (n + 1))} := by
  rw [Set.image_preimage_eq_range_inter, Fin.range_succ]
  ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_diff]; exact And.comm

/-- Pull back an FA system along an injection: `α`-propositions compare via their
    images. Non-triviality requires a witness and must be supplied. -/
def comapFA {α W : Type*} (f : α → W) (hf : Function.Injective f)
    (sys : EpistemicSystemFA W) (hnt : ¬sys.ge ∅ (Set.range f)) :
    EpistemicSystemFA α where
  ge A B := sys.ge (f '' A) (f '' B)
  refl _ := sys.refl _
  mono _ _ hAB := sys.mono _ _ (Set.image_mono hAB)
  bottom := by
    show sys.ge (f '' Set.univ) (f '' ∅)
    rw [Set.image_empty]; exact sys.mono _ _ (Set.empty_subset _)
  nonTrivial := by
    show ¬sys.ge (f '' ∅) (f '' Set.univ)
    rwa [Set.image_empty, Set.image_univ]
  total _ _ := sys.total _ _
  trans _ _ _ h1 h2 := sys.trans _ _ _ h1 h2
  additive A B := by
    show sys.ge (f '' A) (f '' B) ↔ sys.ge (f '' (A \ B)) (f '' (B \ A))
    rw [Set.image_diff hf, Set.image_diff hf]; exact sys.additive _ _

/-- Null element reduction: if atom 0 is null in an FA system on `Fin (n+2)` and
    some atom is not, representability reduces along `Fin.succ` to `Fin (n+1)`. -/
theorem null_elem_reduce {n : ℕ} (sys : EpistemicSystemFA (Fin (n + 2)))
    (hn0 : sys.ge ∅ {(0 : Fin (n + 2))})
    (hnn : ∃ i : Fin (n + 1), ¬sys.ge ∅ {Fin.succ i})
    (sub_repr : ∀ sys' : EpistemicSystemFA (Fin (n + 1)), Representable sys') :
    Representable sys := by
  have hnt : ¬sys.ge ∅ (Set.range (Fin.succ : Fin (n + 1) → Fin (n + 2))) := by
    obtain ⟨i, hi⟩ := hnn
    exact fun h => hi (sys.trans _ _ _ h
      (sys.mono _ _ (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)))
  obtain ⟨m_r, hm_r⟩ := sub_repr (comapFA Fin.succ (Fin.succ_injective _) sys hnt)
  -- lift the sub-measure (the null element gets weight 0)
  refine ⟨{
    mu := fun A => m_r.mu (Fin.succ ⁻¹' A)
    nonneg := fun A => m_r.nonneg _
    additive := fun A B hdisj => by
      rw [Set.preimage_union]; exact m_r.additive _ _ (hdisj.preimage _)
    total := by rw [Set.preimage_univ]; exact m_r.total
  }, reduce_to_disjoint sys _ (fun C D hdisj => ?_)⟩
  rw [null_removal_disjoint sys 0 hn0 C D hdisj,
      ← succ_image_preimage C, ← succ_image_preimage D]
  exact hm_r (Fin.succ ⁻¹' C) (Fin.succ ⁻¹' D)

-- ── Card 0: impossible ─────────────────────────────

theorem no_fa_empty (sys : EpistemicSystemFA (Fin 0)) : False := by
  have : (∅ : Set (Fin 0)) = Set.univ := by ext x; exact Fin.elim0 x
  exact sys.nonTrivial (this ▸ sys.refl ∅)

-- ── Card 1 ─────────────────────────────────────────

private theorem set_fin1_eq (A : Set (Fin 1)) : A = ∅ ∨ A = Set.univ := by
  by_cases h : (0 : Fin 1) ∈ A
  · right; ext x; simp [Fin.eq_zero x, h]
  · left; ext x; exact ⟨fun hx => absurd (Fin.eq_zero x ▸ hx) h, fun hx => hx.elim⟩

private noncomputable def measure_fin1 : FinAddMeasure (Fin 1) where
  mu := fun A => if (0 : Fin 1) ∈ A then 1 else 0
  nonneg := fun A => by split <;> norm_num
  additive := fun A B hdisj => by
    by_cases h0A : (0 : Fin 1) ∈ A <;> by_cases h0B : (0 : Fin 1) ∈ B
    · exact absurd h0B (Set.disjoint_left.mp hdisj h0A)
    · simp [Set.mem_union, h0A, h0B]
    · simp [Set.mem_union, h0A, h0B]
    · simp [h0A, h0B, show (0 : Fin 1) ∉ A ∪ B from fun h => h.elim h0A h0B]
  total := by simp [Set.mem_univ]

theorem representable_fin1 (sys : EpistemicSystemFA (Fin 1)) : Representable sys := by
  refine ⟨measure_fin1, fun A B => ?_⟩
  rcases set_fin1_eq A with rfl | rfl <;> rcases set_fin1_eq B with rfl | rfl
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
  · exact ⟨fun h => absurd h sys.nonTrivial,
          fun h => by simp [FinAddMeasure.inducedGe, measure_fin1, Set.mem_univ] at h; linarith⟩
  · exact ⟨fun _ => by simp [FinAddMeasure.inducedGe, measure_fin1, Set.mem_univ],
          fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩

-- ── Card 2: Infrastructure ──────────────────────────

private noncomputable def measure_fin2 (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    FinAddMeasure (Fin 2) where
  mu := fun A =>
    (if (0 : Fin 2) ∈ A then a else 0) + (if (1 : Fin 2) ∈ A then 1 - a else 0)
  nonneg := fun A => add_nonneg (by split <;> [exact ha; exact le_refl _])
    (by split <;> [linarith; exact le_refl _])
  additive := fun A B hdisj => by
    have hd : ∀ x ∈ A, x ∉ B := fun x hx => Set.disjoint_left.mp hdisj hx
    simp only [Set.mem_union]
    by_cases h0A : (0 : Fin 2) ∈ A <;> by_cases h0B : (0 : Fin 2) ∈ B <;>
    by_cases h1A : (1 : Fin 2) ∈ A <;> by_cases h1B : (1 : Fin 2) ∈ B <;>
    simp_all
  total := by simp only [Set.mem_univ, ite_true]; linarith

private theorem measure_fin2_mu (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (A : Set (Fin 2)) :
    (measure_fin2 a ha ha1).mu A =
    (if (0 : Fin 2) ∈ A then a else 0) + (if (1 : Fin 2) ∈ A then 1 - a else 0) := rfl

private theorem mf2_empty (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu ∅ = 0 := by
  rw [measure_fin2_mu]; simp

private theorem mf2_zero (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu {(0 : Fin 2)} = a := by
  rw [measure_fin2_mu, if_pos (show (0 : Fin 2) ∈ ({(0 : Fin 2)} : Set _) from rfl),
    if_neg (show (1 : Fin 2) ∉ ({(0 : Fin 2)} : Set _) by
      simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega))]
  linarith

private theorem mf2_one (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu {(1 : Fin 2)} = 1 - a := by
  rw [measure_fin2_mu, if_neg (show (0 : Fin 2) ∉ ({(1 : Fin 2)} : Set _) by
      simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)),
    if_pos (show (1 : Fin 2) ∈ ({(1 : Fin 2)} : Set _) from rfl)]
  linarith

private theorem mf2_univ (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu (Set.univ : Set (Fin 2)) = 1 := by
  rw [measure_fin2_mu]; simp only [Set.mem_univ, ite_true]; linarith

private theorem set_fin2_eq (A : Set (Fin 2)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Set.univ := by
  by_cases h0 : (0 : Fin 2) ∈ A <;> by_cases h1 : (1 : Fin 2) ∈ A
  · right; right; right; ext x; fin_cases x <;> simp_all
  · right; left; ext x; fin_cases x <;> simp_all
  · right; right; left; ext x; fin_cases x <;> simp_all
  · left; ext x; fin_cases x <;> simp_all

private theorem not_both_null_fin2 (sys : EpistemicSystemFA (Fin 2)) :
    ¬(sys.ge ∅ {0} ∧ sys.ge ∅ {1}) := by
  intro ⟨h0, h1⟩
  have hd1 : ({(0 : Fin 2)} : Set _) \ Set.univ = ∅ := by ext x; simp
  have hd2 : Set.univ \ ({(0 : Fin 2)} : Set _) = {(1 : Fin 2)} := by
    ext x; simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, Fin.ext_iff]
    omega
  exact sys.nonTrivial (sys.trans _ _ _ h0
    ((sys.additive {0} Set.univ).mpr (hd1 ▸ hd2 ▸ h1)))

-- ── Card 2: Helper for disjoint-pair dispatch ────────

/-- Given measure values and ordering facts, close all 16 disjoint-pair cases on Fin 2.
    The 7 non-disjoint pairs close by exfalso.
    The 5 uniform pairs (∅/∅, X/∅, ∅/univ) are independent of the ordering.
    The 4 critical pairs (∅/{0}, ∅/{1}, {0}/{1}, {1}/{0}) use the hypotheses. -/
private theorem fin2_dispatch (sys : EpistemicSystemFA (Fin 2))
    (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hme : (measure_fin2 a ha ha1).mu ∅ = 0)
    (hm0 : (measure_fin2 a ha ha1).mu {(0 : Fin 2)} = a)
    (hm1 : (measure_fin2 a ha ha1).mu {(1 : Fin 2)} = 1 - a)
    (hmu : (measure_fin2 a ha ha1).mu (Set.univ : Set (Fin 2)) = 1)
    -- Ordering hypotheses matching measure values
    (he0 : sys.ge ∅ {(0 : Fin 2)} ↔ a ≤ 0)
    (he1 : sys.ge ∅ {(1 : Fin 2)} ↔ 1 - a ≤ 0)
    (h01 : sys.ge {(0 : Fin 2)} {1} ↔ a ≥ 1 - a)
    (h10 : sys.ge {(1 : Fin 2)} {0} ↔ 1 - a ≥ a)
    :
    ∀ C D : Set (Fin 2), Disjoint C D →
      (sys.ge C D ↔ (measure_fin2 a ha ha1).inducedGe C D) := by
  intro C D hCD
  have hdisj : ∀ x ∈ C, x ∉ D := fun x hx => Set.disjoint_left.mp hCD hx
  rcases set_fin2_eq C with rfl | rfl | rfl | rfl <;>
  rcases set_fin2_eq D with rfl | rfl | rfl | rfl
  -- ∅ vs ∅
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
  -- ∅ vs {0}
  · show sys.ge ∅ {0} ↔ _ ≥ _; rw [hme, hm0]; exact he0
  -- ∅ vs {1}
  · show sys.ge ∅ {1} ↔ _ ≥ _; rw [hme, hm1]
    exact ⟨fun h => by linarith [he1.mp h], fun h => he1.mpr (by linarith)⟩
  -- ∅ vs univ
  · show sys.ge ∅ Set.univ ↔ _ ≥ _; rw [hme, hmu]
    exact ⟨fun h => absurd h sys.nonTrivial, fun h => by linarith⟩
  -- {0} vs ∅
  · show sys.ge {0} ∅ ↔ _ ≥ _; rw [hm0, hme]
    exact ⟨fun _ => ha, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  -- {0} vs {0}: not disjoint
  · exact (hdisj 0 rfl rfl).elim
  -- {0} vs {1}
  · show sys.ge {0} {1} ↔ _ ≥ _; rw [hm0, hm1]; exact h01
  -- {0} vs univ: not disjoint
  · exact (hdisj 0 rfl (Set.mem_univ _)).elim
  -- {1} vs ∅
  · show sys.ge {1} ∅ ↔ _ ≥ _; rw [hm1, hme]
    exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  -- {1} vs {0}
  · show sys.ge {1} {0} ↔ _ ≥ _; rw [hm1, hm0]; exact h10
  -- {1} vs {1}: not disjoint
  · exact (hdisj 1 rfl rfl).elim
  -- {1} vs univ: not disjoint
  · exact (hdisj 1 rfl (Set.mem_univ _)).elim
  -- univ vs ∅
  · show sys.ge Set.univ ∅ ↔ _ ≥ _; rw [hmu, hme]
    exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  -- univ vs {0}: not disjoint
  · exact (hdisj 0 (Set.mem_univ _) rfl).elim
  -- univ vs {1}: not disjoint
  · exact (hdisj 1 (Set.mem_univ _) rfl).elim
  -- univ vs univ: not disjoint
  · exact (hdisj 0 (Set.mem_univ _) (Set.mem_univ _)).elim

-- ── Card 2: Main theorem ───────────────────────────

theorem representable_fin2 (sys : EpistemicSystemFA (Fin 2)) : Representable sys := by
  by_cases h_null0 : sys.ge ∅ {(0 : Fin 2)}
  · -- Case 1: ge ∅ {0} → a = 0
    have h_nnull1 : ¬sys.ge ∅ {(1 : Fin 2)} := fun h => not_both_null_fin2 sys ⟨h_null0, h⟩
    have h_nge01 : ¬sys.ge {(0 : Fin 2)} {1} :=
      fun h => not_both_null_fin2 sys ⟨h_null0, sys.trans _ _ _ h_null0 h⟩
    have h_ge10 : sys.ge {(1 : Fin 2)} {0} :=
      (sys.total {(1 : Fin 2)} {0}).resolve_right h_nge01
    refine ⟨measure_fin2 0 le_rfl zero_le_one,
      reduce_to_disjoint sys _ (fin2_dispatch sys 0 le_rfl zero_le_one
        (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
        ⟨fun _ => le_refl _, fun _ => h_null0⟩
        ⟨fun h => absurd h h_nnull1, fun h => by linarith⟩
        ⟨fun h => absurd h h_nge01, fun h => by linarith⟩
        ⟨fun _ => by linarith, fun _ => h_ge10⟩)⟩
  · by_cases h_null1 : sys.ge ∅ {(1 : Fin 2)}
    · -- Case 2: ge ∅ {1} → a = 1
      have h_nge10 : ¬sys.ge {(1 : Fin 2)} {0} :=
        fun h => not_both_null_fin2 sys ⟨sys.trans _ _ _ h_null1 h, h_null1⟩
      have h_ge01 : sys.ge {(0 : Fin 2)} {1} :=
        (sys.total {(0 : Fin 2)} {1}).resolve_right h_nge10
      refine ⟨measure_fin2 1 zero_le_one le_rfl,
        reduce_to_disjoint sys _ (fin2_dispatch sys 1 zero_le_one le_rfl
          (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
          ⟨fun h => absurd h h_null0, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h_null1⟩
          ⟨fun _ => by linarith, fun _ => h_ge01⟩
          ⟨fun h => absurd h h_nge10, fun h => by linarith⟩)⟩
    · -- Neither null: both singletons are "positive"
      by_cases h01 : sys.ge {(0 : Fin 2)} {1}
      · by_cases h10 : sys.ge {(1 : Fin 2)} {0}
        · -- Case 3c: ge {0} {1} ∧ ge {1} {0} → a = 1/2
          refine ⟨measure_fin2 (1/2) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin2_dispatch sys (1/2) (by linarith) (by linarith)
              (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
              ⟨fun h => absurd h h_null0, fun h => by linarith⟩
              ⟨fun h => absurd h h_null1, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun _ => by linarith, fun _ => h10⟩)⟩
        · -- Case 3a: ge {0} {1} ∧ ¬ge {1} {0} → a = 2/3
          refine ⟨measure_fin2 (2/3) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin2_dispatch sys (2/3) (by linarith) (by linarith)
              (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
              ⟨fun h => absurd h h_null0, fun h => by linarith⟩
              ⟨fun h => absurd h h_null1, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h h10, fun h => by linarith⟩)⟩
      · -- Case 3b: ¬ge {0} {1} → ge {1} {0} (totality), a = 1/3
        have h10 : sys.ge {(1 : Fin 2)} {0} :=
          (sys.total {(1 : Fin 2)} {0}).resolve_right h01
        refine ⟨measure_fin2 (1/3) (by linarith) (by linarith),
          reduce_to_disjoint sys _ (fin2_dispatch sys (1/3) (by linarith) (by linarith)
            (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
            ⟨fun h => absurd h h_null0, fun h => by linarith⟩
            ⟨fun h => absurd h h_null1, fun h => by linarith⟩
            ⟨fun h => absurd h h01, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h10⟩)⟩

-- ── Transport + Permutation infrastructure ────────────

def transportFA {W α : Type*} (e : W ≃ α)
    (sys : EpistemicSystemFA W) : EpistemicSystemFA α :=
  comapFA e.symm e.symm.injective sys
    (by rw [Equiv.range_eq_univ]; exact sys.nonTrivial)

def transportMeasure {W α : Type*}
    (e : W ≃ α) (m : FinAddMeasure α) : FinAddMeasure W where
  mu := fun A => m.mu (e '' A)
  nonneg := fun A => m.nonneg _
  additive := fun A B hdisj => by
    rw [Set.image_union]; exact m.additive _ _ ((Set.disjoint_image_iff e.injective).mpr hdisj)
  total := by rw [Set.image_univ_of_surjective e.surjective]; exact m.total

theorem transfer_repr {W α : Type*}
    (e : W ≃ α) (sys : EpistemicSystemFA W) (m : FinAddMeasure α)
    (hm : ∀ A B : Set α, (transportFA e sys).ge A B ↔ m.inducedGe A B) :
    ∀ A B : Set W, sys.ge A B ↔ (transportMeasure e m).inducedGe A B := by
  intro A B
  have h := hm (e '' A) (e '' B)
  simpa only [transportFA, comapFA, Equiv.symm_image_image, transportMeasure,
    FinAddMeasure.inducedGe] using h

/-- Null pattern transport: j is null in `transportFA σ sys` iff `σ.symm j` is null in `sys`. -/
theorem perm_null_iff {n : ℕ} (σ : Fin n ≃ Fin n)
    (sys : EpistemicSystemFA (Fin n)) (j : Fin n) :
    (transportFA σ sys).ge ∅ {j} ↔ sys.ge ∅ {σ.symm j} := by
  show sys.ge (σ.symm '' ∅) (σ.symm '' {j}) ↔ sys.ge ∅ {σ.symm j}
  simp only [Set.image_empty, Set.image_singleton]

/-- Representability transports backward along any equivalence. -/
theorem perm_repr {W α : Type*} (σ : W ≃ α) (sys : EpistemicSystemFA W)
    (h : Representable (transportFA σ sys)) : Representable sys := by
  obtain ⟨m, hm⟩ := h
  exact ⟨transportMeasure σ m, transfer_repr σ sys m hm⟩

-- ── Null-atom padding: Theorem 8b at every cardinality ≥ 5 ──

/-- Pad an FA system with one null atom: comparisons on `Fin (n + 1)` are decided
    by the preimage restriction to the first `n` atoms. -/
def padFA {n : ℕ} (sys : EpistemicSystemFA (Fin n)) : EpistemicSystemFA (Fin (n + 1)) where
  ge A B := sys.ge (Fin.castSucc ⁻¹' A) (Fin.castSucc ⁻¹' B)
  refl _ := sys.refl _
  mono _ _ hAB := sys.mono _ _ (Set.preimage_mono hAB)
  bottom := by
    show sys.ge (Fin.castSucc ⁻¹' Set.univ) (Fin.castSucc ⁻¹' ∅)
    rw [Set.preimage_univ, Set.preimage_empty]; exact sys.bottom
  nonTrivial := by
    show ¬sys.ge (Fin.castSucc ⁻¹' ∅) (Fin.castSucc ⁻¹' Set.univ)
    rw [Set.preimage_univ, Set.preimage_empty]; exact sys.nonTrivial
  total _ _ := sys.total _ _
  trans _ _ _ h1 h2 := sys.trans _ _ _ h1 h2
  additive A B := by
    show sys.ge _ _ ↔ sys.ge _ _
    rw [Set.preimage_diff, Set.preimage_diff]; exact sys.additive _ _

/-- The padded atom is null. -/
theorem padFA_last_null {n : ℕ} (sys : EpistemicSystemFA (Fin n)) :
    (padFA sys).ge ∅ {Fin.last n} := by
  show sys.ge (Fin.castSucc ⁻¹' ∅) (Fin.castSucc ⁻¹' {Fin.last n})
  rw [Set.preimage_empty, show Fin.castSucc ⁻¹' {Fin.last n} = (∅ : Set (Fin n)) from
    Set.eq_empty_of_forall_notMem fun i hi => (Fin.castSucc_lt_last i).ne hi]; exact sys.refl ∅

/-- Padding reflects representability: a measure for `padFA sys` assigns the
    padded atom measure zero, so its `Fin.castSucc`-image restriction represents
    `sys`. -/
theorem representable_of_padFA {n : ℕ} {sys : EpistemicSystemFA (Fin n)}
    (h : Representable (padFA sys)) : Representable sys := by
  obtain ⟨m, hm⟩ := h
  have hinj := Fin.castSucc_injective n
  have hlast : m.mu {Fin.last n} = 0 := by
    have h0 : m.mu ∅ ≥ m.mu {Fin.last n} := (hm _ _).mp (padFA_last_null sys)
    rw [m.mu_empty] at h0; linarith [m.nonneg {Fin.last n}]
  have hcover : Fin.castSucc '' (Set.univ : Set (Fin n)) ∪ {Fin.last n} = Set.univ := by
    rw [Set.image_univ]
    ext i
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr rfl
  have hdisj : Disjoint (Fin.castSucc '' (Set.univ : Set (Fin n))) {Fin.last n} :=
    Set.disjoint_singleton_right.mpr fun ⟨i, _, hi⟩ => (Fin.castSucc_lt_last i).ne hi
  have htotal : m.mu (Fin.castSucc '' (Set.univ : Set (Fin n))) = 1 := by
    have := m.additive _ _ hdisj
    rw [hcover, m.total, hlast, add_zero] at this; linarith
  refine ⟨{
    mu := fun A => m.mu (Fin.castSucc '' A)
    nonneg := fun A => m.nonneg _
    additive := fun A B hd => by
      rw [Set.image_union]; exact m.additive _ _ ((Set.disjoint_image_iff hinj).mpr hd)
    total := htotal
  }, fun A B => ?_⟩
  have key := hm (Fin.castSucc '' A) (Fin.castSucc '' B)
  rwa [show (padFA sys).ge (Fin.castSucc '' A) (Fin.castSucc '' B) ↔ sys.ge A B from by
    show sys.ge (Fin.castSucc ⁻¹' (Fin.castSucc '' A)) _ ↔ _
    rw [Set.preimage_image_eq A hinj, Set.preimage_image_eq B hinj]] at key

/-- **Theorem 8b at every cardinality**: for `n ≥ 5` there is a non-representable
    FA system on `Fin n` — the KPS counterexample, padded with null atoms. -/
theorem exists_nonrepresentable_fin {n : ℕ} (h : 5 ≤ n) :
    ∃ sys : EpistemicSystemFA (Fin n), ¬Representable sys := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨kpsSystemFA, kps_not_representable⟩
  | succ n _ ih =>
    obtain ⟨sys, hsys⟩ := ih
    exact ⟨padFA sys, fun h => hsys (representable_of_padFA h)⟩

end ComparativeProbability
