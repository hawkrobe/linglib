import Linglib.Logic.ComparativeProbability.Systems
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Representability of qualitative probability orders

[kraft-pratt-seidenberg-1959] [holliday-icard-2013]

Qualitative probability orders on small domains (|W| ≤ 4) are representable by
finitely additive probability measures (**Theorem 8a**,
[kraft-pratt-seidenberg-1959]). For every |W| ≥ 5 this fails: padding the KPS
counterexample with null atoms gives a non-representable order at each
cardinality (**Theorem 8b**).

`[UPSTREAM]` candidate: KPS representability is measurement theory absent
from mathlib (see the note in `Systems.lean`).

## Contents

1. **`Representable`**: the representability predicate.
2. **KPS counterexample** (Fin 5): non-representable order (`kpsSystem`,
   `kps_not_representable`); null-atom padding (`QualitativeProbability.pad`,
   `exists_nonrepresentable_fin`) extends it to every `Fin n` with `n ≥ 5`.
3. **Shared infrastructure**: injection pullback
   (`QualitativeProbability.comap`), null element reduction
   (`null_elem_reduce`), transport along equivalences
   (`QualitativeProbability.transport`, `perm_repr`).
4. **Small-cardinality proofs**: Fin 0 (`QualitativeProbability.elim0`), Fin 1
   (`representable_fin1`), Fin 2 (`representable_fin2`).  Fin 3 and Fin 4 are
   derived from Scott cancellation in `CancellationFin4.lean`
   (`representable_fin3`, `representable_fin4`).
-/

namespace ComparativeProbability

/-- A qualitative probability order is **representable** when some finitely
    additive probability measure induces exactly its comparison relation. -/
def Representable {W : Type*} (sys : QualitativeProbability (Set W)) : Prop :=
  ∃ m : FinAddMeasure ℚ W, ∀ A B, sys.le A B ↔ m A ≤ m B

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

section KPSSystem

attribute [local instance] Classical.propDecidable

private noncomputable def kpsRankSet (A : Set (Fin 5)) : ℕ := kpsRank A.toFinset
private noncomputable def kpsLe (A B : Set (Fin 5)) : Prop := kpsRankSet A ≤ kpsRankSet B

noncomputable def kpsSystem : QualitativeProbability (Set (Fin 5)) where
  le := kpsLe
  mono' := λ {A B} hAB => kps_mono_finset _ _ (Set.toFinset_subset_toFinset.mpr hAB)
  nonTrivial := by
    simp only [kpsLe, kpsRankSet, Set.top_eq_univ, Set.bot_eq_empty, Set.toFinset_univ,
      Set.toFinset_empty]; decide
  total := λ A B => le_total (kpsRankSet A) (kpsRankSet B)
  trans' := λ {_ _ _} hab hbc => le_trans hab hbc
  additive A B := by
    unfold kpsLe kpsRankSet
    rw [Set.toFinset_sdiff, Set.toFinset_sdiff]
    exact kps_additive_finset _ _

private theorem mu_pair (m : FinAddMeasure ℚ (Fin 5)) (a b : Fin 5) (hab : a ≠ b) :
    m ({a, b} : Set (Fin 5)) = m {a} + m {b} := by
  rw [Set.insert_eq a {b}, m.additive (Set.disjoint_singleton.mpr hab)]

private theorem mu_triple (m : FinAddMeasure ℚ (Fin 5)) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    m ({a, b, c} : Set (Fin 5)) = m {a} + m {b} + m {c} := by
  rw [Set.insert_eq a ({b, c} : Set (Fin 5)), m.additive (A := {a}) (B := {b, c})
    (Set.disjoint_left.mpr fun x hx hxbc => by
      rw [Set.mem_singleton_iff] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxbc
      subst hx; rcases hxbc with rfl | rfl
      exacts [absurd rfl hab, absurd rfl hac]),
    mu_pair m b c hbc, add_assoc]

theorem kps_not_representable : ¬Representable kpsSystem := by
  intro ⟨m, hm⟩
  set P := m ({(0 : Fin 5)} : Set (Fin 5))
  set Q := m ({(1 : Fin 5)} : Set (Fin 5))
  set R := m ({(2 : Fin 5)} : Set (Fin 5))
  set S := m ({(3 : Fin 5)} : Set (Fin 5))
  set T := m ({(4 : Fin 5)} : Set (Fin 5))
  -- Ordering facts: three strict (rank <), one weak (rank ≤)
  have hord1 : ¬ kpsLe {0} ({1, 3} : Set (Fin 5)) := by
    unfold kpsLe kpsRankSet
    simp only [Set.toFinset_insert, Set.toFinset_singleton]; decide
  have hord2 : ¬ kpsLe {2, 3} ({0, 1} : Set (Fin 5)) := by
    unfold kpsLe kpsRankSet
    simp only [Set.toFinset_insert, Set.toFinset_singleton]; decide
  have hord3 : ¬ kpsLe {1, 4} ({0, 3} : Set (Fin 5)) := by
    unfold kpsLe kpsRankSet
    simp only [Set.toFinset_insert, Set.toFinset_singleton]; decide
  have hord4 : kpsLe {2, 4} ({0, 1, 3} : Set (Fin 5)) := by
    unfold kpsLe kpsRankSet
    simp only [Set.toFinset_insert, Set.toFinset_singleton]; decide
  -- Convert to measure inequalities via the representation isomorphism
  have hmeas1 : m ({1, 3} : Set _) < m ({(0 : Fin 5)} : Set _) :=
    not_le.mp (λ h => hord1 ((hm _ _).mpr h))
  have hmeas2 : m ({0, 1} : Set _) < m ({2, 3} : Set _) :=
    not_le.mp (λ h => hord2 ((hm _ _).mpr h))
  have hmeas3 : m ({0, 3} : Set _) < m ({1, 4} : Set _) :=
    not_le.mp (λ h => hord3 ((hm _ _).mpr h))
  have hmeas4 : m ({0, 1, 3} : Set _) ≥ m ({2, 4} : Set _) :=
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
theorem reduce_to_disjoint {W : Type*} (sys : QualitativeProbability (Set W))
    (m : FinAddMeasure ℚ W)
    (h : ∀ C D : Set W, Disjoint C D → (sys.le C D ↔ m C ≤ m D)) :
    ∀ A B, sys.le A B ↔ m A ≤ m B := by
  intro A B
  rw [sys.additive A B]
  exact (h _ _ disjoint_sdiff_sdiff).trans (m.mu_qadd A B).symm

-- ── Null element reduction ────────────────────────────

/-- Removing a null element (`sys.le {j} ∅`) from both sides of a disjoint
    comparison preserves `le`. -/
theorem null_removal_disjoint {W : Type*} (sys : QualitativeProbability (Set W))
    (j : W) (hj : sys.le {j} ∅)
    (C D : Set W) (hdisj : Disjoint C D) :
    sys.le C D ↔ sys.le (C \ {j}) (D \ {j}) := by
  have null_sub : ∀ S : Set W, sys.le S (S \ {j}) := by
    intro S
    by_cases hj_in : j ∈ S
    · rw [sys.additive S (S \ {j}), Set.sdiff_eq_empty.mpr Set.sdiff_subset,
        Set.sdiff_sdiff_cancel_left (Set.singleton_subset_iff.mpr hj_in)]
      exact hj
    · rw [Set.sdiff_singleton_eq_self hj_in]; exact sys.refl S
  by_cases hjC : j ∈ C
  · have hjnD : j ∉ D := Set.disjoint_left.mp hdisj hjC
    rw [Set.sdiff_singleton_eq_self hjnD]
    exact ⟨fun h => sys.trans (sys.mono Set.sdiff_subset) h,
           fun h => sys.trans (null_sub C) h⟩
  · rw [Set.sdiff_singleton_eq_self hjC]
    by_cases hjD : j ∈ D
    · exact ⟨fun h => sys.trans h (null_sub D),
             fun h => sys.trans h (sys.mono Set.sdiff_subset)⟩
    · rw [Set.sdiff_singleton_eq_self hjD]

/-- `Fin.succ '' (Fin.succ ⁻¹' S) = S \ {0}` for `S : Set (Fin (n+1))`. -/
private theorem succ_image_preimage {n : ℕ} (S : Set (Fin (n + 1))) :
    Fin.succ '' (Fin.succ ⁻¹' S) = S \ {(0 : Fin (n + 1))} := by
  rw [Set.image_preimage_eq_range_inter, Fin.range_succ]
  ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_sdiff]; exact And.comm

/-- Pull back a qualitative probability order along an injection: `α`-sets
    compare via their images. Non-triviality requires a witness and must be
    supplied. -/
def QualitativeProbability.comap {α W : Type*} (f : α → W) (hf : Function.Injective f)
    (sys : QualitativeProbability (Set W)) (hnt : ¬sys.le (Set.range f) ∅) :
    QualitativeProbability (Set α) where
  le A B := sys.le (f '' A) (f '' B)
  mono' _ _ hAB := sys.mono (Set.image_mono hAB)
  nonTrivial := by
    show ¬sys.le (f '' Set.univ) (f '' ∅)
    rwa [Set.image_empty, Set.image_univ]
  total _ _ := sys.total _ _
  trans' _ _ _ h1 h2 := sys.trans h1 h2
  additive A B := by
    show sys.le (f '' A) (f '' B) ↔ sys.le (f '' (A \ B)) (f '' (B \ A))
    rw [Set.image_sdiff hf, Set.image_sdiff hf]; exact sys.additive _ _

/-- Null element reduction: if atom 0 is null in an order on `Fin (n+2)` and
    some atom is not, representability reduces along `Fin.succ` to `Fin (n+1)`. -/
theorem null_elem_reduce {n : ℕ} (sys : QualitativeProbability (Set (Fin (n + 2))))
    (hn0 : sys.le {(0 : Fin (n + 2))} ∅)
    (hnn : ∃ i : Fin (n + 1), ¬sys.le {Fin.succ i} ∅)
    (sub_repr : ∀ sys' : QualitativeProbability (Set (Fin (n + 1))), Representable sys') :
    Representable sys := by
  have hnt : ¬sys.le (Set.range (Fin.succ : Fin (n + 1) → Fin (n + 2))) ∅ := by
    obtain ⟨i, hi⟩ := hnn
    exact fun h => hi (sys.trans (sys.mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i))) h)
  obtain ⟨m_r, hm_r⟩ := sub_repr (sys.comap Fin.succ (Fin.succ_injective _) hnt)
  -- lift the sub-measure (the null element gets weight 0)
  refine ⟨m_r.map Fin.succ, reduce_to_disjoint sys _ (fun C D hdisj => ?_)⟩
  rw [null_removal_disjoint sys 0 hn0 C D hdisj,
      ← succ_image_preimage C, ← succ_image_preimage D]
  exact hm_r (Fin.succ ⁻¹' C) (Fin.succ ⁻¹' D)

-- ── Card 0: impossible ─────────────────────────────

/-- There is no qualitative probability order on an empty carrier: `∅ = Ω`
    contradicts non-triviality. Mirrors `Fin.elim0`. -/
def QualitativeProbability.elim0 {C : Sort*} (sys : QualitativeProbability (Set (Fin 0))) :
    C := by
  have : (∅ : Set (Fin 0)) = Set.univ := by ext x; exact Fin.elim0 x
  have h : sys.le ⊤ ⊥ := by
    rw [Set.top_eq_univ, Set.bot_eq_empty, ← this]; exact sys.refl ∅
  exact absurd h sys.nonTrivial

-- ── Card 1 ─────────────────────────────────────────

private theorem set_fin1_eq (A : Set (Fin 1)) : A = ∅ ∨ A = Set.univ := by
  by_cases h : (0 : Fin 1) ∈ A
  · right; ext x; simp [Fin.eq_zero x, h]
  · left; ext x; exact ⟨fun hx => absurd (Fin.eq_zero x ▸ hx) h, fun hx => hx.elim⟩

private noncomputable def measure_fin1 : FinAddMeasure ℚ (Fin 1) :=
  .ofFintype ![1] (by intro i; fin_cases i; norm_num) (by simp)

theorem representable_fin1 (sys : QualitativeProbability (Set (Fin 1))) : Representable sys := by
  refine ⟨measure_fin1, fun A B => ?_⟩
  have hme := measure_fin1.mu_empty
  have hu := measure_fin1.total
  rcases set_fin1_eq A with rfl | rfl <;> rcases set_fin1_eq B with rfl | rfl
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
  · exact ⟨fun _ => by rw [hme, hu]; norm_num, fun _ => sys.mono (Set.empty_subset _)⟩
  · exact ⟨fun h => absurd h sys.nonTrivial, fun h => by rw [hme, hu] at h; linarith⟩
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩

-- ── Card 2: Infrastructure ──────────────────────────

private noncomputable def measure_fin2 (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    FinAddMeasure ℚ (Fin 2) :=
  .ofFintype ![a, 1 - a] (by intro i; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_two])

private theorem mf2_zero (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1) {(0 : Fin 2)} = a := by
  simp [measure_fin2]

private theorem mf2_one (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1) {(1 : Fin 2)} = 1 - a := by
  simp [measure_fin2]

private theorem set_fin2_eq (A : Set (Fin 2)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Set.univ := by
  by_cases h0 : (0 : Fin 2) ∈ A <;> by_cases h1 : (1 : Fin 2) ∈ A
  · right; right; right; ext x; fin_cases x <;> simp_all
  · right; left; ext x; fin_cases x <;> simp_all
  · right; right; left; ext x; fin_cases x <;> simp_all
  · left; ext x; fin_cases x <;> simp_all

private theorem not_both_null_fin2 (sys : QualitativeProbability (Set (Fin 2))) :
    ¬(sys.le {0} ∅ ∧ sys.le {1} ∅) := by
  intro ⟨h0, h1⟩
  have hd1 : ({(0 : Fin 2)} : Set _) \ Set.univ = ∅ := by ext x; simp
  have hd2 : Set.univ \ ({(0 : Fin 2)} : Set _) = {(1 : Fin 2)} := by
    ext x; simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and, Fin.ext_iff]
    omega
  exact sys.nonTrivial (sys.trans ((sys.additive Set.univ {0}).mpr (hd1 ▸ hd2 ▸ h1)) h0)

-- ── Card 2: Helper for disjoint-pair dispatch ────────

/-- Given measure values and ordering facts, close all 16 disjoint-pair cases on Fin 2.
    The 7 non-disjoint pairs close by exfalso.
    The 5 uniform pairs (∅/∅, X/∅, ∅/univ) are independent of the ordering.
    The 4 critical pairs (∅/{0}, ∅/{1}, {0}/{1}, {1}/{0}) use the hypotheses. -/
private theorem fin2_dispatch (sys : QualitativeProbability (Set (Fin 2)))
    (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (he0 : sys.le {(0 : Fin 2)} ∅ ↔ a ≤ 0)
    (he1 : sys.le {(1 : Fin 2)} ∅ ↔ 1 - a ≤ 0)
    (h01 : sys.le {(0 : Fin 2)} {1} ↔ a ≤ 1 - a)
    (h10 : sys.le {(1 : Fin 2)} {0} ↔ 1 - a ≤ a) :
    ∀ C D : Set (Fin 2), Disjoint C D →
      (sys.le C D ↔ measure_fin2 a ha ha1 C ≤ measure_fin2 a ha ha1 D) := by
  intro C D hCD
  have hme := (measure_fin2 a ha ha1).mu_empty
  have hm0 := mf2_zero a ha ha1
  have hm1 := mf2_one a ha ha1
  have hmu := (measure_fin2 a ha ha1).total
  have hdisj : ∀ x ∈ C, x ∉ D := fun x hx => Set.disjoint_left.mp hCD hx
  rcases set_fin2_eq C with rfl | rfl | rfl | rfl <;>
  rcases set_fin2_eq D with rfl | rfl | rfl | rfl
  -- ∅ vs ∅
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
  -- ∅ vs {0}
  · rw [hme, hm0]; exact ⟨fun _ => ha, fun _ => sys.mono (Set.empty_subset _)⟩
  -- ∅ vs {1}
  · rw [hme, hm1]; exact ⟨fun _ => by linarith, fun _ => sys.mono (Set.empty_subset _)⟩
  -- ∅ vs univ
  · rw [hme, hmu]; exact ⟨fun _ => by norm_num, fun _ => sys.mono (Set.empty_subset _)⟩
  -- {0} vs ∅
  · rw [hm0, hme]; exact he0
  -- {0} vs {0}: not disjoint
  · exact (hdisj 0 rfl rfl).elim
  -- {0} vs {1}
  · rw [hm0, hm1]; exact h01
  -- {0} vs univ: not disjoint
  · exact (hdisj 0 rfl (Set.mem_univ _)).elim
  -- {1} vs ∅
  · rw [hm1, hme]; exact he1
  -- {1} vs {0}
  · rw [hm1, hm0]; exact h10
  -- {1} vs {1}: not disjoint
  · exact (hdisj 1 rfl rfl).elim
  -- {1} vs univ: not disjoint
  · exact (hdisj 1 rfl (Set.mem_univ _)).elim
  -- univ vs ∅
  · rw [hmu, hme]; exact ⟨fun h => absurd h sys.nonTrivial, fun h => by linarith⟩
  -- univ vs {0}: not disjoint
  · exact (hdisj 0 (Set.mem_univ _) rfl).elim
  -- univ vs {1}: not disjoint
  · exact (hdisj 1 (Set.mem_univ _) rfl).elim
  -- univ vs univ: not disjoint
  · exact (hdisj 0 (Set.mem_univ _) (Set.mem_univ _)).elim

-- ── Card 2: Main theorem ───────────────────────────

theorem representable_fin2 (sys : QualitativeProbability (Set (Fin 2))) : Representable sys := by
  by_cases h_null0 : sys.le {(0 : Fin 2)} ∅
  · -- Case 1: atom 0 null → a = 0
    have h_nnull1 : ¬sys.le {(1 : Fin 2)} ∅ := fun h => not_both_null_fin2 sys ⟨h_null0, h⟩
    have h_n10 : ¬sys.le {(1 : Fin 2)} {0} :=
      fun h => not_both_null_fin2 sys ⟨h_null0, sys.trans h h_null0⟩
    have h_01 : sys.le {(0 : Fin 2)} {1} :=
      (sys.total {(0 : Fin 2)} {1}).resolve_right h_n10
    refine ⟨measure_fin2 0 le_rfl zero_le_one,
      reduce_to_disjoint sys _ (fin2_dispatch sys 0 le_rfl zero_le_one
        ⟨fun _ => le_refl _, fun _ => h_null0⟩
        ⟨fun h => absurd h h_nnull1, fun h => by linarith⟩
        ⟨fun _ => by linarith, fun _ => h_01⟩
        ⟨fun h => absurd h h_n10, fun h => by linarith⟩)⟩
  · by_cases h_null1 : sys.le {(1 : Fin 2)} ∅
    · -- Case 2: atom 1 null → a = 1
      have h_n01 : ¬sys.le {(0 : Fin 2)} {1} :=
        fun h => not_both_null_fin2 sys ⟨sys.trans h h_null1, h_null1⟩
      have h_10 : sys.le {(1 : Fin 2)} {0} :=
        (sys.total {(1 : Fin 2)} {0}).resolve_right h_n01
      refine ⟨measure_fin2 1 zero_le_one le_rfl,
        reduce_to_disjoint sys _ (fin2_dispatch sys 1 zero_le_one le_rfl
          ⟨fun h => absurd h h_null0, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h_null1⟩
          ⟨fun h => absurd h h_n01, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h_10⟩)⟩
    · -- Neither null: both singletons are "positive"
      by_cases h01 : sys.le {(0 : Fin 2)} {1}
      · by_cases h10 : sys.le {(1 : Fin 2)} {0}
        · -- Case 3c: {0} ≈ {1} → a = 1/2
          refine ⟨measure_fin2 (1/2) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin2_dispatch sys (1/2) (by linarith) (by linarith)
              ⟨fun h => absurd h h_null0, fun h => by linarith⟩
              ⟨fun h => absurd h h_null1, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun _ => by linarith, fun _ => h10⟩)⟩
        · -- Case 3a: {0} ≺ {1} → a = 1/3
          refine ⟨measure_fin2 (1/3) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin2_dispatch sys (1/3) (by linarith) (by linarith)
              ⟨fun h => absurd h h_null0, fun h => by linarith⟩
              ⟨fun h => absurd h h_null1, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h h10, fun h => by linarith⟩)⟩
      · -- Case 3b: ¬({0} ≼ {1}) → {1} ≺ {0} (totality), a = 2/3
        have h10 : sys.le {(1 : Fin 2)} {0} :=
          (sys.total {(1 : Fin 2)} {0}).resolve_right h01
        refine ⟨measure_fin2 (2/3) (by linarith) (by linarith),
          reduce_to_disjoint sys _ (fin2_dispatch sys (2/3) (by linarith) (by linarith)
            ⟨fun h => absurd h h_null0, fun h => by linarith⟩
            ⟨fun h => absurd h h_null1, fun h => by linarith⟩
            ⟨fun h => absurd h h01, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h10⟩)⟩

-- ── Transport + Permutation infrastructure ────────────

/-- Transport a qualitative probability order along an equivalence of carriers. -/
def QualitativeProbability.transport {W α : Type*} (e : W ≃ α)
    (sys : QualitativeProbability (Set W)) : QualitativeProbability (Set α) :=
  sys.comap e.symm e.symm.injective
    (by rw [Equiv.range_eq_univ, ← Set.top_eq_univ, ← Set.bot_eq_empty]; exact sys.nonTrivial)

theorem transfer_repr {W α : Type*}
    (e : W ≃ α) (sys : QualitativeProbability (Set W)) (m : FinAddMeasure ℚ α)
    (hm : ∀ A B : Set α, (sys.transport e).le A B ↔ m A ≤ m B) :
    ∀ A B : Set W, sys.le A B ↔ m.map e.symm A ≤ m.map e.symm B := by
  intro A B
  have h := hm (e '' A) (e '' B)
  simp only [QualitativeProbability.transport, QualitativeProbability.comap,
    Equiv.symm_image_image] at h
  simpa only [FinAddMeasure.map_apply, ← Equiv.image_eq_preimage_symm] using h

/-- Null pattern transport: `j` is null in `sys.transport σ` iff `σ.symm j` is
    null in `sys`. -/
theorem perm_null_iff {n : ℕ} (σ : Fin n ≃ Fin n)
    (sys : QualitativeProbability (Set (Fin n))) (j : Fin n) :
    (sys.transport σ).le {j} ∅ ↔ sys.le {σ.symm j} ∅ := by
  show sys.le (σ.symm '' {j}) (σ.symm '' ∅) ↔ sys.le {σ.symm j} ∅
  simp only [Set.image_empty, Set.image_singleton]

/-- Representability transports backward along any equivalence. -/
theorem perm_repr {W α : Type*} (σ : W ≃ α) (sys : QualitativeProbability (Set W))
    (h : Representable (sys.transport σ)) : Representable sys := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m.map σ.symm, transfer_repr σ sys m hm⟩

-- ── Null-atom padding: Theorem 8b at every cardinality ≥ 5 ──

/-- Pad an order with one null atom: comparisons on `Fin (n + 1)` are decided
    by the preimage restriction to the first `n` atoms. -/
def QualitativeProbability.pad {n : ℕ} (sys : QualitativeProbability (Set (Fin n))) :
    QualitativeProbability (Set (Fin (n + 1))) where
  le A B := sys.le (Fin.castSucc ⁻¹' A) (Fin.castSucc ⁻¹' B)
  mono' _ _ hAB := sys.mono (Set.preimage_mono hAB)
  nonTrivial := by
    show ¬sys.le (Fin.castSucc ⁻¹' Set.univ) (Fin.castSucc ⁻¹' ∅)
    rw [Set.preimage_univ, Set.preimage_empty, ← Set.top_eq_univ, ← Set.bot_eq_empty]
    exact sys.nonTrivial
  total _ _ := sys.total _ _
  trans' _ _ _ h1 h2 := sys.trans h1 h2
  additive A B := by
    show sys.le _ _ ↔ sys.le _ _
    rw [Set.preimage_sdiff, Set.preimage_sdiff]; exact sys.additive _ _

/-- The padded atom is null. -/
theorem QualitativeProbability.pad_last_null {n : ℕ}
    (sys : QualitativeProbability (Set (Fin n))) : sys.pad.le {Fin.last n} ∅ := by
  show sys.le (Fin.castSucc ⁻¹' {Fin.last n}) (Fin.castSucc ⁻¹' ∅)
  rw [Set.preimage_empty, show Fin.castSucc ⁻¹' {Fin.last n} = (∅ : Set (Fin n)) from
    Set.eq_empty_of_forall_notMem fun i hi => (Fin.castSucc_lt_last i).ne hi]; exact sys.refl ∅

/-- Padding reflects representability: a measure for `sys.pad` assigns the
    padded atom measure zero, so its `Fin.castSucc`-image restriction represents
    `sys`. -/
theorem representable_of_pad {n : ℕ} {sys : QualitativeProbability (Set (Fin n))}
    (h : Representable sys.pad) : Representable sys := by
  obtain ⟨m, hm⟩ := h
  have hinj := Fin.castSucc_injective n
  have hlast : m {Fin.last n} = 0 := by
    have h0 : m {Fin.last n} ≤ m ∅ := (hm _ _).mp sys.pad_last_null
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
  have htotal : m (Fin.castSucc '' (Set.univ : Set (Fin n))) = 1 := by
    have := m.additive hdisj
    rw [hcover, m.total, hlast, add_zero] at this; linarith
  refine ⟨{
    toFun := fun A => m (Fin.castSucc '' A)
    nonneg' := fun A => m.nonneg _
    additive' := fun A B hd => by
      rw [Set.image_union]; exact m.additive ((Set.disjoint_image_iff hinj).mpr hd)
    total' := htotal
  }, fun A B => ?_⟩
  have key := hm (Fin.castSucc '' A) (Fin.castSucc '' B)
  rwa [show sys.pad.le (Fin.castSucc '' A) (Fin.castSucc '' B) ↔ sys.le A B from by
    show sys.le (Fin.castSucc ⁻¹' (Fin.castSucc '' A)) _ ↔ _
    rw [Set.preimage_image_eq A hinj, Set.preimage_image_eq B hinj]] at key

/-- **Theorem 8b at every cardinality**: for `n ≥ 5` there is a non-representable
    FA system on `Fin n` — the KPS counterexample, padded with null atoms. -/
theorem exists_nonrepresentable_fin {n : ℕ} (h : 5 ≤ n) :
    ∃ sys : QualitativeProbability (Set (Fin n)), ¬Representable sys := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨kpsSystem, kps_not_representable⟩
  | succ n _ ih =>
    obtain ⟨sys, hsys⟩ := ih
    exact ⟨sys.pad, fun h => hsys (representable_of_pad h)⟩

end ComparativeProbability
