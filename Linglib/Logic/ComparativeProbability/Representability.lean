module

public import Linglib.Logic.ComparativeProbability.Basic
public import Linglib.Logic.ComparativeProbability.Content
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Tauto
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Representability of qualitative probability orders

A qualitative probability order is representable when a finitely additive probability measure
induces it. Kraft, Pratt and Seidenberg show that every order on at most four atoms is
representable and give a five-atom order that is not. This file holds the predicate, the
reductions to disjoint comparisons and past a null atom, and the one- and two-atom cases;
`CancellationFin4.lean` derives the three- and four-atom cases from Scott cancellation, and
`Completeness.lean` holds the five-atom counterexample and its padding to every larger size.

## Main statements

* `Representable`: the representability predicate.
* `reduce_to_disjoint`, `null_elem_reduce`, `perm_repr`: the reductions.
* `representable_fin1`, `representable_fin2`: the one- and two-atom cases.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

/-- A qualitative probability order is **representable** when some finitely
    additive probability measure induces exactly its comparison relation. -/
def Representable {W : Type*} (sys : QualitativeProbability (Set W)) : Prop :=
  ∃ m : FinAddMeasure ℚ W, ∀ A B, sys.le A B ↔ m A ≤ m B

attribute [local instance] Classical.propDecidable

/-! ### Reductions -/

/-- Agreement on disjoint pairs suffices for full representability, since additivity reduces
    every comparison to a disjoint one. -/
theorem reduce_to_disjoint {W : Type*} (sys : QualitativeProbability (Set W))
    (m : FinAddMeasure ℚ W)
    (h : ∀ C D : Set W, Disjoint C D → (sys.le C D ↔ m C ≤ m D)) :
    ∀ A B, sys.le A B ↔ m A ≤ m B := by
  intro A B
  rw [sys.additive A B]
  exact (h _ _ disjoint_sdiff_sdiff).trans (m.mu_qadd A B).symm

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

/-- If atom `0` is null in an order on `Fin (n+2)` and some atom is not, representability
    reduces along `Fin.succ` to `Fin (n+1)`. -/
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

/-! ### One and two atoms -/

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

/-- The measure values and the ordering facts settle all 16 pairs on `Fin 2`. The 7
    non-disjoint pairs close by exfalso, the 5 uniform pairs (∅/∅, X/∅, ∅/univ) do not depend
    on the ordering, and the 4 critical pairs (∅/{0}, ∅/{1}, {0}/{1}, {1}/{0}) use the
    hypotheses. -/
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

/-! ### Transport along equivalences -/

theorem transfer_repr {W α : Type*}
    (e : W ≃ α) (sys : QualitativeProbability (Set W)) (m : FinAddMeasure ℚ α)
    (hm : ∀ A B : Set α, (sys.transport e).le A B ↔ m A ≤ m B) :
    ∀ A B : Set W, sys.le A B ↔ m.map e.symm A ≤ m.map e.symm B := by
  intro A B
  have h := hm (e '' A) (e '' B)
  simp only [QualitativeProbability.transport, QualitativeProbability.comap,
    Equiv.symm_image_image] at h
  simpa only [FinAddMeasure.map_apply, ← Equiv.image_eq_preimage_symm] using h

/-- `j` is null in `sys.transport σ` exactly when `σ.symm j` is null in `sys`. -/
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

end ComparativeProbability
