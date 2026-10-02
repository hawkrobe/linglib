module

public import Linglib.Logic.ComparativeProbability.Basic
public import Linglib.Logic.ComparativeProbability.Content
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Representability of qualitative probability orders

A qualitative probability order is representable when a finitely additive probability measure
induces it. Kraft, Pratt and Seidenberg show that every order on at most four atoms is
representable and give a five-atom order that is not. This file holds the predicate and the
reductions to disjoint comparisons and past a null atom; `CancellationFin4.lean` derives the
cases up to four atoms from Scott cancellation, and `Completeness.lean` holds the five-atom
counterexample and its padding to every larger size.

## Main statements

* `Representable`: the representability predicate.
* `reduce_to_disjoint`, `null_elem_reduce`, `perm_repr`: the reductions.

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
