/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.Trace

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Edge-count grading of the Δ^c bialgebra
[marcolli-chomsky-berwick-2025]

The graded subspaces of `ConnesKreimer R (Nonplanar (α ⊕ β))` under the
edge-count grading (`Forest.edgeCount`, `Core/Data/RoseTree/Nonplanar.lean`),
with the coproduct half of the grading compatibility
(`comulCAlgHomN_of'_mem_gradedSpan`) — the graded content of Lemma 1.2.10.

TODO: once mathlib's graded coalgebra/bialgebra API lands
(leanprover-community/mathlib4#39849), restate `gradedPiece` as a
`DirectSum.Decomposition` and this file's content as a `GradedBialgebra`
instance (with connectedness feeding the graded Hopf upgrade).
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommRing R] {α β : Type*}

/-! ### Edge-count grading

Per [marcolli-chomsky-berwick-2025] p. 37, Lemma 1.2.10:

> Let V^c(𝔉_{SO_0}) denote the vector space (over ℚ) spanned by the
> workspaces F ∈ 𝔉_{SO_0}, endowed with the product given by the
> disjoint union ⊔ and the coproduct Δ^c of (1.2.8). The space
> V(𝔉_{SO_0}) is graded by the number of edges. Then
> (V^c(𝔉_{SO_0}), ⊔, Δ^c) is a graded bialgebra.

This file defines the graded subspaces and proves the coproduct half of
the grading compatibility (`comulCAlgHomN_of'_mem_gradedSpan`); the
product half is edge-count additivity over disjoint union
(`Forest.edgeCount_add`), and edge conservation through the trace cut
machinery is `cutSummandsCN_numNodes`
(`Core/Combinatorics/RootedTree/Cut.lean`). -/

/-- **Graded piece V_n**: the subspace of `ConnesKreimer R (Nonplanar X)`
    spanned by forests with exactly `n` edges. -/
noncomputable def gradedPiece (X : Type*) (n : ℕ) :
    Submodule R (ConnesKreimer R (Nonplanar X)) :=
  Submodule.span R
    {x | ∃ F : Forest (Nonplanar X),
      Forest.edgeCount F = n ∧ x = ConnesKreimer.of' F}

/-! ### Homogeneous tensor span at fixed total edge degree -/

/-- The span of basis tensors `of' F₁ ⊗ of' F₂` with total edge count
    `n` — the homogeneous degree-`n` piece of the tensor square through
    which Δ^c factors. -/
private noncomputable def gradedTensorSpan (n : ℕ) :
    Submodule R (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
      ConnesKreimer R (Nonplanar (α ⊕ β))) :=
  Submodule.span R {y | ∃ F₁ F₂ : Forest (Nonplanar (α ⊕ β)),
    Forest.edgeCount F₁ + Forest.edgeCount F₂ = n ∧
    y = ConnesKreimer.of' F₁ ⊗ₜ[R] ConnesKreimer.of' F₂}

/-- Multiplicativity of the graded tensor spans: degrees add. -/
private theorem gradedTensorSpan_mul {m k : ℕ}
    {u v : ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
      ConnesKreimer R (Nonplanar (α ⊕ β))}
    (hu : u ∈ gradedTensorSpan (R := R) (α := α) (β := β) m)
    (hv : v ∈ gradedTensorSpan (R := R) (α := α) (β := β) k) :
    u * v ∈ gradedTensorSpan (R := R) (α := α) (β := β) (m + k) := by
  have hle : gradedTensorSpan (R := R) (α := α) (β := β) m *
      gradedTensorSpan (R := R) (α := α) (β := β) k ≤
      gradedTensorSpan (R := R) (α := α) (β := β) (m + k) := by
    rw [gradedTensorSpan, gradedTensorSpan, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨a, ⟨F₁, F₂, hab, rfl⟩, b, ⟨G₁, G₂, hgk, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨F₁ + G₁, F₂ + G₂, ?_, ?_⟩
    · rw [Forest.edgeCount_add, Forest.edgeCount_add]
      omega
    · show (ConnesKreimer.of' F₁ ⊗ₜ[R] ConnesKreimer.of' F₂) *
        (ConnesKreimer.of' G₁ ⊗ₜ[R] ConnesKreimer.of' G₂) =
        ConnesKreimer.of' (F₁ + G₁) ⊗ₜ[R] ConnesKreimer.of' (F₂ + G₂)
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← ConnesKreimer.of'_add,
        ← ConnesKreimer.of'_add]
  exact hle (Submodule.mul_mem_mul hu hv)

/-- Tree-level membership: `Δ^c` of a single tree is homogeneous of
    degree the tree's edge count. -/
private theorem comulCTreeN_mem (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    comulCTreeN (R := R) τ T ∈
      gradedTensorSpan (R := R) (α := α) (β := β) (T.numNodes - 1) := by
  unfold comulCTreeN comulTreeNG
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.subset_span ⟨{T}, 0, ?_, ?_⟩
    · rw [Forest.edgeCount_singleton]
      show T.numNodes - 1 + Forest.edgeCount (0 : Forest (Nonplanar (α ⊕ β))) =
        T.numNodes - 1
      show T.numNodes - 1 + 0 = T.numNodes - 1
      omega
    · rw [ConnesKreimer.of'_zero]
      rfl
  · refine multiset_sum_mem _ ?_
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hc
    have hcons := cutSummandsCN_numNodes τ T p hp
    have hpos := Nonplanar.numNodes_pos p.2
    refine Submodule.subset_span ⟨p.1, {p.2}, ?_, rfl⟩
    rw [Forest.edgeCount_singleton]
    omega

/-- Forest-level membership: `Δ^c` of a forest is homogeneous of degree
    its edge count. -/
private theorem comulCForestN_mem (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCForestN (R := R) τ F ∈
      gradedTensorSpan (R := R) (α := α) (β := β) (Forest.edgeCount F) := by
  induction F using Multiset.induction_on with
  | empty =>
    rw [comulCForestN_zero]
    refine Submodule.subset_span ⟨0, 0, rfl, ?_⟩
    rw [Algebra.TensorProduct.one_def, ConnesKreimer.of'_zero]
  | cons T F ih =>
    rw [show comulCForestN (R := R) τ (T ::ₘ F) =
          comulCTreeN (R := R) τ T * comulCForestN (R := R) τ F from
        comulForestNG_cons _ T F,
        Forest.edgeCount_cons]
    exact gradedTensorSpan_mul (comulCTreeN_mem τ T) ih

/-- Δ^c preserves the edge-count grading ([marcolli-chomsky-berwick-2025]
    Lemma 1.2.10, p. 37): the coproduct of a basis forest lies in the span of
    homogeneous tensors `xi ⊗ yi` with degrees summing to the forest's edge
    count. With edge-count additivity over the product (disjoint union) and
    `comulCN_coassoc`, this gives the lemma's graded bialgebra structure on
    `V^c(𝔉_{SO_0})`. -/
theorem comulCAlgHomN_of'_mem_gradedSpan
    (τ : Nonplanar (α ⊕ β) → β) (F : Forest (Nonplanar (α ⊕ β))) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.of' F) ∈
      Submodule.span R {y | ∃ (i j : ℕ) (_hi : i + j = Forest.edgeCount F)
        (xi yi : ConnesKreimer R (Nonplanar (α ⊕ β))),
        xi ∈ gradedPiece (α ⊕ β) i ∧
        yi ∈ gradedPiece (α ⊕ β) j ∧
        y = xi ⊗ₜ[R] yi} := by
  -- Each cut summand splits the edges (the trace marker replaces the cut
  -- subtree by a unit-weight leaf, `cutSummandsCN_numNodes`), and the
  -- homogeneous tensor spans multiply additively (`gradedTensorSpan_mul`).
  rw [comulCAlgHomN_apply_of']
  refine SetLike.le_def.mp (Submodule.span_le.mpr ?_)
    (comulCForestN_mem (R := R) τ F)
  rintro y ⟨F₁, F₂, hsum, rfl⟩
  exact Submodule.subset_span
    ⟨Forest.edgeCount F₁, Forest.edgeCount F₂, hsum,
      ConnesKreimer.of' F₁, ConnesKreimer.of' F₂,
      Submodule.subset_span ⟨F₁, rfl, rfl⟩,
      Submodule.subset_span ⟨F₂, rfl, rfl⟩, rfl⟩

end ConnesKreimer
