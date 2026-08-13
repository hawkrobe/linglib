/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.TraceNonplanar

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Edge-count grading of the Δ^c bialgebra
[marcolli-chomsky-berwick-2025]

The edge-count grading on forests and the graded subspaces of
`ConnesKreimer R (Nonplanar (α ⊕ β))`, with the coproduct half of the
grading compatibility (`comulCAlgHomN_of'_mem_gradedSpan`) — the graded
content of Lemma 1.2.10.
-/

namespace ConnesKreimer

open scoped TensorProduct

/-! ### Edge-count grading

Per [marcolli-chomsky-berwick-2025] p. 37, Lemma 1.2.10:

> Let V^c(𝔉_{SO_0}) denote the vector space (over ℚ) spanned by the
> workspaces F ∈ 𝔉_{SO_0}, endowed with the product given by the
> disjoint union ⊔ and the coproduct Δ^c of (1.2.8). The space
> V(𝔉_{SO_0}) is graded by the number of edges. Then
> (V^c(𝔉_{SO_0}), ⊔, Δ^c) is a graded bialgebra.

This section defines the edge-count grading on forests and its graded
subspaces, and proves the coproduct half of the grading compatibility
(`comulCAlgHomN_of'_mem_gradedSpan`); the product half is edge-count
additivity over disjoint union, and edge conservation through the trace
cut machinery is `cutSummandsCN_numNodes`. -/

section EdgeGrading
variable {R'' : Type*} [CommRing R''] {α'' β'' : Type*}

/-- **Edge count of a forest**: total edges across all trees.

    A tree with `n` vertices has `n - 1` edges. For a forest
    `F = {T_1, ..., T_k}`: total edges = `Σ (weight(T_i) - 1)`.

    Defined as a per-tree sum (avoiding global subtraction) to make
    additivity (`edgeCount (F + G) = edgeCount F + edgeCount G`)
    immediate from `Multiset.map_add` + `Multiset.sum_add`.

    Per MCB Lemma 1.2.10, this is the grading on V^c(𝔉_{SO_0}). -/
def _root_.RoseTree.Nonplanar.Forest.edgeCount {X : Type*} (F : Forest (Nonplanar X)) : ℕ :=
  (F.map (fun T => T.numNodes - 1)).sum

/-- **Graded piece V_n**: the subspace of `ConnesKreimer R'' (Nonplanar X)`
    spanned by forests with exactly `n` edges. -/
noncomputable def gradedPiece (X : Type*) (n : ℕ) :
    Submodule R'' (ConnesKreimer R'' (Nonplanar X)) :=
  Submodule.span R''
    {x | ∃ F : Forest (Nonplanar X), F.edgeCount = n ∧ x = ConnesKreimer.of' F}

/-! ### Edge bookkeeping for `edgeCount` -/

private theorem edgeCount_add {X : Type*} (F G : Forest (Nonplanar X)) :
    Forest.edgeCount (F + G) = Forest.edgeCount F + Forest.edgeCount G := by
  show ((F + G).map (fun T => T.numNodes - 1)).sum = _
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

private theorem edgeCount_singleton {X : Type*} (T : Nonplanar X) :
    Forest.edgeCount ({T} : Forest (Nonplanar X)) = T.numNodes - 1 := by
  show (({T} : Multiset (Nonplanar X)).map (fun T => T.numNodes - 1)).sum = _
  rw [Multiset.map_singleton, Multiset.sum_singleton]

/-- `Σ (wᵢ − 1) + card = Σ wᵢ` for tree-level forests (each `wᵢ ≥ 1`). -/
private theorem sum_map_numNodes_sub_one_add_card {γ : Type*}
    (F : Multiset (RoseTree γ)) :
    ((F.map (fun t => RoseTree.numNodes t - 1)).sum + Multiset.card F =
      (F.map RoseTree.numNodes).sum) := by
  induction F using Multiset.induction_on with
  | empty => rfl
  | cons a F ih =>
    have h1 : 1 ≤ RoseTree.numNodes a := RoseTree.numNodes_pos a
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_cons, Multiset.card_cons]
    omega

/-- **Edge conservation for Δ^c cut summands**: the trace marker replaces
    the cut subtree by a unit-weight leaf, so crown edges plus trunk
    weight recover the tree weight exactly. Descends
    `cutSummandsG_numNodes` (`Core/Combinatorics/RootedTree/Cut.lean`)
    through `Nonplanar.mk`. -/
private theorem cutSummandsCN_numNodes (τ : Nonplanar (α'' ⊕ β'') → β'')
    (T : Nonplanar (α'' ⊕ β'')) :
    ∀ p ∈ cutSummandsCN τ T,
      Forest.edgeCount p.1 + p.2.numNodes = T.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α'' ⊕ β''), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  rw [ConnesKreimer.cutSummandsCP_def] at hq
  have hext : ∀ (t : RoseTree (α'' ⊕ β'')) r,
      ConnesKreimer.extractC (τ ∘ Nonplanar.mk) t = some r →
      (r.map RoseTree.numNodes).sum = 1 := by
    intro t r h
    cases t with
    | node x cs =>
      cases x with
      | inl a =>
        rw [ConnesKreimer.extractC_inl] at h
        obtain rfl := (Option.some.injEq _ _ ▸ h :
          [ConnesKreimer.traceLeaf ((τ ∘ Nonplanar.mk)
            (RoseTree.node (Sum.inl a) cs))] = r)
        simp [ConnesKreimer.traceLeaf]
      | inr b =>
        rw [ConnesKreimer.extractC_inr] at h
        exact absurd h (by simp)
  have h := ConnesKreimer.cutSummandsG_numNodes _ hext T₀ q hq
  have hsub := sum_map_numNodes_sub_one_add_card q.1
  show Forest.edgeCount (q.1.map Nonplanar.mk) +
      (Nonplanar.mk q.2).numNodes = (Nonplanar.mk T₀).numNodes
  rw [Nonplanar.numNodes_mk, Nonplanar.numNodes_mk]
  rw [show Forest.edgeCount (q.1.map Nonplanar.mk) =
      ((q.1.map (fun t => RoseTree.numNodes t - 1)).sum) from by
    show ((q.1.map Nonplanar.mk).map
        (fun T => Nonplanar.numNodes T - 1)).sum = _
    rw [Multiset.map_map]
    rfl]
  omega

/-! ### Homogeneous tensor span at fixed total edge degree -/

/-- The span of basis tensors `of' F₁ ⊗ of' F₂` with total edge count
    `n` — the homogeneous degree-`n` piece of the tensor square through
    which Δ^c factors. -/
private noncomputable def gradedTensorSpan (n : ℕ) :
    Submodule R'' (ConnesKreimer R'' (Nonplanar (α'' ⊕ β'')) ⊗[R'']
      ConnesKreimer R'' (Nonplanar (α'' ⊕ β''))) :=
  Submodule.span R'' {y | ∃ F₁ F₂ : Forest (Nonplanar (α'' ⊕ β'')),
    Forest.edgeCount F₁ + Forest.edgeCount F₂ = n ∧
    y = ConnesKreimer.of' F₁ ⊗ₜ[R''] ConnesKreimer.of' F₂}

/-- Multiplicativity of the graded tensor spans: degrees add. -/
private theorem gradedTensorSpan_mul {m k : ℕ}
    {u v : ConnesKreimer R'' (Nonplanar (α'' ⊕ β'')) ⊗[R'']
      ConnesKreimer R'' (Nonplanar (α'' ⊕ β''))}
    (hu : u ∈ gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') m)
    (hv : v ∈ gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') k) :
    u * v ∈ gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') (m + k) := by
  have hle : gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') m *
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') k ≤
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') (m + k) := by
    rw [gradedTensorSpan, gradedTensorSpan, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨a, ⟨F₁, F₂, hab, rfl⟩, b, ⟨G₁, G₂, hgk, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨F₁ + G₁, F₂ + G₂, ?_, ?_⟩
    · rw [edgeCount_add, edgeCount_add]
      omega
    · show (ConnesKreimer.of' F₁ ⊗ₜ[R''] ConnesKreimer.of' F₂) *
        (ConnesKreimer.of' G₁ ⊗ₜ[R''] ConnesKreimer.of' G₂) =
        ConnesKreimer.of' (F₁ + G₁) ⊗ₜ[R''] ConnesKreimer.of' (F₂ + G₂)
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← ConnesKreimer.of'_add,
        ← ConnesKreimer.of'_add]
  exact hle (Submodule.mul_mem_mul hu hv)

/-- Tree-level membership: `Δ^c` of a single tree is homogeneous of
    degree the tree's edge count. -/
private theorem comulCTreeN_mem (τ : Nonplanar (α'' ⊕ β'') → β'')
    (T : Nonplanar (α'' ⊕ β'')) :
    comulCTreeN (R := R'') τ T ∈
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') (T.numNodes - 1) := by
  unfold comulCTreeN
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.subset_span ⟨{T}, 0, ?_, ?_⟩
    · rw [edgeCount_singleton]
      show T.numNodes - 1 + Forest.edgeCount (0 : Forest (Nonplanar (α'' ⊕ β''))) =
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
    rw [edgeCount_singleton]
    omega

/-- Forest-level membership: `Δ^c` of a forest is homogeneous of degree
    its edge count. -/
private theorem comulCForestN_mem (τ : Nonplanar (α'' ⊕ β'') → β'')
    (F : Forest (Nonplanar (α'' ⊕ β''))) :
    comulCForestN (R := R'') τ F ∈
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'')
        (Forest.edgeCount F) := by
  induction F using Multiset.induction_on with
  | empty =>
    rw [comulCForestN_zero]
    refine Submodule.subset_span
      ⟨0, 0, rfl, ?_⟩
    rw [Algebra.TensorProduct.one_def, ConnesKreimer.of'_zero]
  | cons T F ih =>
    have hcons : comulCForestN (R := R'') τ (T ::ₘ F) =
        comulCTreeN (R := R'') τ T * comulCForestN (R := R'') τ F := by
      show comulCForestN (R := R'') τ (({T} : Multiset (Nonplanar (α'' ⊕ β''))) + F) = _
      rw [comulCForestN_add]
      congr 1
      show ((({T} : Multiset (Nonplanar (α'' ⊕ β''))).map
          (comulCTreeN (R := R'') τ)).prod) = _
      rw [Multiset.map_singleton, Multiset.prod_singleton]
    rw [hcons,
        show Forest.edgeCount (T ::ₘ F) =
          (T.numNodes - 1) + Forest.edgeCount F from by
        show ((T ::ₘ F).map (fun T => T.numNodes - 1)).sum = _
        rw [Multiset.map_cons, Multiset.sum_cons]
        rfl]
    exact gradedTensorSpan_mul (comulCTreeN_mem τ T) ih

/-- **Δ^c preserves the edge-count grading** ([marcolli-chomsky-berwick-2025]
    Lemma 1.2.10, p. 37): the coproduct of a basis forest lies in the span of
    homogeneous tensors `xi ⊗ yi` with degrees summing to the forest's edge
    count. With edge-count additivity over the product (disjoint union) and
    `comulCN_coassoc`, this gives the lemma's graded bialgebra structure on
    `V^c(𝔉_{SO_0})`. -/
theorem comulCAlgHomN_of'_mem_gradedSpan
    (τ : Nonplanar (α'' ⊕ β'') → β'') (F : Forest (Nonplanar (α'' ⊕ β''))) :
    comulCAlgHomN (R := R'') τ (ConnesKreimer.of' F) ∈
      Submodule.span R'' {y | ∃ (i j : ℕ) (_hi : i + j = Forest.edgeCount F)
        (xi yi : ConnesKreimer R'' (Nonplanar (α'' ⊕ β''))),
        xi ∈ gradedPiece (α'' ⊕ β'') i ∧
        yi ∈ gradedPiece (α'' ⊕ β'') j ∧
        y = xi ⊗ₜ[R''] yi} := by
  -- Each cut summand splits the edges (the trace marker replaces the cut
  -- subtree by a unit-weight leaf, `cutSummandsCN_numNodes`), and the
  -- homogeneous tensor spans multiply additively (`gradedTensorSpan_mul`).
  rw [comulCAlgHomN_apply_of']
  refine SetLike.le_def.mp (Submodule.span_le.mpr ?_)
    (comulCForestN_mem (R'' := R'') τ F)
  rintro y ⟨F₁, F₂, hsum, rfl⟩
  exact Submodule.subset_span
    ⟨Forest.edgeCount F₁, Forest.edgeCount F₂, hsum,
      ConnesKreimer.of' F₁, ConnesKreimer.of' F₂,
      Submodule.subset_span ⟨F₁, rfl, rfl⟩,
      Submodule.subset_span ⟨F₂, rfl, rfl⟩, rfl⟩

end EdgeGrading

end ConnesKreimer
