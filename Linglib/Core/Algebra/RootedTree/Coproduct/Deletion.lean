/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.BigOperators.Multiset
import Linglib.Core.Data.Multiset.FilterMap
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Linglib.Core.Algebra.RootedTree.Coproduct.TraceNonplanar
import Linglib.Core.Combinatorics.RootedTree.CutFilterMap
import Linglib.Core.Data.RoseTree.FilterMap

open RoseTree RoseTree.Nonplanar

/-!
# The deletion coproduct Δ^d

The deletion variant of the Connes-Kreimer admissible-cut coproduct
([marcolli-chomsky-berwick-2025] Lemma 1.3.10, p. 44), obtained from the
trace coproduct Δ^c (`Coproduct/TraceNonplanar.lean`) by erasing
trace-placeholder leaves from both tensor channels:
`Δ^d = (Π_{d,c} ⊗ Π_{d,c}) ∘ Δ^c`, where `Π_{d,c}` erases
trace-placeholder leaves.

## Main definitions

* `ConnesKreimer.eraseTracesAlgHom` — `Π_{d,c}` as an algebra hom
  `ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R] ConnesKreimer R (Nonplanar α)`,
  induced by the tree-level partial map (`Core/Data/RoseTree/FilterMap.lean`)
  via `ConnesKreimer.mapDomainAlgHom`.
* `ConnesKreimer.embedInlAlgHom` — the `Sum.inl` embedding as an algebra hom.
* `ConnesKreimer.comulDN` — the deletion coproduct, as the composite above.

## Main results

* `ConnesKreimer.eraseTracesAlgHom_comp_embedInlAlgHom` — erasure
  inverts the embedding.
* `ConnesKreimer.comulDN_embedInl_eq_comulAlgHomN` — on embedded
  trace-free trees, Δ^d agrees with the pruning coproduct Δ^ρ.

## Implementation notes

[marcolli-chomsky-berwick-2025] work with binary trees: their Δ^d
composes with a second projection `Π_{d,p}` contracting degree-1
vertices to restore binary structure, and their comparison
`Δ^d = (id ⊗ Π_{d,p}) ∘ Δ^ρ` holds only weakly (Lemma 1.2.12, a
distance-≤-1 multiplicity discrepancy). On n-ary `Nonplanar` trees
`Π_{d,p}` is the identity, the erasure alone defines Δ^d, and the Δ^ρ
comparison is an exact equality. We erase on both tensor channels so the
target carrier is uniformly trace-free; on the embedded trace-free
inputs of the comparison the crown-channel erasure is the identity,
recovering MCB's one-channel form `(id ⊗ Π_{d,c}) ∘ Δ^c`.

Δ^d carries no separate `Bialgebra` structure: consumers compose through
`embedInlAlgHom` and use the Δ^ρ instance (`instBialgebraRho`,
`Coproduct/PruningDuality.lean`).

## Status

`[UPSTREAM]` candidate.
-/


namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}



/-! ## The trace-erasure algebra hom Π_{d,c} -/

/-- The **trace-erasure algebra hom** `Π_{d,c}`: erase trace subtrees componentwise across each basis
    forest, dropping trace-rooted trees
    (`Multiset.filterMapAddMonoidHom (Nonplanar.filterMap Sum.getLeft?)`), lifted
    through `ConnesKreimer.mapDomainAlgHom`. -/
noncomputable def eraseTracesAlgHom :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.mapDomainAlgHom
    (Multiset.filterMapAddMonoidHom (Nonplanar.filterMap Sum.getLeft?))

@[simp] theorem eraseTracesAlgHom_of' (F : Forest (Nonplanar (α ⊕ β))) :
    eraseTracesAlgHom (R := R) (of' F) =
      of' (R := R) (F.filterMap (Nonplanar.filterMap Sum.getLeft?)) := by
  rw [eraseTracesAlgHom, ConnesKreimer.mapDomainAlgHom_of']
  rfl

/-- `eraseTracesAlgHom` on a single tree: the trace-erased tree if the root
    survives, `1` if the root is a trace placeholder. -/
@[simp] theorem eraseTracesAlgHom_ofTree (T : Nonplanar (α ⊕ β)) :
    eraseTracesAlgHom (R := R) (ofTree T) =
      (Nonplanar.filterMap Sum.getLeft? T).elim 1 ofTree := by
  rw [show (ofTree T : ConnesKreimer R (Nonplanar (α ⊕ β))) = of' {T} from rfl,
      eraseTracesAlgHom_of',
      show ({T} : Forest (Nonplanar (α ⊕ β))) = T ::ₘ 0 from rfl,
      Multiset.filterMap_cons, Multiset.filterMap_zero, add_zero]
  cases Nonplanar.filterMap Sum.getLeft? T with
  | none => simp [of'_zero]
  | some t' => simp [of'_singleton]

/-! ## Sum.inl embedding

The embedding `α → α ⊕ β` lifts componentwise to trees and forests via
`RoseTree.map` / `Nonplanar.map` / `Multiset.map`. -/

/-- The **`Sum.inl` embedding algebra hom**: relabel every basis forest
    componentwise along `Sum.inl`, embedding trace-free trees into the
    marked alphabet. -/
noncomputable def embedInlAlgHom :
    ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.mapDomainAlgHom (Multiset.mapAddMonoidHom (Nonplanar.map Sum.inl))

@[simp] theorem embedInlAlgHom_of' (F : Forest (Nonplanar α)) :
    embedInlAlgHom (R := R) (β := β) (of' F) =
      of' (R := R) (F.map (Nonplanar.map Sum.inl)) := by
  rw [embedInlAlgHom, ConnesKreimer.mapDomainAlgHom_of']
  rfl


/-! ### Erasure inverts embed -/

/-- Erasure inverts the `Sum.inl` embedding: trace-free trees survive
    the round trip. -/
theorem eraseTracesAlgHom_comp_embedInlAlgHom :
    (eraseTracesAlgHom (R := R) (α := α) (β := β)).comp embedInlAlgHom =
      AlgHom.id R (ConnesKreimer R (Nonplanar α)) := by
  apply ConnesKreimer.algHom_ext
  intro F
  show eraseTracesAlgHom (embedInlAlgHom (of' F)) = of' F
  rw [embedInlAlgHom_of', eraseTracesAlgHom_of', Multiset.filterMap_map,
      show ((Nonplanar.filterMap Sum.getLeft? ∘ Nonplanar.map Sum.inl :
              Nonplanar α → Option (Nonplanar α))) = some from
        funext fun T => Nonplanar.filterMap_getLeft?_map_inl T,
      Multiset.filterMap_some]

/-! ## Δ^d definition

`comulDN := (Π_{d,c} ⊗ Π_{d,c}) ∘ Δ^c` — MCB Lemma 1.3.10 by
construction. Target carrier is `Nonplanar α` (trace-free). -/

/-- The **Δ^d coproduct on `ConnesKreimer R (Nonplanar (α ⊕ β))`** as an
    algebra hom, with trace-erasure applied to both channels of
    `comulCAlgHomN τ`. -/
noncomputable def comulDN (τ : Nonplanar (α ⊕ β) → β) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R) (α := α) (β := β))
    eraseTracesAlgHom).comp (comulCAlgHomN τ)

/-! ## Equivalence with Δ^ρ via embedding

The substantive MCB-correspondence: starting from a trace-free
`T : Nonplanar α` and embedding into `Nonplanar (α ⊕ β)` via `Sum.inl`,
applying `comulDN` (= Δ^c then erasure) gives the same result as applying
`comulAlgHomN` (Δ^ρ) directly.

In MCB's binary substrate this requires the additional `Π_{d,p}`
rebinarize step on the right channel; in our n-ary substrate, the
erasure is enough. -/

/-- `eraseTracesAlgHom` applied to an embedded single tree recovers the
    tree: single-tree form of `Nonplanar.filterMap_getLeft?_map_inl`. -/
private theorem eraseTracesAlgHom_ofTree_map_inl
    (T : Nonplanar α) :
    eraseTracesAlgHom (R := R) (β := β)
        (ofTree (Nonplanar.map Sum.inl T)) =
      ofTree T := by
  rw [eraseTracesAlgHom_ofTree, Nonplanar.filterMap_getLeft?_map_inl]
  rfl


/-! ### The cut-summand tensor builder

`Option`-tolerant on both channels: a filtered-out crown entry (`none`)
is dropped, a filtered-out trunk contributes `1`. The filtered Δ^c
summands and the `some`-embedded Δ^ρ summands of
`Core/Combinatorics/RootedTree/CutFilterMap.lean` both land in its
domain. -/

private noncomputable def cutTensor
    (q : Multiset (Option (RoseTree α)) × Option (RoseTree α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (of' (q.1.filterMap (Option.map Nonplanar.mk)) : ConnesKreimer R (Nonplanar α))
    ⊗ₜ[R] (q.2.map Nonplanar.mk).elim 1 ofTree

/-- The `(Π ⊗ Π)`-image of a projected Δ^c summand is `cutTensor` of its
    filtered form. -/
private theorem cutTensor_filterMap
    (p : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β)) :
    eraseTracesAlgHom (R := R) (of' (p.1.map Nonplanar.mk)) ⊗ₜ[R]
        eraseTracesAlgHom (ofTree (Nonplanar.mk p.2)) =
      cutTensor (R := R)
        (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
          (RoseTree.filterMap Sum.getLeft?) p) := by
  unfold cutTensor
  congr 1
  · rw [eraseTracesAlgHom_of', Prod.map_fst, Multiset.filterMap_map,
        Multiset.filterMap_map]
    rfl
  · rw [eraseTracesAlgHom_ofTree, Nonplanar.filterMap_mk, Prod.map_snd]

/-- On `some`-embedded Δ^ρ summands, `cutTensor` is the plain summand
    tensor. -/
private theorem cutTensor_some (p : Multiset (RoseTree α) × RoseTree α) :
    cutTensor (R := R) (Prod.map (Multiset.map some) some p) =
      (of' (p.1.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
        ofTree (Nonplanar.mk p.2) := by
  unfold cutTensor
  congr 1
  · rw [Prod.map_fst, Multiset.filterMap_map,
        show (Option.map Nonplanar.mk ∘ (some : RoseTree α → Option (RoseTree α)))
          = (some ∘ (Nonplanar.mk : RoseTree α → Nonplanar α)) from rfl,
        Multiset.filterMap_eq_map]


/-! ### Lift from tree-level to Nonplanar -/

/-- Per-tree form of the Δ^ρ comparison, descended from the cut-summand
    identity `cutSummandsCP_map_inl_filterMap` through the quotient. -/
private theorem eraseTraces_comulCTreeN_map_inl
    (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar α) :
    (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R) (α := α) (β := β))
        eraseTracesAlgHom) (comulCTreeN τ (Nonplanar.map Sum.inl T)) =
      comulTreeN T := by
  refine Quotient.inductionOn T ?_
  intro t
  -- Unfold both sides via comulCTreeN definition.
  show (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R)) eraseTracesAlgHom)
        (comulCTreeN τ (Nonplanar.mk (RoseTree.map Sum.inl t))) =
       comulTreeN (Nonplanar.mk t)
  unfold comulCTreeN comulTreeNG
  rw [map_add]
  -- First summand: (S ⊗ S) (ofTree (mk (embed t)) ⊗ 1) = ofTree (mk t) ⊗ 1.
  rw [show (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R)) eraseTracesAlgHom)
            (ofTree (Nonplanar.mk (RoseTree.map Sum.inl t)) ⊗ₜ[R]
              (1 : ConnesKreimer R (Nonplanar (α ⊕ β)))) =
          ofTree (Nonplanar.mk t) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) from by
    rw [Algebra.TensorProduct.map_tmul, map_one]
    congr 1
    -- mk (RoseTree.map Sum.inl t) = embedInl (mk t)
    exact eraseTracesAlgHom_ofTree_map_inl (Nonplanar.mk t)]
  congr 1
  -- Second summand: (S ⊗ S) (sum over cuts) = sum over Δ^ρ cuts.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R)) eraseTracesAlgHom)]
  simp only [Multiset.map_map]
  -- Reduce sum-of-(S⊗S)-applied to sum of per-summand tensors.
  rw [show ((Algebra.TensorProduct.map (eraseTracesAlgHom (R := R)) eraseTracesAlgHom) ∘
            (fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) =>
              of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)) =
          (fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) =>
            eraseTracesAlgHom (of' (R := R) p.1) ⊗ₜ[R]
              eraseTracesAlgHom (ofTree p.2)) from by
    funext p
    rw [Function.comp_apply, Algebra.TensorProduct.map_tmul]]
  -- Cuts descend to tree-level: cutSummandsCN τ (mk t') = (cutSummandsCP (τ ∘ mk) t').map projSummand.
  rw [show cutSummandsCN τ (Nonplanar.mk (RoseTree.map Sum.inl t)) =
        (cutSummandsCP (τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl t)).map projSummand from
      cutSummandsCN_mk _ _]
  rw [show cutSummandsN (Nonplanar.mk t) =
        (cutSummandsP t).map projSummand from
      cutSummandsN_mk _]
  rw [Multiset.map_map, Multiset.map_map]
  -- Both integrands factor through the Option-tolerant tensor builder.
  rw [show ((fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) =>
              eraseTracesAlgHom (of' (R := R) p.1) ⊗ₜ[R]
                eraseTracesAlgHom (ofTree p.2)) ∘ projSummand) =
          (cutTensor (R := R)) ∘
            (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
              (RoseTree.filterMap Sum.getLeft?)) from by
    funext p
    exact cutTensor_filterMap p]
  rw [show ((fun p : Forest (Nonplanar α) × Nonplanar α =>
              (of' (R := R) p.1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
                ofTree p.2) ∘ projSummand) =
          (cutTensor (R := R)) ∘ (Prod.map (Multiset.map some) some) from by
    funext p
    exact (cutTensor_some p).symm]
  rw [← Multiset.map_map, ← Multiset.map_map, cutSummandsCP_map_inl_filterMap]

/-- Forest-level form of the Δ^ρ comparison: the per-tree form lifted
    multiplicatively. -/
private theorem eraseTraces_comulCForestN_map_inl
    (τ : Nonplanar (α ⊕ β) → β) (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R) (α := α) (β := β))
        eraseTracesAlgHom) (comulCForestN τ (F.map (Nonplanar.map Sum.inl))) =
      comulForestN F := by
  induction F using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, comulCForestN_zero, comulForestN_zero, map_one]
  | cons T F' ih =>
    rw [Multiset.map_cons, comulForestN_cons]
    -- comulCForestN τ (T_embed ::ₘ F'_embed) = comulCTreeN τ T_embed * comulCForestN τ F'_embed
    have hcons : comulCForestN (R := R) τ
        (Nonplanar.map Sum.inl T ::ₘ F'.map (Nonplanar.map Sum.inl)) =
        comulCTreeN τ (Nonplanar.map Sum.inl T) *
          comulCForestN (R := R) τ (F'.map (Nonplanar.map Sum.inl)) :=
      comulForestNG_cons _ _ _
    rw [hcons, map_mul, eraseTraces_comulCTreeN_map_inl, ih]

/-- On embedded trace-free trees the deletion coproduct agrees with the
    pruning coproduct Δ^ρ: the n-ary form of the
    [marcolli-chomsky-berwick-2025] comparison
    `Δ^d = (id ⊗ Π_{d,p}) ∘ Δ^ρ`, exact here because the rebinarize step
    `Π_{d,p}` is the identity. -/
theorem comulDN_embedInl_eq_comulAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    (comulDN (R := R) τ).comp (embedInlAlgHom (R := R) (β := β)) =
      comulAlgHomN := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (eraseTracesAlgHom (R := R))
          eraseTracesAlgHom) (comulCAlgHomN τ (embedInlAlgHom (of' F))) =
       comulAlgHomN (of' F)
  rw [embedInlAlgHom_of', comulCAlgHomN_apply_of', comulAlgHomN_apply_of']
  exact eraseTraces_comulCForestN_map_inl τ F

end ConnesKreimer

