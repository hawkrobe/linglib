/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Cut
import Linglib.Core.Data.RoseTree.FilterMap

open RoseTree

/-!
# The Δ^c enumeration filters onto the Δ^ρ enumeration

On a `Sum.inl`-embedded tree, the Δ^c cut enumeration (`cutSummandsCP`)
cuts at exactly the sites of the Δ^ρ enumeration (`cutSummandsP`):
applying `RoseTree.filterMap Sum.getLeft?` to each Δ^c summand — which
erases the trace placeholders — recovers the corresponding Δ^ρ summand,
as an equality of multisets. Both sides are stated `Option`-valued
(filtered on the left, embedded by `some` on the right), which keeps the
maps total.

This is the combinatorial content of the Δ^d = Δ^ρ comparison
([marcolli-chomsky-berwick-2025] Lemma 1.3.10); the algebra layer
(`Core/Algebra/RootedTree/Coproduct/Deletion.lean`) transports it
through a cut-summand tensor builder.

## Main results

* `ConnesKreimer.cutSummandsCP_map_inl_filterMap` — per-tree: filtered
  Δ^c summands of `RoseTree.map Sum.inl t` are the Δ^ρ summands of `t`.
* `ConnesKreimer.cutListSummandsG_map_inl_filterMap`,
  `ConnesKreimer.augActionG_map_inl_filterMap` — children-list and
  per-child companions of the mutual induction.
-/

namespace ConnesKreimer

variable {α β : Type*}

mutual

/-- **Per-tree**: filtering the Δ^c cut summands of an embedded tree
    yields the `some`-embedded Δ^ρ cut summands. -/
theorem cutSummandsCP_map_inl_filterMap (τ : RoseTree (α ⊕ β) → β) :
    ∀ (t : RoseTree α),
      (cutSummandsCP τ (RoseTree.map Sum.inl t)).map
          (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
            (RoseTree.filterMap Sum.getLeft?))
        = (cutSummandsP t).map (Prod.map (Multiset.map some) some)
  | .node a cs => by
    rw [RoseTree.map_node, cutSummandsCP_node, cutSummandsP_node,
        Multiset.map_map, Multiset.map_map]
    rw [show (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
              (RoseTree.filterMap (Sum.getLeft? (α := α) (β := β)))) ∘
          (fun p : Multiset (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β)) =>
            (p.1, RoseTree.node (Sum.inl a) p.2)) =
        (fun q : Multiset (Option (RoseTree α)) × List (RoseTree α) =>
          (q.1, some (RoseTree.node a q.2))) ∘
          (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
            (RoseTree.filterMapList Sum.getLeft?)) from by
      funext p
      rfl]
    rw [show (Prod.map (Multiset.map (some : RoseTree α → Option (RoseTree α)))
              (some : RoseTree α → Option (RoseTree α))) ∘
          (fun p : Multiset (RoseTree α) × List (RoseTree α) =>
            (p.1, RoseTree.node a p.2)) =
        (fun q : Multiset (Option (RoseTree α)) × List (RoseTree α) =>
          (q.1, some (RoseTree.node a q.2))) ∘
          (Prod.map (Multiset.map some) id) from by
      funext p; rfl]
    rw [← Multiset.map_map, ← Multiset.map_map,
        cutListSummandsG_map_inl_filterMap τ cs]

/-- **Children-list**: companion of `cutSummandsCP_map_inl_filterMap` at
    the list level, with `RoseTree.filterMapList` on the remainder. -/
theorem cutListSummandsG_map_inl_filterMap (τ : RoseTree (α ⊕ β) → β) :
    ∀ (cs : List (RoseTree α)),
      (cutListSummandsG (extractC τ) (List.map (RoseTree.map Sum.inl) cs)).map
          (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
            (RoseTree.filterMapList Sum.getLeft?))
        = (cutListSummandsP cs).map (Prod.map (Multiset.map some) id)
  | [] => by
    rw [List.map_nil, cutListSummandsG_nil, cutListSummandsP_nil,
        Multiset.map_singleton, Multiset.map_singleton]
    rfl
  | c :: cs' => by
    rw [List.map_cons, cutListSummandsG_cons, cutListSummandsP_cons',
        Multiset.map_map, Multiset.map_map]
    rw [show (Prod.map (Multiset.map (RoseTree.filterMap
                (Sum.getLeft? (α := α) (β := β))))
              (RoseTree.filterMapList Sum.getLeft?)) ∘
          (fun p : (Multiset (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β))) ×
                   (Multiset (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β))) =>
            (p.1.1 + p.2.1, p.1.2 ++ p.2.2)) =
        (fun q : (Multiset (Option (RoseTree α)) × List (RoseTree α)) ×
                 (Multiset (Option (RoseTree α)) × List (RoseTree α)) =>
          (q.1.1 + q.2.1, q.1.2 ++ q.2.2)) ∘
          (Prod.map
            (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
              (RoseTree.filterMapList Sum.getLeft?))
            (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
              (RoseTree.filterMapList Sum.getLeft?))) from by
      funext p
      show ((p.1.1 + p.2.1).map (RoseTree.filterMap Sum.getLeft?),
            RoseTree.filterMapList Sum.getLeft? (p.1.2 ++ p.2.2)) = _
      rw [Multiset.map_add, RoseTree.filterMapList_append]
      rfl]
    rw [show (Prod.map (Multiset.map (some : RoseTree α → Option (RoseTree α)))
              (id : List (RoseTree α) → List (RoseTree α))) ∘
          (combineP_fn (α := α)) =
        (fun q : (Multiset (Option (RoseTree α)) × List (RoseTree α)) ×
                 (Multiset (Option (RoseTree α)) × List (RoseTree α)) =>
          (q.1.1 + q.2.1, q.1.2 ++ q.2.2)) ∘
          (Prod.map (Prod.map (Multiset.map some) Option.toList)
                    (Prod.map (Multiset.map some) id)) from by
      funext p
      obtain ⟨⟨F₁, opt⟩, ⟨F₂, l₂⟩⟩ := p
      cases opt with
      | none =>
        show ((F₁ + F₂).map some, l₂) = (F₁.map some + F₂.map some, [] ++ l₂)
        rw [Multiset.map_add]
        rfl
      | some r =>
        show ((F₁ + F₂).map some, r :: l₂) =
             (F₁.map some + F₂.map some, [r] ++ l₂)
        rw [Multiset.map_add]
        rfl]
    rw [← Multiset.map_map, ← Multiset.map_map,
        map_prodMap_product_G, map_prodMap_product_G,
        augActionG_map_inl_filterMap τ c,
        cutListSummandsG_map_inl_filterMap τ cs']

/-- **Per-child**: companion of `cutSummandsCP_map_inl_filterMap` for
    the augmented action, with the Δ^ρ `Option` remainder listed via
    `Option.toList`. The extract-whole branch filters to `({some c}, [])`,
    matching Δ^ρ's delete branch `({c}, none)`. -/
theorem augActionG_map_inl_filterMap (τ : RoseTree (α ⊕ β) → β) :
    ∀ (c : RoseTree α),
      (augActionG (extractC τ) (RoseTree.map Sum.inl c)).map
          (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
            (RoseTree.filterMapList Sum.getLeft?))
        = (augActionP c).map (Prod.map (Multiset.map some) Option.toList)
  | c => by
    have hextract : extractC τ (RoseTree.map Sum.inl c) =
        some [traceLeaf (τ (RoseTree.map Sum.inl c))] := by
      obtain ⟨a, cs⟩ := c
      rfl
    rw [augActionG_eq_some _ _ _ hextract, augActionP_eq,
        Multiset.map_cons, Multiset.map_cons, Multiset.map_map, Multiset.map_map]
    congr 1
    · show (({RoseTree.map Sum.inl c} : Multiset _).map
              (RoseTree.filterMap Sum.getLeft?),
            RoseTree.filterMapList Sum.getLeft?
              [traceLeaf (τ (RoseTree.map Sum.inl c))]) =
           (({c} : Multiset (RoseTree α)).map some,
            Option.toList (none : Option (RoseTree α)))
      rw [Multiset.map_singleton, Multiset.map_singleton,
          RoseTree.filterMap_getLeft?_map_inl]
      rfl
    · rw [show (Prod.map (Multiset.map (RoseTree.filterMap
                  (Sum.getLeft? (α := α) (β := β))))
                (RoseTree.filterMapList Sum.getLeft?)) ∘
            (fun p : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) =>
              (p.1, [p.2])) =
          (fun q : Multiset (Option (RoseTree α)) × Option (RoseTree α) =>
            (q.1, q.2.toList)) ∘
            (Prod.map (Multiset.map (RoseTree.filterMap Sum.getLeft?))
              (RoseTree.filterMap Sum.getLeft?)) from by
        funext p
        show (p.1.map (RoseTree.filterMap Sum.getLeft?),
              RoseTree.filterMapList Sum.getLeft? [p.2]) = _
        rw [RoseTree.filterMapList_singleton]
        rfl]
      rw [show (Prod.map (Multiset.map (some : RoseTree α → Option (RoseTree α)))
                (Option.toList (α := RoseTree α))) ∘
            (fun p : Multiset (RoseTree α) × RoseTree α => (p.1, some p.2)) =
          (fun q : Multiset (Option (RoseTree α)) × Option (RoseTree α) =>
            (q.1, q.2.toList)) ∘
            (Prod.map (Multiset.map some) some) from by
        funext p; rfl]
      rw [← Multiset.map_map, ← Multiset.map_map,
          show cutSummandsG (extractC τ) (RoseTree.map Sum.inl c) =
            cutSummandsCP τ (RoseTree.map Sum.inl c) from rfl,
          cutSummandsCP_map_inl_filterMap τ c]

end

end ConnesKreimer
