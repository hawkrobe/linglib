/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Widesubcategory
import Linglib.Phonology.Autosegmental.AR

/-!
# Embeddings of autosegmental graphs

Two flavours of precedence-preserving embedding between autosegmental graphs, and
the relationship between them:

* **Subgraph embedding** (`Graph.SubgraphEmbeds`/`Free`) — a *containment* relation
  on `Graph` objects: "does the forbidden block `F` occur as a contiguous block of
  `G` at some offset?". This is [jardine-2017]'s connected-subgraph embedding and
  the basis of his **banned-subgraph grammars** (Ch. 5): `G` is well-formed w.r.t. a
  forbidden set `{Fᵢ}` exactly when no `Fᵢ` embeds (`Free`). Stays at the `Graph`
  layer, with no morphism machinery — consumers (`Studies.Jardine2017`) need only
  the object layer.

* **Precedence-preserving morphisms** (`precPreserving`/`PrecAR`) — an *order-embedding*
  property of `AR.Hom`s, promoted to a wide subcategory. These are the morphisms that
  preserve the linear order on each tier; they are the home of phonological
  *process* functoriality (Jardine Ch. 7; `Studies.LaoideKemp2026`'s lenition is a
  functor on `PrecAR` but not on the full `AR`). The **morphism-axis** analogue of
  the **object-axis** `WellFormedAR` (`ObjectProperty.FullSubcategory` for planarity);
  here the tool is `MorphismProperty` + `WideSubcategory`, with the `Category`
  inherited free from `IsMultiplicative`.

The two are connected but distinct: a `SubgraphEmbeds` block embedding (the offset
translation `j ↦ j + δ`) *is* an order-embedding, so subgraph translations are
canonical instances of precedence-preserving maps — but `precPreserving` is strictly
more general (any order-embedding, not only contiguous translations), and the two
serve orthogonal purposes (well-formedness vs functoriality).
-/

namespace Autosegmental

variable {α β : Type*}

/-! ### Subgraph embedding (the containment relation; banned-subgraph grammars) -/

namespace Graph

/-- F's upper tier appears at offset `δᵤ` in G's upper tier, F's lower tier at
    offset `δₗ` in G's lower tier, and all of F's association lines are present
    in G shifted by `(δᵤ, δₗ)`. -/
def IsSubgraphAt (F G : Graph α β) (δᵤ δₗ : Nat) : Prop :=
  (∀ i, i < F.upper.len → G.upper.get? (i + δᵤ) = F.upper.get? i) ∧
  (∀ j, j < F.lower.len → G.lower.get? (j + δₗ) = F.lower.get? j) ∧
  (∀ p ∈ F.links, (p.fst + δᵤ, p.snd + δₗ) ∈ G.links)

instance [DecidableEq α] [DecidableEq β] (F G : Graph α β) (δᵤ δₗ : Nat) :
    Decidable (IsSubgraphAt F G δᵤ δₗ) := by
  unfold IsSubgraphAt; infer_instance

/-- `F` **subgraph-embeds** into `G` iff some offset `(δᵤ, δₗ)` places F as a
    contiguous block inside G — [jardine-2017]'s connected-subgraph embedding. -/
def SubgraphEmbeds (F G : Graph α β) : Prop :=
  ∃ δᵤ ∈ Finset.range (G.upper.len + 1),
  ∃ δₗ ∈ Finset.range (G.lower.len + 1),
    IsSubgraphAt F G δᵤ δₗ

instance [DecidableEq α] [DecidableEq β] (F G : Graph α β) :
    Decidable (SubgraphEmbeds F G) := by
  unfold SubgraphEmbeds; infer_instance

/-- `SubgraphEmbeds` is reflexive: F is a subgraph of itself at offset `(0, 0)`. -/
theorem SubgraphEmbeds.refl (G : Graph α β) : SubgraphEmbeds G G := by
  refine ⟨0, ?_, 0, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i hi; simp
  · intro j hj; simp
  · intro p hp; simpa using hp

/-- `G` is **free of** the forbidden block patterns `fs`: no `F ∈ fs`
    subgraph-embeds into `G`. This is [jardine-2017]'s forbidden-substructure
    well-formedness predicate — the positional analogue of `G` being
    `SimpleGraph.Free` of a family of patterns — letting a consumer write
    `G.Free forbidden` for the whole set rather than conjoining one
    `¬ SubgraphEmbeds Fᵢ G` per pattern. -/
def Free (G : Graph α β) (fs : List (Graph α β)) : Prop :=
  ∀ F ∈ fs, ¬ SubgraphEmbeds F G

instance [DecidableEq α] [DecidableEq β] (G : Graph α β) (fs : List (Graph α β)) :
    Decidable (G.Free fs) := by unfold Free; infer_instance

end Graph

/-! ### Precedence-preserving morphisms (the order-embedding wide subcategory) -/

open CategoryTheory MorphismProperty

/-- A morphism of `AR` is **precedence-preserving** iff both tier maps are
    order-embeddings (strictly monotone `Fin`-reindexings) — it preserves the
    linear order on each tier. `SubgraphEmbeds` block translations are canonical
    instances; this property is more general (any order-embedding). -/
def precPreserving : MorphismProperty (AR α β) :=
  fun _ _ f => StrictMono f.fU.toFun ∧ StrictMono f.fL.toFun

instance : (precPreserving (α := α) (β := β)).IsMultiplicative where
  id_mem _ := ⟨strictMono_id, strictMono_id⟩
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1, hg.2.comp hf.2⟩

/-- A precedence-preserving morphism **reflects the initial position**: an
    order-embedding sends only the slot-0 lower element to slot 0. This is the
    structural content of "lenition targets the word-initial position". -/
theorem precPreserving.reflects_zero {A B : AR α β} {f : AR.Hom A B}
    (hf : precPreserving f) (j : Fin A.lower.len) (h0 : (f.fL.toFun j : ℕ) = 0) :
    (j : ℕ) = 0 := by
  have h := hf.2.le_iff_le (a := j) (b := ⟨0, j.pos⟩)
  simp only [Fin.le_def, h0, Nat.le_zero] at h
  omega

/-- The **precedence-preserving wide subcategory** of `AR`: same objects, with
    morphisms restricted to order-embedding tier maps. The `Category` instance is
    inherited from `WideSubcategory` via `precPreserving.IsMultiplicative`. -/
abbrev PrecAR (α β : Type*) := WideSubcategory (precPreserving (α := α) (β := β))

end Autosegmental
