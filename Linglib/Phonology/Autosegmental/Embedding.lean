/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Widesubcategory
import Linglib.Core.Data.List.Factors
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

/-! #### Monotonicity under concatenation

A subgraph that embeds in `A` still embeds in `A` concatenated with anything: the
[jardine-heinz-2015] `concat` only *appends* tier positions and *index-shifts*
links, so an existing block-embedding survives — at the same offset on the left
(`concat_left`, the left block is an unshifted prefix), shifted by the prepended
block's tier lengths on the right (`concat_right`, via `get?_concat_right` and the
`shiftLink` image). These are the embedding-side of `realize`'s monoid
homomorphism: the realization of a contiguous symbol window embeds in the
realization of the whole string. -/

/-- A `get?` returning `some` is in-range (contrapositive of the out-of-range
    `none`). -/
private theorem lt_len_of_get?_isSome {a : LabeledTuple α} {i : ℕ}
    (h : (a.get? i).isSome) : i < a.len := by
  by_contra hc; rw [LabeledTuple.get?, dif_neg hc] at h; exact absurd h (by simp)

/-- **Left concat-monotonicity**: an embedding into `A` survives appending `C` on
    the right, at the same offset (`A`'s tier positions and links are an unshifted
    prefix of `A.concat C`'s). -/
theorem SubgraphEmbeds.concat_left {F A : Graph α β} (C : Graph α β)
    (h : SubgraphEmbeds F A) : SubgraphEmbeds F (A.concat C) := by
  obtain ⟨δᵤ, hδᵤ, δₗ, hδₗ, hu, hl, hlinks⟩ := h
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hδᵤ hδₗ
  refine ⟨δᵤ, ?_, δₗ, ?_, fun i hi => ?_, fun j hj => ?_, fun p hp => ?_⟩
  · simp only [Finset.mem_range, upper_concat, LabeledTuple.concat_len]; omega
  · simp only [Finset.mem_range, lower_concat, LabeledTuple.concat_len]; omega
  · have hin : i + δᵤ < A.upper.len :=
      lt_len_of_get?_isSome (by rw [hu i hi]; simp [LabeledTuple.get?, hi])
    rw [upper_concat, LabeledTuple.get?_concat_left hin]; exact hu i hi
  · have hin : j + δₗ < A.lower.len :=
      lt_len_of_get?_isSome (by rw [hl j hj]; simp [LabeledTuple.get?, hj])
    rw [lower_concat, LabeledTuple.get?_concat_left hin]; exact hl j hj
  · rw [links_concat]; exact Finset.mem_union_left _ (hlinks p hp)

/-- **Right concat-monotonicity**: an embedding into `A` survives prepending `C` on
    the left, shifted by `C`'s tier lengths (`A` becomes the index-shifted right
    block of `C.concat A`). -/
theorem SubgraphEmbeds.concat_right {F A : Graph α β} (C : Graph α β)
    (h : SubgraphEmbeds F A) : SubgraphEmbeds F (C.concat A) := by
  obtain ⟨δᵤ, hδᵤ, δₗ, hδₗ, hu, hl, hlinks⟩ := h
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hδᵤ hδₗ
  refine ⟨δᵤ + C.upper.len, ?_, δₗ + C.lower.len, ?_, fun i hi => ?_, fun j hj => ?_,
    fun p hp => ?_⟩
  · simp only [Finset.mem_range, upper_concat, LabeledTuple.concat_len]; omega
  · simp only [Finset.mem_range, lower_concat, LabeledTuple.concat_len]; omega
  · rw [upper_concat, show i + (δᵤ + C.upper.len) = C.upper.len + (i + δᵤ) by omega,
      LabeledTuple.get?_concat_right]; exact hu i hi
  · rw [lower_concat, show j + (δₗ + C.lower.len) = C.lower.len + (j + δₗ) by omega,
      LabeledTuple.get?_concat_right]; exact hl j hj
  · rw [links_concat]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(p.1 + δᵤ, p.2 + δₗ), hlinks p hp, by simp [shiftLink]; omega⟩)

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

/-! #### Link-free embedding reduces to per-tier factor occurrence

A forbidden subgraph with no association lines decouples: the two tiers impose
independent contiguous-factor constraints, with no link to fix their relative offset.
This is the structural fact behind the link-free fragment of the autosegmental →
star-free placement (`Studies.Jardine2019`): a link-free forbidden grammar reads as a
Boolean combination of per-tier factor constraints. -/

/-- A `LabeledTuple` offset-match is exactly a `toList` infix (positional companion
`List.isInfix_iff_exists_offset`). -/
private theorem exists_offset_iff_infix {γ : Type*} (a b : LabeledTuple γ) :
    (∃ δ ≤ b.len, ∀ i < a.len, b.get? (i + δ) = a.get? i) ↔ a.toList <:+: b.toList := by
  rw [List.isInfix_iff_exists_offset]
  simp only [LabeledTuple.get?_eq_getElem?, LabeledTuple.toList_length]

/-- For a forbidden subgraph **with no association lines**, embedding reduces to two
independent tier-factor occurrences: `F` subgraph-embeds in `G` iff `F`'s upper tier is
a contiguous factor of `G`'s upper tier and `F`'s lower tier is a contiguous factor of
`G`'s lower tier. The tiers are unconstrained relative to each other precisely because
there are no links to couple their offsets. -/
theorem subgraphEmbeds_iff_infix_of_links_empty (F G : Graph α β) (hF : F.links = ∅) :
    SubgraphEmbeds F G ↔
      F.upper.toList <:+: G.upper.toList ∧ F.lower.toList <:+: G.lower.toList := by
  unfold SubgraphEmbeds IsSubgraphAt
  simp only [Finset.mem_range, Nat.lt_succ_iff, hF, Finset.notMem_empty, false_implies,
    forall_const, and_true]
  rw [← exists_offset_iff_infix F.upper G.upper, ← exists_offset_iff_infix F.lower G.lower]
  constructor
  · rintro ⟨δᵤ, hδᵤ, δₗ, hδₗ, hu, hl⟩; exact ⟨⟨δᵤ, hδᵤ, hu⟩, ⟨δₗ, hδₗ, hl⟩⟩
  · rintro ⟨⟨δᵤ, hδᵤ, hu⟩, ⟨δₗ, hδₗ, hl⟩⟩; exact ⟨δᵤ, hδᵤ, δₗ, hδₗ, hu, hl⟩

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
