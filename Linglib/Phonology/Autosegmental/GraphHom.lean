/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Group.Defs
import Linglib.Phonology.Autosegmental.NoCrossing
import Linglib.Phonology.Autosegmental.Graph

/-!
# Autosegmental graph homomorphisms — the category `Graph_AR`

The morphism / category layer of `Autosegmental.Graph`, split out of
`Graph.lean` (the object layer): label- and link-preserving `Hom`s, the
category laws, the monoidal `concatMap` bifunctor, and the
forbidden- and sub-graph embedding API ([jardine-2017]). The object layer
(structure, planarity, concatenation monoid) lives in `Graph.lean`;
only `AR.lean` and embedding consumers need this file.
-/

namespace Autosegmental

namespace Graph

variable {α β : Type*}

/-! ### Graph homomorphisms (the category `Graph_AR`)

A `Hom A B` is a label-preserving, link-preserving map between two
bipartite autosegmental graphs. Composition is function composition on
vertex indices; identity is the identity on indices. Together,
`(Graph α β, Hom, id, comp)` forms a category — the **category of
autosegmental graphs** for fixed tier-element types.

* **Forbidden subgraphs** ([jardine-2017]): an AR `G` is well-formed
  with respect to a constraint set `{F_i}` iff no `F_i` embeds (via an
  injective `Hom`) into `G`. `Embeds F G` captures this.

* **Tier projections / erasure morphisms** ([burness-mcmullin-2020]):
  tier-based subregular constructions arise as particular morphisms;
  the morphism layer is where the subregular machinery (TSL, MTSL,
  ITSL, OTSL) lives. Encoded as specific `Hom`s in consumer files.

* **Monoidal structure**: `concat` (Jardine-Heinz 2015) extends to a
  functorial operation on `Hom` via `Hom.concatMap`, making
  `Graph_AR` a monoidal category with `empty` as the unit object.
-/

/-- A graph homomorphism between two bipartite ARs. Maps upper-tier
    indices to upper-tier indices, lower-tier indices to lower-tier
    indices, preserving labels and association lines.

    The functions `fUpper` and `fLower` are defined on all of `Nat`,
    but their behavior is fully determined: on in-bounds indices, by the
    label-preservation conditions; on out-of-bounds indices, by the
    `upper_canonical` / `lower_canonical` requirement that they perform
    the **canonical shift** `i ↦ i - A.upper.length + B.upper.length`.

    The canonical-shift constraint is what makes morphism equality
    reflect the categorical notion: two homomorphisms agreeing on
    in-range indices are forced to agree everywhere. Without it, the
    monoidal-category coherence laws (right unitor naturality, pentagon,
    triangle) cannot be closed because `tensorHom f (𝟙 empty)`'s
    `concatMap`-induced behavior on out-of-range indices is the shift,
    while `f.fUpper` on out-of-range would be free. -/
structure Hom (A B : Graph α β) where
  /-- Vertex map on the upper tier. -/
  fUpper : Nat → Nat
  /-- Vertex map on the lower tier. -/
  fLower : Nat → Nat
  /-- The upper map preserves labels at in-bounds positions. -/
  upper_label : ∀ i, i < A.upper.length →
    fUpper i < B.upper.length ∧ B.upper[fUpper i]? = A.upper[i]?
  /-- The lower map preserves labels at in-bounds positions. -/
  lower_label : ∀ j, j < A.lower.length →
    fLower j < B.lower.length ∧ B.lower[fLower j]? = A.lower[j]?
  /-- Association lines are preserved. -/
  links_preserve : ∀ p ∈ A.links, (fUpper p.fst, fLower p.snd) ∈ B.links
  /-- **Canonical-shift on out-of-range upper indices.** For
      `i ≥ A.upper.length`, `fUpper i = i - A.upper.length + B.upper.length`.
      This makes morphism equality reflect categorical equality: two
      morphisms agreeing in-range must agree everywhere. -/
  upper_canonical : ∀ i, A.upper.length ≤ i →
    fUpper i = i - A.upper.length + B.upper.length
  /-- **Canonical-shift on out-of-range lower indices.** For
      `j ≥ A.lower.length`, `fLower j = j - A.lower.length + B.lower.length`. -/
  lower_canonical : ∀ j, A.lower.length ≤ j →
    fLower j = j - A.lower.length + B.lower.length

namespace Hom

variable {A B C D : Graph α β}

/-- The identity homomorphism. -/
def id (A : Graph α β) : Hom A A where
  fUpper := _root_.id
  fLower := _root_.id
  upper_label _ h := ⟨h, rfl⟩
  lower_label _ h := ⟨h, rfl⟩
  links_preserve _ hp := hp
  upper_canonical i hi := by show i = _; omega
  lower_canonical j hj := by show j = _; omega

/-- Composition of homomorphisms (in diagrammatic order: `f.comp g`
    is "do `f` first, then `g`"). -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  fUpper := g.fUpper ∘ f.fUpper
  fLower := g.fLower ∘ f.fLower
  upper_label i hi := by
    obtain ⟨hf, hfl⟩ := f.upper_label i hi
    obtain ⟨hg, hgl⟩ := g.upper_label (f.fUpper i) hf
    refine ⟨hg, ?_⟩
    rw [Function.comp_apply, hgl, hfl]
  lower_label j hj := by
    obtain ⟨hf, hfl⟩ := f.lower_label j hj
    obtain ⟨hg, hgl⟩ := g.lower_label (f.fLower j) hf
    refine ⟨hg, ?_⟩
    rw [Function.comp_apply, hgl, hfl]
  links_preserve p hp :=
    g.links_preserve _ (f.links_preserve p hp)
  upper_canonical i hi := by
    show g.fUpper (f.fUpper i) = _
    rw [f.upper_canonical i hi, g.upper_canonical _ (by omega)]
    omega
  lower_canonical j hj := by
    show g.fLower (f.fLower j) = _
    rw [f.lower_canonical j hj, g.lower_canonical _ (by omega)]
    omega

@[ext]
theorem ext {f g : Hom A B} (hUp : f.fUpper = g.fUpper) (hLow : f.fLower = g.fLower) :
    f = g := by
  cases f; cases g; congr

/-! #### Category laws -/

theorem id_comp (f : Hom A B) : (Hom.id A).comp f = f := by
  ext <;> rfl

theorem comp_id (f : Hom A B) : f.comp (Hom.id B) = f := by
  ext <;> rfl

theorem comp_assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext <;> rfl

/-! #### Concatenation as a bifunctor (`concatMap`)

Given homomorphisms `f : Hom A A'` and `g : Hom B B'`, the
**concatenation tensor** `f ⊗ g` is a homomorphism
`A.concat B → A'.concat B'`. The index maps split case-wise: an
index `i < A.upper.length` routes through `f`; an index
`≥ A.upper.length` (i.e., in B's part of `A.concat B`'s tier)
routes through `g`, shifted by `A'.upper.length` to land in B's
part of `A'.concat B`.

The asymmetric `A.InBounds` hypothesis is necessary: the case-split
on `p.fst < A.upper.length` for an A-link only matches the if-branch
when `A` is in-bounds. Without it, an A-link with out-of-bounds first
coordinate would route to the else-branch, which uses `g`, not `f` —
breaking `links_preserve`. `B.InBounds` is *not* needed: shifted
B-links have `p.fst ≥ A.upper.length` unconditionally, so the
else-branch fires regardless of whether the underlying B-index was
in-bounds.

`concatMap` is the bifunctor underlying the `MonoidalCategory`
structure on the autosegmental category (`AR α β`) — see
`Phonology/Autosegmental/AR.lean`.
-/

/-- Concatenation tensor on homomorphisms: `f ⊗ g`. -/
def concatMap {A A' B B' : Graph α β}
    (hA : A.InBounds) (f : Hom A A') (g : Hom B B') :
    Hom (A.concat B) (A'.concat B') where
  fUpper i := if i < A.upper.length then f.fUpper i
              else g.fUpper (i - A.upper.length) + A'.upper.length
  fLower j := if j < A.lower.length then f.fLower j
              else g.fLower (j - A.lower.length) + A'.lower.length
  upper_label := by
    intro i hi
    simp only [upper_concat, List.length_append] at hi
    by_cases hib : i < A.upper.length
    · -- Case 1: i in A's part.
      simp only [hib, if_true]
      obtain ⟨h1, h2⟩ := f.upper_label i hib
      refine ⟨by simp [upper_concat, List.length_append]; omega, ?_⟩
      simp only [upper_concat]
      rw [List.getElem?_append_left h1, List.getElem?_append_left hib]
      exact h2
    · -- Case 2: i in B's shifted part.
      simp only [hib, if_false]
      push_neg at hib
      have hib' : i - A.upper.length < B.upper.length := by omega
      obtain ⟨h1, h2⟩ := g.upper_label (i - A.upper.length) hib'
      refine ⟨by simp [upper_concat, List.length_append]; omega, ?_⟩
      simp only [upper_concat]
      have hge_target : A'.upper.length ≤ g.fUpper (i - A.upper.length) + A'.upper.length := by omega
      have hge_source : A.upper.length ≤ i := hib
      rw [List.getElem?_append_right hge_target, List.getElem?_append_right hge_source]
      have hsub : g.fUpper (i - A.upper.length) + A'.upper.length - A'.upper.length =
                  g.fUpper (i - A.upper.length) := by omega
      rw [hsub]
      exact h2
  lower_label := by
    intro j hj
    simp only [lower_concat, List.length_append] at hj
    by_cases hjb : j < A.lower.length
    · simp only [hjb, if_true]
      obtain ⟨h1, h2⟩ := f.lower_label j hjb
      refine ⟨by simp [lower_concat, List.length_append]; omega, ?_⟩
      simp only [lower_concat]
      rw [List.getElem?_append_left h1, List.getElem?_append_left hjb]
      exact h2
    · simp only [hjb, if_false]
      push_neg at hjb
      have hjb' : j - A.lower.length < B.lower.length := by omega
      obtain ⟨h1, h2⟩ := g.lower_label (j - A.lower.length) hjb'
      refine ⟨by simp [lower_concat, List.length_append]; omega, ?_⟩
      simp only [lower_concat]
      have hge_target : A'.lower.length ≤ g.fLower (j - A.lower.length) + A'.lower.length := by omega
      have hge_source : A.lower.length ≤ j := hjb
      rw [List.getElem?_append_right hge_target, List.getElem?_append_right hge_source]
      have hsub : g.fLower (j - A.lower.length) + A'.lower.length - A'.lower.length =
                  g.fLower (j - A.lower.length) := by omega
      rw [hsub]
      exact h2
  links_preserve := by
    intro p hp
    rw [links_concat, Finset.mem_union] at hp
    rw [links_concat, Finset.mem_union]
    rcases hp with hp | hp
    · -- Case A: p ∈ A.links. By A.InBounds the if-branches fire.
      left
      obtain ⟨hAu, hAl⟩ := hA p hp
      show (if p.fst < A.upper.length then f.fUpper p.fst else _,
            if p.snd < A.lower.length then f.fLower p.snd else _) ∈ A'.links
      rw [if_pos hAu, if_pos hAl]
      exact f.links_preserve p hp
    · -- Case B: p is a shifted B-link.
      right
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [Finset.mem_image]
      refine ⟨(g.fUpper q.fst, g.fLower q.snd), g.links_preserve q hq, ?_⟩
      have hgu : ¬ q.fst + A.upper.length < A.upper.length := by omega
      have hgl : ¬ q.snd + A.lower.length < A.lower.length := by omega
      have hsubu : q.fst + A.upper.length - A.upper.length = q.fst := by omega
      have hsubl : q.snd + A.lower.length - A.lower.length = q.snd := by omega
      simp [shiftLink, hgu, hgl, hsubu, hsubl]
  upper_canonical i hi := by
    -- For `i ≥ (A.concat B).upper.length = A.upper.length + B.upper.length`,
    -- the else-branch fires (since `i ≥ A.upper.length`) and
    -- `i - A.upper.length ≥ B.upper.length` triggers `g.upper_canonical`.
    simp only [upper_concat, List.length_append] at hi
    have hib : ¬ i < A.upper.length := by omega
    show (if i < A.upper.length then _ else _) = _
    simp only [hib, if_false]
    rw [g.upper_canonical _ (by omega)]
    simp only [upper_concat, List.length_append]
    omega
  lower_canonical j hj := by
    simp only [lower_concat, List.length_append] at hj
    have hjb : ¬ j < A.lower.length := by omega
    show (if j < A.lower.length then _ else _) = _
    simp only [hjb, if_false]
    rw [g.lower_canonical _ (by omega)]
    simp only [lower_concat, List.length_append]
    omega

/-! #### Functoriality of `concatMap` -/

/-- The identity on `A.concat B` factors through identities on `A` and
    `B`: `concatMap (id A) (id B) = id (A.concat B)`. Foundational for
    the bifunctor structure (`tensor_id` law of mathlib's
    `MonoidalCategory`). -/
theorem concatMap_id {A B : Graph α β} (hA : A.InBounds) :
    concatMap hA (id A) (id B) = id (A.concat B) := by
  ext i
  · simp only [concatMap, id]
    by_cases hi : i < A.upper.length
    · simp [hi]
    · simp [hi]; omega
  · simp only [concatMap, id]
    by_cases hi : i < A.lower.length
    · simp [hi]
    · simp [hi]; omega

/-- Composition factors through `concatMap`:
    `(concatMap f g).comp (concatMap f' g') = concatMap (f.comp f') (g.comp g')`.
    The other half of the bifunctor laws (`tensor_comp` in mathlib's
    `MonoidalCategory`). -/
theorem concatMap_comp {A A' A'' B B' B'' : Graph α β}
    (hA : A.InBounds) (hA' : A'.InBounds)
    (f : Hom A A') (f' : Hom A' A'') (g : Hom B B') (g' : Hom B' B'') :
    (concatMap hA f g).comp (concatMap hA' f' g') =
      concatMap hA (f.comp f') (g.comp g') := by
  ext i
  · by_cases hi : i < A.upper.length
    · obtain ⟨hf, _⟩ := f.upper_label i hi
      simp [comp, concatMap, hi, hf]
    · have hshift : ¬ g.fUpper (i - A.upper.length) + A'.upper.length < A'.upper.length := by
        omega
      simp [comp, concatMap, hi, hshift]
  · by_cases hi : i < A.lower.length
    · obtain ⟨hf, _⟩ := f.lower_label i hi
      simp [comp, concatMap, hi, hf]
    · have hshift : ¬ g.fLower (i - A.lower.length) + A'.lower.length < A'.lower.length := by
        omega
      simp [comp, concatMap, hi, hshift]

end Hom

/-! ### Forbidden-subgraph embedding ([jardine-2017])

Two notions of embedding are formalised:

* **`Embeds F G`** — the weaker, *category-theoretic* notion: there is
  a label-and-link-preserving injective `Hom F G`. The morphism need
  not preserve precedence (list order); F's positions can be mapped to
  any positions of G as long as labels and association lines match.
* **`SubgraphEmbeds F G`** — the stronger, *autosegmental* notion that
  [jardine-2017] actually uses: there exist offsets `(δᵤ, δₗ)`
  such that F's upper and lower tiers appear as a *contiguous block*
  of G's tiers at those offsets, and F's links match G's links
  shifted by the offset. Equivalently: the embedding is a *translation*
  that preserves precedence edges (implicit in list order).

For Jardine 2017-style forbidden-subgraph analyses
([chandlee-jardine-2019], [burness-mcmullin-2020]), use
`SubgraphEmbeds`. The weaker `Embeds` is the underlying category-
theoretic structure.
-/

/-- `F` **embeds** into `G` iff there is an injective homomorphism
    `F → G`. Category-theoretic notion: label-and-link-preserving
    injection on indices. Does not preserve precedence. -/
def Embeds (F G : Graph α β) : Prop :=
  ∃ h : Hom F G, Function.Injective h.fUpper ∧ Function.Injective h.fLower

/-- Embedding is reflexive: every AR embeds into itself via the
    identity. -/
theorem Embeds.refl (G : Graph α β) : Embeds G G :=
  ⟨Hom.id G, Function.injective_id, Function.injective_id⟩

/-- Embedding is transitive: a composition of injective homomorphisms
    is injective. -/
theorem Embeds.trans {F G H : Graph α β}
    (hFG : Embeds F G) (hGH : Embeds G H) : Embeds F H := by
  obtain ⟨f, hfU, hfL⟩ := hFG
  obtain ⟨g, hgU, hgL⟩ := hGH
  refine ⟨f.comp g, ?_, ?_⟩
  · exact hgU.comp hfU
  · exact hgL.comp hfL

/-! ### Subgraph embedding (precedence-preserving translation)

The autosegmental notion of "F is a connected subgraph of G" used in
[jardine-2017]: F appears as a contiguous block of G at some
offset. Equivalently, the embedding is a translation by `(δᵤ, δₗ)`.
-/

/-- F's upper tier appears at offset `δᵤ` in G's upper tier, F's
    lower tier appears at offset `δₗ` in G's lower tier, and all of
    F's association lines are present in G at the appropriate offset.
    The `IsSubgraphAt` formulation of [jardine-2017]'s
    connected-subgraph embedding. -/
def IsSubgraphAt (F G : Graph α β) (δᵤ δₗ : Nat) : Prop :=
  (∀ i, i < F.upper.length → G.upper[i + δᵤ]? = F.upper[i]?) ∧
  (∀ j, j < F.lower.length → G.lower[j + δₗ]? = F.lower[j]?) ∧
  (∀ p ∈ F.links, (p.fst + δᵤ, p.snd + δₗ) ∈ G.links)

instance [DecidableEq α] [DecidableEq β] (F G : Graph α β) (δᵤ δₗ : Nat) :
    Decidable (IsSubgraphAt F G δᵤ δₗ) := by
  unfold IsSubgraphAt; infer_instance

/-- `F` **subgraph-embeds** into `G` iff there is an offset
    `(δᵤ, δₗ)` placing F as a contiguous block inside G. The
    autosegmental connected-subgraph embedding of [jardine-2017]. -/
def SubgraphEmbeds (F G : Graph α β) : Prop :=
  ∃ δᵤ ∈ Finset.range (G.upper.length + 1),
  ∃ δₗ ∈ Finset.range (G.lower.length + 1),
    IsSubgraphAt F G δᵤ δₗ

instance [DecidableEq α] [DecidableEq β] (F G : Graph α β) :
    Decidable (SubgraphEmbeds F G) := by
  unfold SubgraphEmbeds; infer_instance

/-- `SubgraphEmbeds` is reflexive: F is a subgraph of itself at
    offset `(0, 0)`. -/
theorem SubgraphEmbeds.refl (G : Graph α β) : SubgraphEmbeds G G := by
  refine ⟨0, ?_, 0, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i hi; simp
  · intro j hj; simp
  · intro p hp; simpa using hp

end Graph

end Autosegmental
