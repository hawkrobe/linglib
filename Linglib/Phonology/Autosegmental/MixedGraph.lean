/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Logic.Relation
import Linglib.Core.Combinatorics.MixedGraph

/-!
# Labeled mixed graphs

A labeled mixed graph `⟨V, E, A, ℓ⟩` has labeled vertices, undirected
association edges, and directed order arcs — the autosegmental representation
of [jardine-2019], with no further structure. Tiers are not part of the object:
a tier assignment `t : S → ι` on the labels induces the tier partition, and
well-formedness axioms carve the representations out of the raw graphs
relative to it.

## Main definitions

* `Autosegmental.MixedGraph V S`: the labeled mixed graph; `PrecPath` is the
  transitive closure of its arcs.
* `IsTierOrdered`, `NoInternalAssoc`, `IsSaturated`, `IsPlanar`, `IsOCPClean`:
  the §4.2 axioms (1–2, 3, 4, 5, 6; [jardine-heinz-2015] numbers the NCC and OCP
  as 4 and 5 and has no saturation axiom). Saturation is stated but not imposed,
  as in `AR.lean`; tier-orderedness includes path-closure, [jardine-2019]'s
  reading that `A` represents the order.
* `MixedGraph.Hom`: label- and association-preserving maps; `precPreserving`
  marks the full-structure homomorphisms, `MixedGraph.Iso` the full-structure
  equivalences.
* `MixedGraph.concat t`: concatenation — the vertex sum with a same-tier bridge,
  [jardine-heinz-2015] Definition 2 in the order signature, minus its `R_ID`
  merge (`OCP.collapse`); `MixedGraph.sum` is the bridge-free coproduct.
* `MixedGraphCat S`: the category of labeled mixed graphs ([jardine-2019]'s
  `GR(Γ)`), with `HasInitial` and `HasBinaryCoproducts`; `Representation t` is
  the category of autosegmental representations — the full subcategory on
  Axioms 1–3, monoidal under `concat`.

## Main results

* `concat_empty_iso`, `empty_concat_iso`, `concat_assoc_iso`,
  `isTierOrdered_concat`, `noInternalAssoc_concat`: [jardine-heinz-2015]
  Theorems 1, 3 and 4 up to `Iso`, unconditional in the order signature.
* `not_isTierOrdered_sum`: the bridge-free coproduct leaves the axiom class
  whenever the factors share a tier — Axiom 2 forces `concat`'s bridges.
* `Representation.tierColoring`: the tier map properly colors the association
  graph, so tier arity bounds its chromatic number (`edges_colorable`).

## Implementation notes

The graph components reuse `SimpleGraph` (edges are two-element sets, so
association is symmetric and loopless) and `Digraph`, bundled in
`Core/Combinatorics/MixedGraph.lean`; no cross-tier order is stored. Morphisms
default to the broad precedence-forgetting class, where the coproduct and the
OCP repair live.
Subgraph-based notions (`ASL.lean`) are signature-sensitive and do not transfer
to the order signature for free. Monoid laws hold up to `Iso`; strictness
belongs to the tiered normal form (`MultiAR.lean`).

## TODO

* The normal-form equivalence with the strict tuple presentation, with
  `IsPlanar` reducing to the per-pair NCC on normal forms.
-/

namespace Autosegmental

variable {V V₁ V₂ V₃ S ι : Type*}

/-- A labeled mixed graph `⟨V, E, A, ℓ⟩`: a mixed graph with a vertex labeling. -/
structure MixedGraph (V S : Type*) extends _root_.MixedGraph V where
  /-- The labeling (`ℓ`). -/
  label : V → S

namespace MixedGraph

/-- The precedence-path relation: the transitive closure of the arcs. -/
def PrecPath (G : MixedGraph V S) : V → V → Prop := Relation.TransGen G.arcs.Adj

/-- The tier of a vertex under a tier assignment on the alphabet. -/
def tier (t : S → ι) (G : MixedGraph V S) (v : V) : ι := t (G.label v)

/-- Tier equality propagates along precedence paths once arcs are tier-internal;
    stated as a lemma because use sites have destructured endpoints, on which
    `induction` cannot fire. -/
lemma precPath_tier {t : S → ι} {G : MixedGraph V S}
    (harc : ∀ ⦃v w⦄, G.arcs.Adj v w → G.tier t v = G.tier t w) {v w : V}
    (h : G.PrecPath v w) : G.tier t v = G.tier t w := by
  induction h with
  | single h => exact harc h
  | tail _ h ih => exact ih.trans (harc h)

/-! ### The §4.2 axioms -/

section Axioms
variable (t : S → ι) (G : MixedGraph V S)

/-- Axioms 1–2 ([jardine-2016-diss] §4.2): precedence stays within a tier,
    precedence paths totally order each tier class, no path returns to its
    origin, and the arcs are path-closed — [jardine-2019]'s reading that `A`
    represents *the order* on each string, so per tier the arcs are exactly a
    strict total order. Closure is what makes the tuple normal form arc-exact. -/
def IsTierOrdered : Prop :=
  (∀ ⦃v w⦄, G.arcs.Adj v w → G.tier t v = G.tier t w) ∧
    (∀ ⦃v w⦄, v ≠ w → G.tier t v = G.tier t w → G.PrecPath v w ∨ G.PrecPath w v) ∧
    (∀ v, ¬ G.PrecPath v v) ∧
    ∀ ⦃v w⦄, G.PrecPath v w → G.arcs.Adj v w

/-- Axiom 3: association never links precedence-path-related (tier-internal)
    vertices. Tier-free — stated on paths alone, as in the dissertation. -/
def NoInternalAssoc : Prop := ∀ ⦃v w⦄, G.edges.Adj v w → ¬ G.PrecPath v w

/-- Axiom 4 (full specification): every vertex participates in an association.
    [goldsmith-1976]'s original well-formedness condition; stated but deliberately
    not imposed — floating elements are well-formed, as in `AR.lean`. -/
def IsSaturated : Prop := ∀ v, ∃ w, G.edges.Adj v w

/-- Axiom 5, the No-Crossing Constraint in [jardine-2016-diss]'s general path
    form: no two association edges whose endpoints straddle in opposite precedence
    order. -/
def IsPlanar : Prop :=
  ∀ ⦃v v' w w'⦄, G.edges.Adj v v' → G.edges.Adj w w' → G.PrecPath v w →
    ¬ G.PrecPath w' v'

/-- Axiom 6, the OCP on melody tier `m`: precedence-adjacent vertices on `m` bear
    distinct labels. -/
def IsOCPClean (m : ι) : Prop :=
  ∀ ⦃v w⦄, G.arcs.Adj v w → G.tier t v = m → G.label v ≠ G.label w

end Axioms

/-! ### Morphisms -/

/-- A label- and association-preserving map of labeled mixed graphs. Precedence
    is deliberately *not* required — reassociation analyses move material across
    the order — so this is the broad morphism class where the coproduct and the
    OCP repair live; the precedence-preserving maps form the wide morphism class
    `precPreserving` (the legacy `AR.Hom` vs `PrecAR` split, at the foundation). -/
@[ext]
structure Hom (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) where
  /-- The vertex map. -/
  toFun : V₁ → V₂
  /-- Association edges are preserved. -/
  edge_map : ∀ ⦃v w⦄, G₁.edges.Adj v w → G₂.edges.Adj (toFun v) (toFun w)
  /-- Labels are preserved. -/
  label_comp : ∀ v, G₂.label (toFun v) = G₁.label v

/-- The edge face of a morphism, a stock graph homomorphism. -/
def Hom.edgesHom {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (f : Hom G₁ G₂) :
    G₁.edges →g G₂.edges :=
  ⟨f.toFun, fun h => f.edge_map h⟩

/-- The identity morphism. -/
def Hom.id (G : MixedGraph V S) : Hom G G :=
  ⟨_root_.id, fun _ _ h => h, fun _ => rfl⟩

/-- Composition of morphisms. -/
def Hom.comp {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {G₃ : MixedGraph V₃ S}
    (f : Hom G₁ G₂) (g : Hom G₂ G₃) : Hom G₁ G₃ :=
  ⟨g.toFun ∘ f.toFun, fun _ _ h => g.edge_map (f.edge_map h),
    fun v => (g.label_comp _).trans (f.label_comp v)⟩

/-! ### Isomorphism -/

/-- A label- and relation-preserving equivalence of labeled mixed graphs. -/
structure Iso (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) extends V₁ ≃ V₂ where
  edges_iff : ∀ v w, G₂.edges.Adj (toEquiv v) (toEquiv w) ↔ G₁.edges.Adj v w
  arcs_iff : ∀ v w, G₂.arcs.Adj (toEquiv v) (toEquiv w) ↔ G₁.arcs.Adj v w
  label_comp : ∀ v, G₂.label (toEquiv v) = G₁.label v

/-- The edge face of an isomorphism, as a stock `SimpleGraph.Iso`. -/
def Iso.edgesIso {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (e : Iso G₁ G₂) :
    G₁.edges ≃g G₂.edges :=
  ⟨e.toEquiv, fun {v w} => e.edges_iff v w⟩

/-- The arc face of an isomorphism, as a stock `RelIso`. -/
def Iso.arcsIso {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (e : Iso G₁ G₂) :
    G₁.arcs.Adj ≃r G₂.arcs.Adj :=
  ⟨e.toEquiv, fun {v w} => e.arcs_iff v w⟩

/-- An isomorphism as a morphism. -/
def Iso.toHom {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (e : Iso G₁ G₂) : Hom G₁ G₂ :=
  ⟨e.toEquiv, fun _ _ h => (e.edges_iff _ _).mpr h, e.label_comp⟩

/-- The identity isomorphism. -/
def Iso.refl (G : MixedGraph V S) : Iso G G :=
  ⟨Equiv.refl V, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩

/-- Inverse isomorphism. -/
def Iso.symm {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (e : Iso G₁ G₂) : Iso G₂ G₁ where
  toEquiv := e.toEquiv.symm
  edges_iff v w := by
    conv_rhs => rw [show v = e.toEquiv (e.toEquiv.symm v) from (e.toEquiv.apply_symm_apply v).symm,
      show w = e.toEquiv (e.toEquiv.symm w) from (e.toEquiv.apply_symm_apply w).symm]
    exact (e.edges_iff _ _).symm
  arcs_iff v w := by
    conv_rhs => rw [show v = e.toEquiv (e.toEquiv.symm v) from (e.toEquiv.apply_symm_apply v).symm,
      show w = e.toEquiv (e.toEquiv.symm w) from (e.toEquiv.apply_symm_apply w).symm]
    exact (e.arcs_iff _ _).symm
  label_comp v := by
    conv_rhs => rw [show v = e.toEquiv (e.toEquiv.symm v) from (e.toEquiv.apply_symm_apply v).symm]
    exact (e.label_comp _).symm

/-- Composition of isomorphisms. -/
def Iso.trans {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {G₃ : MixedGraph V₃ S}
    (e : Iso G₁ G₂) (f : Iso G₂ G₃) : Iso G₁ G₃ where
  toEquiv := e.toEquiv.trans f.toEquiv
  edges_iff v w := (f.edges_iff _ _).trans (e.edges_iff v w)
  arcs_iff v w := (f.arcs_iff _ _).trans (e.arcs_iff v w)
  label_comp v := (f.label_comp _).trans (e.label_comp v)

/-! ### The empty graph -/

/-- The empty labeled mixed graph, on the empty vertex type. -/
def empty (S : Type*) : MixedGraph PEmpty S := ⟨⟨⊥, ⊥⟩, PEmpty.elim⟩

theorem empty_isTierOrdered (t : S → ι) : (empty S).IsTierOrdered t :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun v => v.elim⟩

theorem empty_noInternalAssoc : (empty S).NoInternalAssoc := fun v => v.elim

/-! ### Tier-bridging concatenation

Per tier class, concatenation is the ordinal sum: blockwise arcs plus a bridging
arc from every `G₁`-vertex of a class to every same-class `G₂`-vertex. This is
the signature of [jardine-2019]'s own formulation — arcs represent *the order* on
each string, not its successor steps — under which [jardine-heinz-2015]
Definition 2's last-to-first successor bridge becomes the complete same-class
bridge: the two composites agree in precedence-closure, the relation the axioms
and results here consume (on the definability relationship between the two
signatures cf. [jardine-2017-complexity]; note that subgraph-based notions such
as `ASL.lean`'s forbidden-factor grammars are signature-sensitive and do not
transfer for free). The order form makes the bridge total (the paper's
`first`/`last` are partial) and functorial, and its monoid laws unconditional
where the successor form's associativity is conditional on the tier classes being
string graphs (the paper's Lemma 1 remark). -/

section Concat
variable (t : S → ι)

/-- Concatenation ([jardine-heinz-2015] Definition 2, minus the `R_ID` melody
    merge, in the precedence signature): stock disjoint sum on edges; on arcs the
    per-tier ordinal sum — blockwise arcs plus a bridge from each `G₁`-vertex to
    each same-tier `G₂`-vertex. -/
def concat (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) : MixedGraph (V₁ ⊕ V₂) S where
  edges := G₁.edges ⊕g G₂.edges
  arcs :=
    ⟨fun v w =>
      match v, w with
      | .inl v, .inl w => G₁.arcs.Adj v w
      | .inr v, .inr w => G₂.arcs.Adj v w
      | .inl v, .inr w => G₁.tier t v = G₂.tier t w
      | .inr _, .inl _ => False⟩
  label := Sum.elim G₁.label G₂.label

@[simp] theorem concat_label_inl (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) (v : V₁) :
    (concat t G₁ G₂).label (.inl v) = G₁.label v := rfl

@[simp] theorem concat_label_inr (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) (v : V₂) :
    (concat t G₁ G₂).label (.inr v) = G₂.label v := rfl

@[simp] theorem concat_edges (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) :
    (concat t G₁ G₂).edges = G₁.edges ⊕g G₂.edges := rfl

@[simp] theorem concat_arcs_inl_inl {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {v w : V₁} :
    (concat t G₁ G₂).arcs.Adj (.inl v) (.inl w) ↔ G₁.arcs.Adj v w := Iff.rfl

@[simp] theorem concat_arcs_inr_inr {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {v w : V₂} :
    (concat t G₁ G₂).arcs.Adj (.inr v) (.inr w) ↔ G₂.arcs.Adj v w := Iff.rfl

/-! ### Unit laws ([jardine-heinz-2015] Theorem 1) -/

/-- Concatenation with the empty graph on the right, up to isomorphism. -/
def concat_empty_iso (G : MixedGraph V S) : Iso (concat t G (empty S)) G where
  toEquiv := Equiv.sumEmpty V PEmpty
  edges_iff v w := by
    rcases v with v | v
    · rcases w with w | w
      · simp [Equiv.sumEmpty]
      · exact w.elim
    · exact v.elim
  arcs_iff v w := by
    rcases v with v | v
    · rcases w with w | w
      · exact Iff.rfl
      · exact w.elim
    · exact v.elim
  label_comp v := by
    rcases v with v | v
    · rfl
    · exact v.elim

/-- Concatenation with the empty graph on the left, up to isomorphism. -/
def empty_concat_iso (G : MixedGraph V S) : Iso (concat t (empty S) G) G where
  toEquiv := Equiv.emptySum PEmpty V
  edges_iff v w := by
    rcases v with v | v
    · exact v.elim
    · rcases w with w | w
      · exact w.elim
      · simp [Equiv.emptySum]
  arcs_iff v w := by
    rcases v with v | v
    · exact v.elim
    · rcases w with w | w
      · exact w.elim
      · exact Iff.rfl
  label_comp v := by
    rcases v with v | v
    · exact v.elim
    · rfl

/-! #### Precedence paths in a concatenation

Paths never return from the second block to the first, so blockwise paths
decompose into factor paths. -/

private lemma precPath_inr_cases {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {b : V₂}
    {y : V₁ ⊕ V₂} (h : (concat t G₁ G₂).PrecPath (.inr b) y) :
    ∃ b', y = .inr b' ∧ G₂.PrecPath b b' := by
  induction h with
  | @single y' h =>
      cases y' with
      | inl a => exact (h : False).elim
      | inr b' => exact ⟨b', rfl, .single (h : G₂.arcs.Adj b b')⟩
  | @tail y' y'' _ h ih =>
      obtain ⟨b'', rfl, hp⟩ := ih
      cases y'' with
      | inl a => exact (h : False).elim
      | inr b' => exact ⟨b', rfl, hp.tail (h : G₂.arcs.Adj b'' b')⟩

private lemma precPath_inl_cases {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {a : V₁}
    {y : V₁ ⊕ V₂} (h : (concat t G₁ G₂).PrecPath (.inl a) y) :
    (∃ a', y = .inl a' ∧ G₁.PrecPath a a') ∨ ∃ b, y = .inr b := by
  induction h with
  | @single y' h =>
      cases y' with
      | inl a' => exact Or.inl ⟨a', rfl, .single (h : G₁.arcs.Adj a a')⟩
      | inr b => exact Or.inr ⟨b, rfl⟩
  | @tail y' y'' _ h ih =>
      rcases ih with ⟨a'', rfl, hp⟩ | ⟨b, rfl⟩
      · cases y'' with
        | inl a' => exact Or.inl ⟨a', rfl, hp.tail (h : G₁.arcs.Adj a'' a')⟩
        | inr b => exact Or.inr ⟨b, rfl⟩
      · cases y'' with
        | inl a' => exact (h : False).elim
        | inr b' => exact Or.inr ⟨b', rfl⟩

@[simp] theorem concat_precPath_inl_inl {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S}
    {a a' : V₁} : (concat t G₁ G₂).PrecPath (.inl a) (.inl a') ↔ G₁.PrecPath a a' := by
  constructor
  · intro h
    rcases precPath_inl_cases t h with ⟨x, hx, hp⟩ | ⟨b, hb⟩
    · cases hx; exact hp
    · exact absurd hb (by simp)
  · intro h
    exact Relation.TransGen.lift Sum.inl (fun _ _ hab => hab) h

@[simp] theorem concat_precPath_inr_inr {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S}
    {b b' : V₂} : (concat t G₁ G₂).PrecPath (.inr b) (.inr b') ↔ G₂.PrecPath b b' := by
  constructor
  · intro h
    obtain ⟨x, hx, hp⟩ := precPath_inr_cases t h
    cases hx; exact hp
  · intro h
    exact Relation.TransGen.lift Sum.inr (fun _ _ hab => hab) h

@[simp] theorem concat_not_precPath_inr_inl {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S}
    {b : V₂} {a : V₁} : ¬ (concat t G₁ G₂).PrecPath (.inr b) (.inl a) := fun h => by
  obtain ⟨_, hx, _⟩ := precPath_inr_cases t h
  exact absurd hx (by simp)

/-! #### Axiom preservation ([jardine-heinz-2015] Theorem 4's structural half) -/

/-- Concatenation preserves Axioms 1–2, including path-closure: a cross-seam
    path forces tier equality, which is already a bridge arc. -/
theorem isTierOrdered_concat {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S}
    (h₁ : G₁.IsTierOrdered t) (h₂ : G₂.IsTierOrdered t) :
    (concat t G₁ G₂).IsTierOrdered t := by
  have hint : ∀ ⦃v w⦄, (concat t G₁ G₂).arcs.Adj v w →
      (concat t G₁ G₂).tier t v = (concat t G₁ G₂).tier t w := by
    rintro (v | v) (w | w) h
    exacts [h₁.1 h, h, h.elim, h₂.1 h]
  refine ⟨hint, ?_, ?_, ?_⟩
  · rintro (v | v) (w | w) hne htier
    · rcases h₁.2.1 (by simpa using hne) htier with hp | hp
      · exact Or.inl ((concat_precPath_inl_inl t).mpr hp)
      · exact Or.inr ((concat_precPath_inl_inl t).mpr hp)
    · exact Or.inl (.single htier)
    · exact Or.inr (.single htier.symm)
    · rcases h₂.2.1 (by simpa using hne) htier with hp | hp
      · exact Or.inl ((concat_precPath_inr_inr t).mpr hp)
      · exact Or.inr ((concat_precPath_inr_inr t).mpr hp)
  · rintro (v | v) h
    · exact h₁.2.2.1 v ((concat_precPath_inl_inl t).mp h)
    · exact h₂.2.2.1 v ((concat_precPath_inr_inr t).mp h)
  · rintro (v | v) (w | w) h
    · exact h₁.2.2.2 ((concat_precPath_inl_inl t).mp h)
    · exact precPath_tier hint h
    · exact absurd h (concat_not_precPath_inr_inl t)
    · exact h₂.2.2.2 ((concat_precPath_inr_inr t).mp h)

/-- Concatenation preserves Axiom 3: the disjoint edge sum adds no cross edges,
    and blockwise paths are factor paths. -/
theorem noInternalAssoc_concat {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S}
    (h₁ : G₁.NoInternalAssoc) (h₂ : G₂.NoInternalAssoc) :
    (concat t G₁ G₂).NoInternalAssoc := by
  rintro (v | v) (w | w) hadj hp
  · exact h₁ hadj ((concat_precPath_inl_inl t).mp hp)
  · exact absurd hadj (by simp)
  · exact absurd hadj (by simp)
  · exact h₂ hadj ((concat_precPath_inr_inr t).mp hp)

/-! #### Functoriality of concatenation -/

/-- Concatenation of morphisms is `Sum.map`: blockwise preservation from the
    factors, and label preservation transports the bridge's tier equality. Domain and codomain
    of each factor may have independent vertex types, as morphisms in `MixedGraphCat S` do. -/
def Hom.sumMap {V₁' V₂' : Type*} {G₁ : MixedGraph V₁ S} {G₁' : MixedGraph V₁' S}
    {G₂ : MixedGraph V₂ S} {G₂' : MixedGraph V₂' S}
    (f : Hom G₁ G₁') (g : Hom G₂ G₂') : Hom (concat t G₁ G₂) (concat t G₁' G₂') where
  toFun := Sum.map f.toFun g.toFun
  edge_map := by
    rintro (v | v) (w | w) h
    · exact f.edge_map h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact g.edge_map h
  label_comp := by
    rintro (v | v)
    · exact f.label_comp v
    · exact g.label_comp v

/-! #### Associativity up to isomorphism ([jardine-heinz-2015] Theorem 3) -/

/-- Concatenation is associative up to isomorphism, over `Equiv.sumAssoc`; the
    edge face is the stock `SimpleGraph.Iso.sumAssoc`, and every arc case holds
    definitionally in the order signature. -/
def concat_assoc_iso (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) (G₃ : MixedGraph V₃ S) :
    Iso (concat t (concat t G₁ G₂) G₃) (concat t G₁ (concat t G₂ G₃)) where
  toEquiv := Equiv.sumAssoc V₁ V₂ V₃
  edges_iff v w := SimpleGraph.Iso.sumAssoc.map_rel_iff
  arcs_iff v w := by
    rcases v with (a | b) | c <;> rcases w with (a' | b') | c' <;> exact Iff.rfl
  label_comp v := by
    rcases v with (a | b) | c <;> rfl

end Concat

/-! ### The bridge-free sum, and why the bridges exist

The plain blockwise sum carries no bridging arcs. It is the categorical
coproduct of the broad category (`MixedGraphCat`), but it does **not** stay in
the axiom class: whenever both factors occupy a common tier, Axiom 2's totality
fails across the seam (`not_isTierOrdered_sum`) — `concat`'s bridges are the
minimal repair that keeps concatenation inside `Representation`. -/

/-- The bridge-free blockwise sum. -/
def sum (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) : MixedGraph (V₁ ⊕ V₂) S where
  edges := G₁.edges ⊕g G₂.edges
  arcs :=
    ⟨fun v w =>
      match v, w with
      | .inl v, .inl w => G₁.arcs.Adj v w
      | .inr v, .inr w => G₂.arcs.Adj v w
      | _, _ => False⟩
  label := Sum.elim G₁.label G₂.label

@[simp] theorem sum_edges (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) :
    (G₁.sum G₂).edges = G₁.edges ⊕g G₂.edges := rfl

private lemma sum_precPath_inl {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {a : V₁}
    {y : V₁ ⊕ V₂} (h : (G₁.sum G₂).PrecPath (.inl a) y) : ∃ a', y = .inl a' := by
  induction h with
  | @single y' h =>
      cases y' with
      | inl a' => exact ⟨a', rfl⟩
      | inr b => exact (h : False).elim
  | @tail y' y'' _ h ih =>
      obtain ⟨a'', rfl⟩ := ih
      cases y'' with
      | inl a' => exact ⟨a', rfl⟩
      | inr b => exact (h : False).elim

private lemma sum_precPath_inr {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {b : V₂}
    {y : V₁ ⊕ V₂} (h : (G₁.sum G₂).PrecPath (.inr b) y) : ∃ b', y = .inr b' := by
  induction h with
  | @single y' h =>
      cases y' with
      | inl a => exact (h : False).elim
      | inr b' => exact ⟨b', rfl⟩
  | @tail y' y'' _ h ih =>
      obtain ⟨b'', rfl⟩ := ih
      cases y'' with
      | inl a => exact (h : False).elim
      | inr b' => exact ⟨b', rfl⟩

/-- Copairing out of the bridge-free sum. -/
def sumDesc {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {H : MixedGraph V₃ S}
    (f : Hom G₁ H) (g : Hom G₂ H) : Hom (G₁.sum G₂) H where
  toFun := Sum.elim f.toFun g.toFun
  edge_map := by
    rintro (v | v) (w | w) h
    · exact f.edge_map h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact g.edge_map h
  label_comp := by
    rintro (v | v)
    · exact f.label_comp v
    · exact g.label_comp v

/-- **Axiom 2 forces the bridges**: the bridge-free sum of two graphs occupying a
    common tier is never tier-ordered — same-tier vertices from the two factors
    are precedence-unrelated across the seam. -/
theorem not_isTierOrdered_sum (t : S → ι) {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S}
    (v : V₁) (w : V₂) (htier : G₁.tier t v = G₂.tier t w) :
    ¬ (G₁.sum G₂).IsTierOrdered t := by
  intro h
  rcases h.2.1 (v := .inl v) (w := .inr w) (by simp) htier with hp | hp
  · obtain ⟨a', ha⟩ := sum_precPath_inl hp
    exact absurd ha (by simp)
  · obtain ⟨b', hb⟩ := sum_precPath_inr hp
    exact absurd hb (by simp)

end MixedGraph

/-! ### The category of labeled mixed graphs -/

open CategoryTheory

universe u v

/-- An object of the category of labeled mixed graphs over `S`: a vertex type
    bundled with a labeled mixed graph on it. -/
structure MixedGraphCat (S : Type v) : Type (max (u + 1) v) where
  /-- The vertex type. -/
  V : Type u
  /-- The labeled mixed graph. -/
  graph : MixedGraph V S

namespace MixedGraphCat

instance : Category (MixedGraphCat S) where
  Hom X Y := MixedGraph.Hom X.graph Y.graph
  id X := MixedGraph.Hom.id X.graph
  comp f g := f.comp g
  id_comp _ := MixedGraph.Hom.ext rfl
  comp_id _ := MixedGraph.Hom.ext rfl
  assoc _ _ _ := MixedGraph.Hom.ext rfl

open Limits

/-- The empty graph object. -/
def empty (S : Type v) : MixedGraphCat S := ⟨PEmpty, MixedGraph.empty S⟩

instance (Y : MixedGraphCat S) : Subsingleton (empty S ⟶ Y) :=
  ⟨fun _ _ => MixedGraph.Hom.ext (funext fun v => v.elim)⟩

instance (Y : MixedGraphCat S) : Nonempty (empty S ⟶ Y) :=
  ⟨⟨PEmpty.elim, fun v => v.elim, fun v => v.elim⟩⟩

instance : HasInitial (MixedGraphCat S) := hasInitial_of_unique (empty S)

/-- The bridge-free sum object. -/
def sumObj (X Y : MixedGraphCat S) : MixedGraphCat S := ⟨X.V ⊕ Y.V, X.graph.sum Y.graph⟩

/-- Left coprojection. -/
def inl (X Y : MixedGraphCat S) : X ⟶ sumObj X Y :=
  ⟨Sum.inl, fun _ _ h => h, fun _ => rfl⟩

/-- Right coprojection. -/
def inr (X Y : MixedGraphCat S) : Y ⟶ sumObj X Y :=
  ⟨Sum.inr, fun _ _ h => h, fun _ => rfl⟩

/-- Copairing out of the bridge-free sum. -/
def desc {X Y T : MixedGraphCat S} (f : X ⟶ T) (g : Y ⟶ T) : sumObj X Y ⟶ T :=
  MixedGraph.sumDesc (f : MixedGraph.Hom _ _) (g : MixedGraph.Hom _ _)

/-- The bridge-free sum is the categorical coproduct of the broad category
    (contrast `MixedGraph.not_isTierOrdered_sum`: it leaves the axiom class,
    which is why `Representation`'s tensor is the bridged `concat` instead). -/
instance (X Y : MixedGraphCat S) : HasBinaryCoproduct X Y :=
  HasColimit.mk
    { cocone := BinaryCofan.mk (inl X Y) (inr X Y)
      isColimit := BinaryCofan.IsColimit.mk _ (fun f g => desc f g)
        (fun f g => MixedGraph.Hom.ext rfl)
        (fun f g => MixedGraph.Hom.ext rfl)
        (fun f g m h₁ h₂ => MixedGraph.Hom.ext (funext fun v => by
          rcases v with v | v
          · exact congrArg (fun φ => MixedGraph.Hom.toFun φ v) h₁
          · exact congrArg (fun φ => MixedGraph.Hom.toFun φ v) h₂)) }

instance : HasBinaryCoproducts (MixedGraphCat S) := hasBinaryCoproducts_of_hasColimit_pair _

end MixedGraphCat

/-- Precedence preservation as a morphism property: the maps that also preserve
    arcs — the model-theoretic full-structure homomorphisms, the foundation
    counterpart of the legacy `PrecAR` wide subcategory. -/
def precPreserving : MorphismProperty (MixedGraphCat S) := fun X Y f =>
  ∀ ⦃v w⦄, X.graph.arcs.Adj v w → Y.graph.arcs.Adj (f.toFun v) (f.toFun w)

instance : (precPreserving (S := S)).IsMultiplicative where
  id_mem _ := fun _ _ h => h
  comp_mem _ _ hf hg := fun _ _ h => hg (hf h)

/-! ### The category of autosegmental representations -/

variable (t : S → ι)

/-- The structural axiom class ([jardine-2016-diss] §4.2, Axioms 1–3) as an
    object property of the graph category. -/
def isRepresentation : ObjectProperty (MixedGraphCat S) := fun X =>
  X.graph.IsTierOrdered t ∧ X.graph.NoInternalAssoc

/-- The category of autosegmental representations over a tier assignment: the
    full subcategory of labeled mixed graphs satisfying the structural axioms.
    These are the formal literature's **ARs** — [jardine-2019] and
    [chandlee-jardine-2019] introduce "autosegmental representation" once and
    use `AR` as the type-name throughout; this category takes that name once the
    bipartite strict carrier currently called `AR` is dissolved into it. -/
abbrev Representation := (isRepresentation t).FullSubcategory

/-! ### The monoidal structure: morpheme concatenation -/

namespace Representation

open MonoidalCategory

variable {t}

/-- The tensor unit: the empty representation. -/
def unit : Representation t :=
  ⟨⟨PEmpty, MixedGraph.empty S⟩, MixedGraph.empty_isTierOrdered t,
    MixedGraph.empty_noInternalAssoc⟩

/-- The tensor: morpheme concatenation, staying in the axiom class by
    `isTierOrdered_concat`/`noInternalAssoc_concat`. -/
def tensor (X Y : Representation t) : Representation t :=
  ⟨⟨X.obj.V ⊕ Y.obj.V, MixedGraph.concat t X.obj.graph Y.obj.graph⟩,
    MixedGraph.isTierOrdered_concat t X.property.1 Y.property.1,
    MixedGraph.noInternalAssoc_concat t X.property.2 Y.property.2⟩

/-- Under the structural axioms the tier map properly colors the association
    graph: same-tier vertices are precedence-related (Axioms 1–2) and associated
    vertices never are (Axiom 3), so associated vertices lie on distinct tiers.
    Goldsmith's bipartite two-tier geometry is the two-colorable case. -/
def tierColoring (X : Representation t) : X.obj.graph.edges.Coloring ι :=
  SimpleGraph.Coloring.mk (X.obj.graph.tier t) fun {_ _} hadj htier =>
    (X.property.1.2.1 hadj.ne htier).elim (X.property.2 hadj) (X.property.2 hadj.symm)

/-- A representation's association graph is colorable by its tiers: tier arity
    bounds the chromatic number of the association pattern. -/
theorem edges_colorable [Fintype ι] (X : Representation t) :
    X.obj.graph.edges.Colorable (Fintype.card ι) :=
  (tierColoring X).colorable

/-- A graph isomorphism as an isomorphism of representations. -/
def mkIso {X Y : Representation t} (e : MixedGraph.Iso X.obj.graph Y.obj.graph) : X ≅ Y :=
  InducedCategory.isoMk
    ⟨e.toHom, e.symm.toHom,
      MixedGraph.Hom.ext (funext fun v => e.toEquiv.symm_apply_apply v),
      MixedGraph.Hom.ext (funext fun v => e.toEquiv.apply_symm_apply v)⟩

/-- The tensor on morphisms, as a representation morphism. -/
def tensorHomAux {X₁ Y₁ X₂ Y₂ : Representation t} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensor X₁ X₂ ⟶ tensor Y₁ Y₂ :=
  InducedCategory.homMk (MixedGraph.Hom.sumMap (G₁ := X₁.obj.graph) (G₁' := Y₁.obj.graph)
    (G₂ := X₂.obj.graph) (G₂' := Y₂.obj.graph) t f.hom g.hom)

/-- Left whiskering, as a representation morphism. -/
def whiskerLeftAux (X : Representation t) {Y₁ Y₂ : Representation t} (f : Y₁ ⟶ Y₂) :
    tensor X Y₁ ⟶ tensor X Y₂ :=
  InducedCategory.homMk (MixedGraph.Hom.sumMap (G₁ := X.obj.graph) (G₁' := X.obj.graph)
    (G₂ := Y₁.obj.graph) (G₂' := Y₂.obj.graph) t (MixedGraph.Hom.id X.obj.graph) f.hom)

/-- Right whiskering, as a representation morphism. -/
def whiskerRightAux {X₁ X₂ : Representation t} (f : X₁ ⟶ X₂) (Y : Representation t) :
    tensor X₁ Y ⟶ tensor X₂ Y :=
  InducedCategory.homMk (MixedGraph.Hom.sumMap (G₁ := X₁.obj.graph) (G₁' := X₂.obj.graph)
    (G₂ := Y.obj.graph) (G₂' := Y.obj.graph) t f.hom (MixedGraph.Hom.id Y.obj.graph))

@[simps] instance instMonoidalStruct : MonoidalCategoryStruct (Representation t) where
  tensorObj := tensor
  tensorUnit := unit
  tensorHom := tensorHomAux
  whiskerLeft := whiskerLeftAux
  whiskerRight := whiskerRightAux
  associator X Y Z := mkIso (MixedGraph.concat_assoc_iso t X.obj.graph Y.obj.graph Z.obj.graph)
  leftUnitor X := mkIso (MixedGraph.empty_concat_iso t X.obj.graph)
  rightUnitor X := mkIso (MixedGraph.concat_empty_iso t X.obj.graph)

/-- The category of autosegmental representations is monoidal under morpheme
    concatenation — [jardine-heinz-2015] Theorems 1 and 3 packaged as coherence,
    with every proof a componentwise `rfl` over the concrete sum maps. -/
instance : MonoidalCategory (Representation t) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by rcases (v : _ ⊕ _) with v | v <;> rfl)))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by rcases (v : _ ⊕ _) with v | v <;> rfl)))
    (associator_naturality := fun _ _ _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rcases (v : _ ⊕ _) with v | v <;> rfl
        · rfl)))
    (leftUnitor_naturality := fun _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · exact v.elim
        · rfl)))
    (rightUnitor_naturality := fun _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rfl
        · exact v.elim)))
    (pentagon := fun _ _ _ _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rcases (v : _ ⊕ _) with v | v
          · rcases (v : _ ⊕ _) with v | v <;> rfl
          · rfl
        · rfl)))
    (triangle := fun _ _ => InducedCategory.hom_ext
      (MixedGraph.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rcases (v : _ ⊕ _) with v | v
          · rfl
          · exact v.elim
        · rfl)))

end Representation

end Autosegmental
