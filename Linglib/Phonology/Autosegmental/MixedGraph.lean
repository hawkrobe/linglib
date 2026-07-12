/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Logic.Relation
import Linglib.Core.Combinatorics.MixedGraph

/-!
# Labeled mixed graphs — the autosegmental foundation

A labeled mixed graph `⟨V, E, A, ℓ⟩` ([jardine-heinz-2015] §2; [jardine-2016-diss]
§4.1) is the literature's most general autosegmental object: a mixed graph
(`Core/Combinatorics/MixedGraph.lean` — undirected association edges `E`, here a
`SimpleGraph` since the dissertation's edges are cardinality-two sets, and directed
precedence arcs `A`, a `Digraph`) together with a vertex labeling. As pure relations
over a vertex-type parameter it is a finite relational structure in the
model-theoretic-phonology sense — the format in which notational-equivalence results
are proved ([jardine-danis-iacoponi-2021], [oakden-2020]) — and stores no ambient
cross-tier order, which is structure the object does not have.

Tiers are not part of the object. A tier assignment `t : S → ι` on the alphabet
induces the node partition, and [jardine-2016-diss] §4.2's well-formedness axioms
carve the autosegmental representations out of the raw graphs relative to it.

Concatenation is [jardine-heinz-2015] Definition 2 *minus its `R_ID` melody merge*
(the OCP repair, modeled separately as `OCP.collapse`, matching `AR.lean`): on
edges it is the stock disjoint sum `⊕g`; on arcs it is the blockwise sum plus, per
tier class, bridging arcs from the first factor's precedence-maximal vertices to
the second factor's precedence-minimal ones. The monoid laws hold up to
structure-preserving equivalence (`MixedGraph.Iso`), not up to equality —
strictness belongs to the tiered normal form, not to the foundation.

## Main definitions

* `Autosegmental.MixedGraph V S`: a `MixedGraph V` with a labeling `label : V → S`
  (the owner-relative name: within this namespace, the labeled object, following
  the dissertation's own usage). `PrecPath` is the transitive closure of the arcs.
* The [jardine-2016-diss] §4.2 axioms, relative to a tier assignment where tiers
  matter: `IsTierOrdered` (Axioms 1–2), `NoInternalAssoc` (Axiom 3), `IsSaturated`
  (Axiom 4 — stated, deliberately not imposed, as in `AR.lean`), `IsPlanar`
  (Axiom 5, the No-Crossing Constraint in its general path form), `IsOCPClean`
  (Axiom 6).
* `MixedGraph.Hom` / `MixedGraph.Iso`: label- and relation-preserving maps and
  equivalences; faces project to the stock `SimpleGraph.Hom`/`Iso` and
  `RelHom`/`RelIso`.
* `MixedGraph.concat t`: tier-bridging concatenation on the vertex sum.
* `MixedGraphCat S`: **the category of labeled mixed graphs** (vertex type
  bundled with a graph); `Representation t` is **the category of autosegmental
  representations** — the full subcategory of the structural axiom class
  (Axioms 1–3), the category autosegmental phonology actually works in.

## Main results

* `concat_empty_iso` / `empty_concat_iso`: the unit laws up to `Iso`
  ([jardine-heinz-2015] Theorem 1).

## TODO

* Associativity up to `Iso` ([jardine-heinz-2015] Theorem 3; the edge component is
  stock `SimpleGraph.Iso.sumAssoc`, the arc component is the bridge algebra —
  conditional on the tier classes being precedence chains, per the paper's Lemma 1
  remark).
* Axiom preservation under `concat` ([jardine-heinz-2015] Theorem 4 and its
  Axiom 1–3 analogues).
* The normal-form equivalence: every graph satisfying Axioms 1–3 is isomorphic to
  a tier-indexed family of `LabeledTuple`s with per-pair links — the strict tiered
  presentation `MultiAR` builds on — with `IsPlanar` reducing to the per-pair NCC.
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

/-! ### The §4.2 axioms -/

section Axioms
variable (t : S → ι) (G : MixedGraph V S)

/-- Axioms 1–2 ([jardine-2016-diss] §4.2): precedence stays within a tier,
    precedence paths totally order each tier class, and no path returns to its
    origin. -/
def IsTierOrdered : Prop :=
  (∀ ⦃v w⦄, G.arcs.Adj v w → G.tier t v = G.tier t w) ∧
    (∀ ⦃v w⦄, v ≠ w → G.tier t v = G.tier t w → G.PrecPath v w ∨ G.PrecPath w v) ∧
    ∀ v, ¬ G.PrecPath v v

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

/-- A label- and relation-preserving map of labeled mixed graphs. -/
@[ext]
structure Hom (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) where
  /-- The vertex map. -/
  toFun : V₁ → V₂
  /-- Association edges are preserved. -/
  edge_map : ∀ ⦃v w⦄, G₁.edges.Adj v w → G₂.edges.Adj (toFun v) (toFun w)
  /-- Precedence arcs are preserved. -/
  arc_map : ∀ ⦃v w⦄, G₁.arcs.Adj v w → G₂.arcs.Adj (toFun v) (toFun w)
  /-- Labels are preserved. -/
  label_comp : ∀ v, G₂.label (toFun v) = G₁.label v

/-- The edge face of a morphism, a stock graph homomorphism. -/
def Hom.edgesHom {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (f : Hom G₁ G₂) :
    G₁.edges →g G₂.edges :=
  ⟨f.toFun, fun h => f.edge_map h⟩

/-- The arc face of a morphism, a stock relation homomorphism. -/
def Hom.arcsHom {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (f : Hom G₁ G₂) :
    G₁.arcs.Adj →r G₂.arcs.Adj :=
  ⟨f.toFun, fun h => f.arc_map h⟩

/-- The identity morphism. -/
def Hom.id (G : MixedGraph V S) : Hom G G :=
  ⟨_root_.id, fun _ _ h => h, fun _ _ h => h, fun _ => rfl⟩

/-- Composition of morphisms. -/
def Hom.comp {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {G₃ : MixedGraph V₃ S}
    (f : Hom G₁ G₂) (g : Hom G₂ G₃) : Hom G₁ G₃ :=
  ⟨g.toFun ∘ f.toFun, fun _ _ h => g.edge_map (f.edge_map h),
    fun _ _ h => g.arc_map (f.arc_map h), fun v => (g.label_comp _).trans (f.label_comp v)⟩

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

/-! ### Tier-bridging concatenation

Per tier class, concatenation adds bridging arcs from the first factor's
precedence-maximal vertices of that class to the second factor's
precedence-minimal ones. On graphs whose tier classes are precedence chains
(Axioms 1–2) this is [jardine-heinz-2015]'s last-to-first bridge; on raw graphs
it is total (a maximal-to-minimal complete bridge), where the paper's
`first`/`last` are partial. -/

section Concat
variable (t : S → ι)

/-- `v` is precedence-maximal within its tier class. -/
def IsTierMax (G : MixedGraph V S) (v : V) : Prop :=
  ∀ ⦃w⦄, G.tier t w = G.tier t v → ¬ G.PrecPath v w

/-- `v` is precedence-minimal within its tier class. -/
def IsTierMin (G : MixedGraph V S) (v : V) : Prop :=
  ∀ ⦃w⦄, G.tier t w = G.tier t v → ¬ G.PrecPath w v

/-- Concatenation ([jardine-heinz-2015] Definition 2, minus the `R_ID` melody
    merge): stock disjoint sum on edges; blockwise sum on arcs plus a bridging arc
    from each tier-maximal vertex of `G₁` to each same-tier tier-minimal vertex of
    `G₂`. -/
def concat (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) : MixedGraph (V₁ ⊕ V₂) S where
  edges := G₁.edges ⊕g G₂.edges
  arcs :=
    ⟨fun v w =>
      match v, w with
      | .inl v, .inl w => G₁.arcs.Adj v w
      | .inr v, .inr w => G₂.arcs.Adj v w
      | .inl v, .inr w => G₁.tier t v = G₂.tier t w ∧ IsTierMax t G₁ v ∧ IsTierMin t G₂ w
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

end Concat

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

end MixedGraphCat

/-! ### The category of autosegmental representations -/

variable (t : S → ι)

/-- The structural axiom class ([jardine-2016-diss] §4.2, Axioms 1–3) as an
    object property of the graph category. -/
def isRepresentation : ObjectProperty (MixedGraphCat S) := fun X =>
  X.graph.IsTierOrdered t ∧ X.graph.NoInternalAssoc

/-- The category of autosegmental representations over a tier assignment: the
    full subcategory of labeled mixed graphs satisfying the structural axioms. -/
abbrev Representation := (isRepresentation t).FullSubcategory

end Autosegmental
