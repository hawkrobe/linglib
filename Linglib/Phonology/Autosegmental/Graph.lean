/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Monoidal.Widesubcategory
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Logic.Relation
import Linglib.Core.Combinatorics.MixedGraph

/-!
# Labeled mixed graphs

A labeled mixed graph `⟨V, E, A, ℓ⟩` has labeled vertices, undirected
association edges, and directed order arcs — the autosegmental representation
of [jardine-2019], with no further structure. The graph is a `MixedGraph` (Core)
and the labeling a map `ℓ : V → S`; `Graph S` bundles the two. Tiers are
not part of the object: a tier assignment `t : S → ι` on the labels induces a
vertex coloring `X.tier t`, and well-formedness axioms carve the representations
out of the raw graphs relative to it.

## Main definitions

* `IsTierOrdered`, `NoInternalAssoc`, `IsSaturated`, `IsPlanar`, `IsOCPClean`:
  the §4.2 axioms (1–2, 3, 4, 5, 6; [jardine-heinz-2015] numbers the NCC and OCP
  as 4 and 5 and has no saturation axiom) as predicates on a `MixedGraph` and, for
  tier-relative axioms, a vertex coloring `c : V → ι`. Saturation is stated but
  not imposed; tier-orderedness includes path-closure
  (`MixedGraph.PrecPath`), [jardine-2019]'s reading that `A` represents the order.
* `Graph S`: the labeled mixed graph ([jardine-2019]'s `GR(Γ)`) and the
  category thereof, with `HasInitial` and `HasBinaryCoproducts`;
  `Graph.Hom` are label- and association-preserving maps, `precPreserving`
  marks the full-structure homomorphisms, `Graph.Iso` the full-structure
  equivalences.
* `Graph.concat t`: concatenation — the vertex sum with a same-tier
  bridge, [jardine-heinz-2015] Definition 2 in the order signature, minus its
  `R_ID` merge (`OCP.collapse`); `Graph.sum` is the bridge-free coproduct.
* `AR t`: the category of autosegmental representations — the full
  subcategory of labeled mixed graphs on Axioms 1–3, monoidal under `concat`.

## Main results

* `concatEmptyIso`, `emptyConcatIso`, `concatAssocIso`,
  `isTierOrdered_concat`, `noInternalAssoc_concat`, `isPlanar_concat`:
  [jardine-heinz-2015] Theorems 1, 3 and 4 up to `Iso`, unconditional in the
  order signature; `isPlanar_concat` is [jardine-2019]'s NCC-preservation.
* `not_isTierOrdered_sum`: the bridge-free coproduct leaves the axiom class
  whenever the factors share a tier — Axiom 2 forces `concat`'s bridges.
* `AR.tierColoring`: the tier map properly colors the association
  graph, so tier arity bounds its chromatic number (`edges_colorable`).

## Implementation notes

`concat` bridges *every* same-tier pair, so its arcs are order-closed
representatives: [jardine-2019]'s operative concatenation bridges one partial
`(last, first)` pair per tier, and the two forms are interconvertible as Hasse
diagram ↔ transitive closure on the finite per-tier strict orders. The complete
bridge is total and functorial where `first`/`last` are partial and not
hom-preserved, and its monoid laws are unconditional where the successor form's
associativity requires string-graph tier classes ([jardine-heinz-2015]'s Lemma 1
remark). The choice is not free elsewhere: subgraph-based notions such as
`ASL.lean`'s forbidden factors are signature-sensitive ([jardine-2017-complexity]).

## TODO

* Package `AR.ofData` and `AR.isoOfReaderEq` (`NormalForm.lean`) as a
  `CategoryTheory.Equivalence` between the strict tuple category and the
  finite representations, and reduce `IsPlanar` on normal forms to the
  per-pair `IsNonCrossing` of the link relation.
-/

namespace Autosegmental

variable {V S ι : Type*}

/-! ### The §4.2 axioms -/

section Axioms
variable (G : MixedGraph V)

/-- Axioms 1–2 ([jardine-2016-diss] §4.2): the arcs are tier-internal and
    strictly totally order each fiber of the coloring `c`. -/
structure IsTierOrdered (c : V → ι) : Prop where
  /-- Arcs never leave a tier. -/
  tier_eq : ∀ ⦃v w⦄, G.arcs.Adj v w → c v = c w
  /-- Distinct same-tier vertices are arc-comparable. -/
  total : ∀ ⦃v w⦄, v ≠ w → c v = c w → G.arcs.Adj v w ∨ G.arcs.Adj w v
  /-- No vertex precedes itself. -/
  irrefl : ∀ v, ¬ G.arcs.Adj v v
  /-- Arcs compose. -/
  trans : ∀ ⦃u v w⦄, G.arcs.Adj u v → G.arcs.Adj v w → G.arcs.Adj u w

/-- Axiom 3: association never links precedence-path-related (tier-internal)
    vertices. Tier-free — stated on arcs alone, as in the dissertation. -/
def NoInternalAssoc : Prop := ∀ ⦃v w⦄, G.edges.Adj v w → ¬ G.arcs.Adj v w

/-- Axiom 4 (full specification): every vertex participates in an association.
    [goldsmith-1976]'s original well-formedness condition; stated but deliberately
    not imposed — floating elements are well-formed. -/
def IsSaturated : Prop := ∀ v, ∃ w, G.edges.Adj v w

/-- Axiom 5, the No-Crossing Constraint in [jardine-2016-diss]'s general path
    form: no two association edges whose endpoints straddle in opposite precedence
    order. -/
def IsPlanar : Prop :=
  ∀ ⦃v v' w w'⦄, G.edges.Adj v v' → G.edges.Adj w w' → G.arcs.Adj v w → ¬ G.arcs.Adj w' v'

/-- Axiom 6, the OCP on melody tier `m`: precedence-adjacent vertices on `m`
    bear distinct labels. Adjacency is the covering relation of the arcs — in
    the order-closed signature bare arcs relate all order-comparable pairs,
    which would wrongly ban any repeated label anywhere on the tier. -/
def IsOCPClean (ℓ : V → S) (t : S → ι) (m : ι) : Prop :=
  ∀ ⦃v w⦄, G.arcs.Adj v w → (∀ u, ¬ (G.arcs.Adj v u ∧ G.arcs.Adj u w)) →
    t (ℓ v) = m → ℓ v ≠ ℓ w

end Axioms

variable {G : MixedGraph V} {c : V → ι}

/-- On the axiom class, precedence paths coincide with the arcs — the
    dissertation's `≺`. -/
theorem IsTierOrdered.precPath_eq (h : IsTierOrdered G c) : G.PrecPath = G.arcs.Adj :=
  haveI : IsTrans V G.arcs.Adj := ⟨h.trans⟩
  Relation.transGen_eq_self

/-- The classed form of the axioms: on each tier the arcs are a strict total
    order. Feeds `linearOrderOfSTO` for sorting the fibers. -/
theorem IsTierOrdered.isStrictTotalOrder (h : IsTierOrdered G c) (i : ι) :
    IsStrictTotalOrder {v // c v = i} (G.arcs.Adj · ·) where
  trichotomous a b hab hba :=
    Subtype.ext <| of_not_not fun hne => (h.total hne (a.2.trans b.2.symm)).elim hab hba
  irrefl a := h.irrefl a
  trans _ _ _ hab hbc := h.trans hab hbc

/-! ### The category of labeled mixed graphs -/

/-- An object of the category of labeled mixed graphs over `S`: a vertex type
    with a mixed graph `⟨V, E, A⟩` on it and a labeling `ℓ : V → S` — the
    literature's labeled mixed graph `⟨V, E, A, ℓ⟩` / [jardine-2019]'s `GR(Γ)`. -/
structure Graph (S : Type*) where
  /-- The vertex type. -/
  V : Type*
  /-- The mixed graph: undirected association edges and directed order arcs. -/
  graph : MixedGraph V
  /-- The labeling (`ℓ`). -/
  label : V → S

namespace Graph

variable {X Y Z : Graph S}

/-- The tier of a vertex under a tier assignment on the alphabet. -/
def tier (t : S → ι) (X : Graph S) : X.V → ι := t ∘ X.label

/-! ### Morphisms -/

/-- A label- and association-preserving map of labeled mixed graphs. Precedence
    is deliberately *not* required — reassociation analyses move material across
    the order — so this is the broad morphism class where the coproduct and the
    OCP repair live; the precedence-preserving maps form the wide morphism class
    `precPreserving` (the legacy `AR.Hom` vs `PrecAR` split, at the foundation). -/
@[ext]
structure Hom (X Y : Graph S) where
  /-- The vertex map. -/
  toFun : X.V → Y.V
  /-- Association edges are preserved. -/
  edge_map : ∀ ⦃v w⦄, X.graph.edges.Adj v w → Y.graph.edges.Adj (toFun v) (toFun w)
  /-- Labels are preserved. -/
  label_comp : ∀ v, Y.label (toFun v) = X.label v

/-- The edge face of a morphism, a stock graph homomorphism. -/
def Hom.edgesHom (f : Hom X Y) : X.graph.edges →g Y.graph.edges :=
  ⟨f.toFun, fun h => f.edge_map h⟩

/-- The identity morphism. -/
def Hom.id (X : Graph S) : Hom X X :=
  ⟨_root_.id, fun _ _ h => h, fun _ => rfl⟩

/-- Composition of morphisms. -/
def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, fun _ _ h => g.edge_map (f.edge_map h),
    fun v => (g.label_comp _).trans (f.label_comp v)⟩

/-! ### Isomorphism -/

/-- A label- and relation-preserving equivalence of labeled mixed graphs. -/
structure Iso (X Y : Graph S) extends X.V ≃ Y.V where
  /-- Association edges correspond. -/
  edges_iff : ∀ v w, Y.graph.edges.Adj (toEquiv v) (toEquiv w) ↔ X.graph.edges.Adj v w
  /-- Order arcs correspond. -/
  arcs_iff : ∀ v w, Y.graph.arcs.Adj (toEquiv v) (toEquiv w) ↔ X.graph.arcs.Adj v w
  /-- Labels are preserved. -/
  label_comp : ∀ v, Y.label (toEquiv v) = X.label v

/-- The edge face of an isomorphism, as a stock `SimpleGraph.Iso`. -/
def Iso.edgesIso (e : Iso X Y) : X.graph.edges ≃g Y.graph.edges :=
  ⟨e.toEquiv, e.edges_iff _ _⟩

/-- The arc face of an isomorphism, as a stock `RelIso`. -/
def Iso.arcsIso (e : Iso X Y) : X.graph.arcs.Adj ≃r Y.graph.arcs.Adj :=
  ⟨e.toEquiv, e.arcs_iff _ _⟩

/-- An isomorphism as a morphism. -/
def Iso.toHom (e : Iso X Y) : Hom X Y :=
  ⟨e.toEquiv, fun _ _ h => (e.edges_iff _ _).mpr h, e.label_comp⟩

/-- The identity isomorphism. -/
def Iso.refl (X : Graph S) : Iso X X :=
  ⟨Equiv.refl X.V, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩

/-- Inverse isomorphism. -/
def Iso.symm (e : Iso X Y) : Iso Y X where
  toEquiv := e.toEquiv.symm
  edges_iff v w := by simpa using (e.edges_iff (e.toEquiv.symm v) (e.toEquiv.symm w)).symm
  arcs_iff v w := by simpa using (e.arcs_iff (e.toEquiv.symm v) (e.toEquiv.symm w)).symm
  label_comp v := by simpa using (e.label_comp (e.toEquiv.symm v)).symm

/-- Composition of isomorphisms. -/
def Iso.trans (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  toEquiv := e.toEquiv.trans f.toEquiv
  edges_iff v w := (f.edges_iff _ _).trans (e.edges_iff v w)
  arcs_iff v w := (f.arcs_iff _ _).trans (e.arcs_iff v w)
  label_comp v := (f.label_comp _).trans (e.label_comp v)

/-! ### The empty graph -/

/-- The empty labeled mixed graph, on the empty vertex type. -/
def empty (S : Type*) : Graph S := ⟨PEmpty, ⟨⊥, ⊥⟩, PEmpty.elim⟩

theorem isTierOrdered_empty (t : S → ι) : IsTierOrdered (empty S).graph ((empty S).tier t) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun v => v.elim⟩

theorem noInternalAssoc_empty : NoInternalAssoc (empty S).graph := fun v => v.elim

/-! ### Tier-bridging concatenation

Per tier class, concatenation is the ordinal sum: blockwise arcs plus a bridge
from every `X`-vertex to every same-tier `Y`-vertex. On the choice of the
complete bridge over [jardine-2019]'s partial `(last, first)` pair, see the
implementation notes above. -/

section Concat
variable (t : S → ι)

/-- Concatenation ([jardine-heinz-2015] Definition 2, minus the `R_ID` melody
    merge, in the precedence signature): stock disjoint sum on edges; on arcs the
    per-tier ordinal sum — blockwise arcs plus a bridge from each `X`-vertex to
    each same-tier `Y`-vertex. -/
def concat (X Y : Graph S) : Graph S where
  V := X.V ⊕ Y.V
  graph.edges := X.graph.edges ⊕g Y.graph.edges
  graph.arcs :=
    ⟨fun
      | .inl v, .inl w => X.graph.arcs.Adj v w
      | .inr v, .inr w => Y.graph.arcs.Adj v w
      | .inl v, .inr w => X.tier t v = Y.tier t w
      | .inr _, .inl _ => False⟩
  label := Sum.elim X.label Y.label

@[simp] theorem concat_label_inl (v : X.V) : (concat t X Y).label (.inl v) = X.label v := rfl

@[simp] theorem concat_label_inr (v : Y.V) : (concat t X Y).label (.inr v) = Y.label v := rfl

@[simp] theorem concat_edges :
    (concat t X Y).graph.edges = X.graph.edges ⊕g Y.graph.edges := rfl

@[simp] theorem concat_arcs_inl_inl {v w : X.V} :
    (concat t X Y).graph.arcs.Adj (.inl v) (.inl w) ↔ X.graph.arcs.Adj v w := Iff.rfl

@[simp] theorem concat_arcs_inr_inr {v w : Y.V} :
    (concat t X Y).graph.arcs.Adj (.inr v) (.inr w) ↔ Y.graph.arcs.Adj v w := Iff.rfl

@[simp] theorem concat_arcs_inl_inr {v : X.V} {w : Y.V} :
    (concat t X Y).graph.arcs.Adj (.inl v) (.inr w) ↔ X.tier t v = Y.tier t w := Iff.rfl

@[simp] theorem not_concat_arcs_inr_inl {v : Y.V} {w : X.V} :
    ¬ (concat t X Y).graph.arcs.Adj (.inr v) (.inl w) := fun h => h

/-! ### Unit laws ([jardine-heinz-2015] Theorem 1) -/

/-- Concatenation with the empty graph on the right, up to isomorphism. -/
def concatEmptyIso (X : Graph S) : Iso (concat t X (empty S)) X where
  toEquiv := Equiv.sumEmpty X.V PEmpty
  edges_iff
    | .inl _, .inl _ => Iff.rfl
    | .inl _, .inr w => w.elim
    | .inr v, _ => v.elim
  arcs_iff
    | .inl _, .inl _ => Iff.rfl
    | .inl _, .inr w => w.elim
    | .inr v, _ => v.elim
  label_comp
    | .inl _ => rfl
    | .inr v => v.elim

/-- Concatenation with the empty graph on the left, up to isomorphism. -/
def emptyConcatIso (X : Graph S) : Iso (concat t (empty S) X) X where
  toEquiv := Equiv.emptySum PEmpty X.V
  edges_iff
    | .inl v, _ => v.elim
    | .inr _, .inl w => w.elim
    | .inr _, .inr _ => Iff.rfl
  arcs_iff
    | .inl v, _ => v.elim
    | .inr _, .inl w => w.elim
    | .inr _, .inr _ => Iff.rfl
  label_comp
    | .inl v => v.elim
    | .inr _ => rfl

/-! #### Axiom preservation ([jardine-heinz-2015] Theorem 4's structural half) -/

/-- Concatenation preserves Axioms 1–2; transitivity through the seam holds
    because arcs are tier-internal. -/
theorem isTierOrdered_concat
    (h₁ : IsTierOrdered X.graph (X.tier t)) (h₂ : IsTierOrdered Y.graph (Y.tier t)) :
    IsTierOrdered (concat t X Y).graph ((concat t X Y).tier t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (v | v) (w | w) h
    exacts [h₁.tier_eq h, h, h.elim, h₂.tier_eq h]
  · rintro (v | v) (w | w) hne htier
    · rcases h₁.total (by rintro rfl; exact hne rfl) htier with hp | hp
      exacts [Or.inl hp, Or.inr hp]
    · exact Or.inl htier
    · exact Or.inr htier.symm
    · rcases h₂.total (by rintro rfl; exact hne rfl) htier with hp | hp
      exacts [Or.inl hp, Or.inr hp]
  · rintro (v | v) h
    exacts [h₁.irrefl v h, h₂.irrefl v h]
  · rintro (u | u) (v | v) (w | w) huv hvw <;>
      first
        | exact h₁.trans huv hvw
        | exact h₂.trans huv hvw
        | exact (h₁.tier_eq huv).trans hvw
        | exact huv.trans (h₂.tier_eq hvw)
        | exact (huv : False).elim
        | exact (hvw : False).elim

/-- Concatenation preserves Axiom 3: the disjoint edge sum adds no cross
    edges. -/
theorem noInternalAssoc_concat (h₁ : NoInternalAssoc X.graph) (h₂ : NoInternalAssoc Y.graph) :
    NoInternalAssoc (concat t X Y).graph := by
  rintro (v | v) (w | w) hadj harc
  exacts [h₁ hadj harc, absurd hadj (by simp), absurd hadj (by simp), h₂ hadj harc]

/-- Concatenation preserves the No-Crossing Constraint ([jardine-2019]'s
    headline [jardine-heinz-2015] result): plain factor planarity suffices.
    Association edges are blockwise, so a straddle needs both edges in one block —
    reducing to the factor's `IsPlanar` — or one per block, where the required
    return arc runs `inr → inl` and does not exist. -/
theorem isPlanar_concat (h₁ : IsPlanar X.graph) (h₂ : IsPlanar Y.graph) :
    IsPlanar (concat t X Y).graph := by
  rintro (v | v) (v' | v') (w | w) (w' | w') hvv' hww' hvw hw'v' <;>
    first
      | exact h₁ hvv' hww' hvw hw'v'
      | exact h₂ hvv' hww' hvw hw'v'
      | exact (hvw : False).elim
      | exact (hw'v' : False).elim
      | simp_all

/-! #### Functoriality of concatenation -/

/-- Concatenation of morphisms is `Sum.map`: blockwise preservation from the
    factors; label preservation transports the bridge's tier equality. -/
def Hom.concatMap {X₁ Y₁ X₂ Y₂ : Graph S}
    (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) : Hom (concat t X₁ X₂) (concat t Y₁ Y₂) where
  toFun := Sum.map f.toFun g.toFun
  edge_map := by
    rintro (v | v) (w | w) h
    exacts [f.edge_map h, absurd h (by simp), absurd h (by simp), g.edge_map h]
  label_comp := by
    rintro (v | v)
    exacts [f.label_comp v, g.label_comp v]

/-- Concatenation of isomorphisms: full-structure isos compose blockwise, the
    bridge transported by label preservation. -/
def Iso.concatCongr {X₁ Y₁ X₂ Y₂ : Graph S} (e₁ : Iso X₁ Y₁) (e₂ : Iso X₂ Y₂) :
    Iso (concat t X₁ X₂) (concat t Y₁ Y₂) where
  toEquiv := e₁.toEquiv.sumCongr e₂.toEquiv
  edges_iff v w := by
    rcases v with v | v <;> rcases w with w | w
    exacts [e₁.edges_iff v w, Iff.rfl, Iff.rfl, e₂.edges_iff v w]
  arcs_iff v w := by
    rcases v with v | v <;> rcases w with w | w
    · exact e₁.arcs_iff v w
    · show Y₁.tier t (e₁.toEquiv v) = Y₂.tier t (e₂.toEquiv w) ↔ X₁.tier t v = X₂.tier t w
      rw [show Y₁.tier t (e₁.toEquiv v) = X₁.tier t v from congrArg t (e₁.label_comp v),
        show Y₂.tier t (e₂.toEquiv w) = X₂.tier t w from congrArg t (e₂.label_comp w)]
    · exact Iff.rfl
    · exact e₂.arcs_iff v w
  label_comp v := by
    rcases v with v | v
    exacts [e₁.label_comp v, e₂.label_comp v]

/-! #### Associativity up to isomorphism ([jardine-heinz-2015] Theorem 3) -/

/-- Concatenation is associative up to isomorphism, over `Equiv.sumAssoc`; the
    edge face is the stock `SimpleGraph.Iso.sumAssoc`, and every arc case holds
    definitionally in the order signature. -/
def concatAssocIso (X Y Z : Graph S) :
    Iso (concat t (concat t X Y) Z) (concat t X (concat t Y Z)) where
  toEquiv := Equiv.sumAssoc X.V Y.V Z.V
  edges_iff v w := SimpleGraph.Iso.sumAssoc.map_rel_iff
  arcs_iff v w := by
    rcases v with (a | b) | c <;> rcases w with (a' | b') | c' <;> exact Iff.rfl
  label_comp v := by
    rcases v with (a | b) | c <;> rfl

end Concat

/-! ### The bridge-free sum, and why the bridges exist

The plain blockwise sum carries no bridging arcs. It is the categorical
coproduct of the broad category (`Graph`), but it does **not** stay in
the axiom class: whenever both factors occupy a common tier, Axiom 2's totality
fails across the seam (`not_isTierOrdered_sum`) — `concat`'s bridges are the
minimal repair that keeps concatenation inside `AR`. -/

/-- The bridge-free blockwise sum. -/
def sum (X Y : Graph S) : Graph S where
  V := X.V ⊕ Y.V
  graph.edges := X.graph.edges ⊕g Y.graph.edges
  graph.arcs :=
    ⟨fun
      | .inl v, .inl w => X.graph.arcs.Adj v w
      | .inr v, .inr w => Y.graph.arcs.Adj v w
      | _, _ => False⟩
  label := Sum.elim X.label Y.label

@[simp] theorem sum_edges : (sum X Y).graph.edges = X.graph.edges ⊕g Y.graph.edges := rfl

@[simp] theorem sum_label_inl (v : X.V) : (sum X Y).label (.inl v) = X.label v := rfl

@[simp] theorem sum_label_inr (v : Y.V) : (sum X Y).label (.inr v) = Y.label v := rfl

@[simp] theorem sum_arcs_inl_inl {v w : X.V} :
    (sum X Y).graph.arcs.Adj (.inl v) (.inl w) ↔ X.graph.arcs.Adj v w := Iff.rfl

@[simp] theorem sum_arcs_inr_inr {v w : Y.V} :
    (sum X Y).graph.arcs.Adj (.inr v) (.inr w) ↔ Y.graph.arcs.Adj v w := Iff.rfl

@[simp] theorem not_sum_arcs_inl_inr {v : X.V} {w : Y.V} :
    ¬ (sum X Y).graph.arcs.Adj (.inl v) (.inr w) := fun h => h

@[simp] theorem not_sum_arcs_inr_inl {v : Y.V} {w : X.V} :
    ¬ (sum X Y).graph.arcs.Adj (.inr v) (.inl w) := fun h => h

/-- Copairing out of the bridge-free sum. -/
def sumDesc (f : Hom X Z) (g : Hom Y Z) : Hom (sum X Y) Z where
  toFun := Sum.elim f.toFun g.toFun
  edge_map := by
    rintro (v | v) (w | w) h
    exacts [f.edge_map h, absurd h (by simp), absurd h (by simp), g.edge_map h]
  label_comp := by
    rintro (v | v)
    exacts [f.label_comp v, g.label_comp v]

/-- **Axiom 2 forces the bridges**: the bridge-free sum of two graphs occupying a
    common tier is never tier-ordered — same-tier vertices from the two factors
    are precedence-unrelated across the seam. -/
theorem not_isTierOrdered_sum (t : S → ι) (v : X.V) (w : Y.V)
    (htier : X.tier t v = Y.tier t w) :
    ¬ IsTierOrdered (sum X Y).graph ((sum X Y).tier t) := fun h => by
  simpa using h.total (v := .inl v) (w := .inr w) Sum.inl_ne_inr htier

/-! ### Category structure, initial object, and coproducts -/

open CategoryTheory Limits

instance : Category (Graph S) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := f.comp g
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

instance (Y : Graph S) : Subsingleton (empty S ⟶ Y) :=
  ⟨fun _ _ => Hom.ext (funext fun v => v.elim)⟩

instance (Y : Graph S) : Nonempty (empty S ⟶ Y) :=
  ⟨⟨PEmpty.elim, fun v => v.elim, fun v => v.elim⟩⟩

instance : HasInitial (Graph S) := hasInitial_of_unique (empty S)

/-- Left coprojection. -/
def inl (X Y : Graph S) : X ⟶ sum X Y :=
  ⟨Sum.inl, fun _ _ h => h, fun _ => rfl⟩

/-- Right coprojection. -/
def inr (X Y : Graph S) : Y ⟶ sum X Y :=
  ⟨Sum.inr, fun _ _ h => h, fun _ => rfl⟩

/-- The bridge-free sum is the categorical coproduct of the broad category
    (contrast `not_isTierOrdered_sum`: it leaves the axiom class, which is why
    `AR`'s tensor is the bridged `concat` instead). -/
instance (X Y : Graph S) : HasBinaryCoproduct X Y :=
  HasColimit.mk
    { cocone := BinaryCofan.mk (inl X Y) (inr X Y)
      isColimit := BinaryCofan.IsColimit.mk _ (fun f g => sumDesc f g)
        (fun f g => Hom.ext rfl)
        (fun f g => Hom.ext rfl)
        (fun f g m h₁ h₂ => Hom.ext (funext fun v => by
          rcases v with v | v
          · exact congrArg (fun φ => Hom.toFun φ v) h₁
          · exact congrArg (fun φ => Hom.toFun φ v) h₂)) }

instance : HasBinaryCoproducts (Graph S) := hasBinaryCoproducts_of_hasColimit_pair _

end Graph

open CategoryTheory

/-- Precedence preservation as a morphism property: the maps that also preserve
    arcs — the model-theoretic full-structure homomorphisms, the foundation
    counterpart of the legacy `PrecAR` wide subcategory. -/
def Graph.precPreserving : MorphismProperty (Graph S) := fun X Y f =>
  ∀ ⦃v w⦄, X.graph.arcs.Adj v w → Y.graph.arcs.Adj (f.toFun v) (f.toFun w)

instance : (Graph.precPreserving (S := S)).IsMultiplicative where
  id_mem _ := fun _ _ h => h
  comp_mem _ _ hf hg := fun _ _ h => hg (hf h)

/-- A full isomorphism's underlying morphism preserves precedence. -/
theorem Graph.Iso.toHom_precPreserving {X Y : Graph S}
    (e : Graph.Iso X Y) : Graph.precPreserving e.toHom :=
  fun _ _ h => (e.arcs_iff _ _).mpr h

/-- Concatenation of precedence-preserving morphisms preserves precedence:
    blockwise from the factors, the bridge transported by labels. -/
theorem Graph.Hom.concatMap_precPreserving (t : S → ι)
    {X₁ Y₁ X₂ Y₂ : Graph S}
    {f : Graph.Hom X₁ Y₁} {g : Graph.Hom X₂ Y₂}
    (hf : Graph.precPreserving f) (hg : Graph.precPreserving g) :
    Graph.precPreserving (f.concatMap t g) := by
  rintro (v | v) (w | w) h
  · exact hf h
  · show Y₁.tier t (f.toFun v) = Y₂.tier t (g.toFun w)
    rw [show Y₁.tier t (f.toFun v) = X₁.tier t v from congrArg t (f.label_comp v),
      show Y₂.tier t (g.toFun w) = X₂.tier t w from congrArg t (g.label_comp w)]
    exact h
  · exact h.elim
  · exact hg h

/-! ### The category of autosegmental representations -/

variable (t : S → ι)

/-- The structural axiom class ([jardine-2016-diss] §4.2, Axioms 1–3) as an
    object property of the graph category. -/
def isRepresentation : ObjectProperty (Graph S) := fun X =>
  IsTierOrdered X.graph (X.tier t) ∧ NoInternalAssoc X.graph

/-- The category of **autosegmental representations** over a tier assignment:
    the full subcategory of labeled mixed graphs satisfying the structural
    axioms — the formal literature's ARs ([jardine-2019],
    [chandlee-jardine-2019]). -/
abbrev AR := (isRepresentation t).FullSubcategory

/-! ### The monoidal structure: morpheme concatenation -/

namespace AR

open MonoidalCategory

variable {t}

/-- Under the structural axioms the tier map properly colors the association
    graph: same-tier vertices are precedence-related (Axioms 1–2) and associated
    vertices never are (Axiom 3), so associated vertices lie on distinct tiers.
    Goldsmith's bipartite two-tier geometry is the two-colorable case. -/
def tierColoring (X : AR t) : X.obj.graph.edges.Coloring ι :=
  SimpleGraph.Coloring.mk (X.obj.tier t) fun {_ _} hadj htier =>
    (X.property.1.total hadj.ne htier).elim (X.property.2 hadj) (X.property.2 hadj.symm)

/-- A representation's association graph is colorable by its tiers: tier arity
    bounds the chromatic number of the association pattern. -/
theorem edges_colorable [Fintype ι] (X : AR t) :
    X.obj.graph.edges.Colorable (Fintype.card ι) :=
  (tierColoring X).colorable

/-- A graph isomorphism as an isomorphism of representations. -/
def mkIso {X Y : AR t} (e : Graph.Iso X.obj Y.obj) : X ≅ Y :=
  InducedCategory.isoMk
    ⟨e.toHom, e.symm.toHom,
      Graph.Hom.ext (funext fun v => e.toEquiv.symm_apply_apply v),
      Graph.Hom.ext (funext fun v => e.toEquiv.apply_symm_apply v)⟩

/-- Componentwise extensionality for representation morphisms. -/
theorem hom_ext {X Y : AR t} {f g : X ⟶ Y}
    (h : ∀ v, f.hom.toFun v = g.hom.toFun v) : f = g :=
  InducedCategory.hom_ext (Graph.Hom.ext (funext h))

universe u₁ u₂ u₃

/-- Monoidal structure: morpheme concatenation as tensor, the empty
    representation as unit; the axiom class is closed under both by
    `isTierOrdered_concat`/`noInternalAssoc_concat`. Universes pinned so the
    unit's vertex type shares the objects' universe — autobinding would split
    the instance head into an unusable `max`. -/
@[simps] instance instMonoidalStruct {S : Type u₁} {ι : Type u₂} {t : S → ι} :
    MonoidalCategoryStruct (AR.{u₁, u₂, u₃} t) where
  tensorObj X Y :=
    ⟨Graph.concat t X.obj Y.obj,
      Graph.isTierOrdered_concat t X.property.1 Y.property.1,
      Graph.noInternalAssoc_concat t X.property.2 Y.property.2⟩
  tensorUnit :=
    ⟨Graph.empty S, Graph.isTierOrdered_empty t,
      Graph.noInternalAssoc_empty⟩
  tensorHom f g := InducedCategory.homMk (Graph.Hom.concatMap t f.hom g.hom)
  whiskerLeft X _ _ f :=
    InducedCategory.homMk (Graph.Hom.concatMap t (Graph.Hom.id X.obj) f.hom)
  whiskerRight f Y :=
    InducedCategory.homMk (Graph.Hom.concatMap t f.hom (Graph.Hom.id Y.obj))
  associator X Y Z := mkIso (Graph.concatAssocIso t X.obj Y.obj Z.obj)
  leftUnitor X := mkIso (Graph.emptyConcatIso t X.obj)
  rightUnitor X := mkIso (Graph.concatEmptyIso t X.obj)

/-- The category of autosegmental representations is monoidal under morpheme
    concatenation — [jardine-heinz-2015] Theorems 1 and 3 packaged as coherence,
    with every proof a componentwise `rfl` over the concrete sum maps. -/
instance : MonoidalCategory (AR t) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => hom_ext (congrFun Sum.map_id_id))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => hom_ext (congrFun (Sum.map_comp_map _ _ _ _)))
    (associator_naturality := fun _ _ _ => hom_ext fun v => by
      repeat' rcases (v : _ ⊕ _) with v | v
      all_goals rfl)
    (leftUnitor_naturality := fun _ => hom_ext fun v => by
      rcases (v : _ ⊕ _) with v | v <;> first | rfl | exact v.elim)
    (rightUnitor_naturality := fun _ => hom_ext fun v => by
      rcases (v : _ ⊕ _) with v | v <;> first | rfl | exact v.elim)
    (pentagon := fun _ _ _ _ => hom_ext fun v => by
      repeat' rcases (v : _ ⊕ _) with v | v
      all_goals rfl)
    (triangle := fun _ _ => hom_ext fun v => by
      repeat' rcases (v : _ ⊕ _) with v | v
      all_goals first | rfl | exact v.elim)

/-- Precedence preservation on representations: the classical morphisms of the
    theory, as a monoidally-stable wide subcategory of the broad category. -/
def precPreserving : MorphismProperty (AR t) :=
  fun _ _ f => Graph.precPreserving f.hom

instance : (precPreserving (t := t)).IsMonoidalStable where
  id_mem _ := fun _ _ h => h
  comp_mem _ _ hf hg := fun _ _ h => hg (hf h)
  whiskerLeft _ _ _ _ hg :=
    Graph.Hom.concatMap_precPreserving t (fun _ _ h => h) hg
  whiskerRight _ hf _ :=
    Graph.Hom.concatMap_precPreserving t hf (fun _ _ h => h)
  associator_hom_mem A B C :=
    (Graph.concatAssocIso t A.obj B.obj C.obj).toHom_precPreserving
  associator_inv_mem A B C :=
    (Graph.concatAssocIso t A.obj B.obj C.obj).symm.toHom_precPreserving
  leftUnitor_hom_mem A := (Graph.emptyConcatIso t A.obj).toHom_precPreserving
  leftUnitor_inv_mem A := (Graph.emptyConcatIso t A.obj).symm.toHom_precPreserving
  rightUnitor_hom_mem A := (Graph.concatEmptyIso t A.obj).toHom_precPreserving
  rightUnitor_inv_mem A := (Graph.concatEmptyIso t A.obj).symm.toHom_precPreserving

end AR

end Autosegmental
