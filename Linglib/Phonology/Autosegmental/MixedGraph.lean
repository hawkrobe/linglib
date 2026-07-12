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
of [jardine-2019], with no further structure. The graph is a `MixedGraph` (Core)
and the labeling a map `ℓ : V → S`; `MixedGraphCat S` bundles the two. Tiers are
not part of the object: a tier assignment `t : S → ι` on the labels induces a
vertex coloring `X.tier t`, and well-formedness axioms carve the representations
out of the raw graphs relative to it.

## Main definitions

* `IsTierOrdered`, `NoInternalAssoc`, `IsSaturated`, `IsPlanar`, `IsOCPClean`:
  the §4.2 axioms (1–2, 3, 4, 5, 6; [jardine-heinz-2015] numbers the NCC and OCP
  as 4 and 5 and has no saturation axiom) as predicates on a `MixedGraph` and, for
  tier-relative axioms, a vertex coloring `c : V → ι`. Saturation is stated but
  not imposed, as in `AR.lean`; tier-orderedness includes path-closure
  (`MixedGraph.PrecPath`), [jardine-2019]'s reading that `A` represents the order.
* `MixedGraphCat S`: the labeled mixed graph ([jardine-2019]'s `GR(Γ)`) and the
  category thereof, with `HasInitial` and `HasBinaryCoproducts`;
  `MixedGraphCat.Hom` are label- and association-preserving maps, `precPreserving`
  marks the full-structure homomorphisms, `MixedGraphCat.Iso` the full-structure
  equivalences.
* `MixedGraphCat.concat t`: concatenation — the vertex sum with a same-tier
  bridge, [jardine-heinz-2015] Definition 2 in the order signature, minus its
  `R_ID` merge (`OCP.collapse`); `MixedGraphCat.sum` is the bridge-free coproduct.
* `Representation t`: the category of autosegmental representations — the full
  subcategory of labeled mixed graphs on Axioms 1–3, monoidal under `concat`.

## Main results

* `concat_empty_iso`, `empty_concat_iso`, `concat_assoc_iso`,
  `isTierOrdered_concat`, `noInternalAssoc_concat`, `isPlanar_concat`:
  [jardine-heinz-2015] Theorems 1, 3 and 4 up to `Iso`, unconditional in the
  order signature; `isPlanar_concat` is [jardine-2019]'s NCC-preservation.
* `not_isTierOrdered_sum`: the bridge-free coproduct leaves the axiom class
  whenever the factors share a tier — Axiom 2 forces `concat`'s bridges.
* `Representation.tierColoring`: the tier map properly colors the association
  graph, so tier arity bounds its chromatic number (`edges_colorable`).

## TODO

* The normal-form equivalence with the strict tuple presentation, with
  `IsPlanar` reducing to the per-pair NCC on normal forms.
-/

namespace Autosegmental

variable {V S ι : Type*}

/-! ### The §4.2 axioms -/

section Axioms
variable (G : MixedGraph V)

/-- Axioms 1–2 ([jardine-2016-diss] §4.2). Axiom 2's tier partition enters as
    the coloring `c` — data, not a proposition — and what remains propositional
    is Axiom 1 relative to it: the arcs are tier-internal and strictly totally
    order each fiber. This is [jardine-2019]'s reading that `A` represents *the
    order* on each string; the arcs coincide with their path closure
    (`IsTierOrdered.precPath_eq`), so no closure operator appears in the
    axioms. -/
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
    not imposed — floating elements are well-formed, as in `AR.lean`. -/
def IsSaturated : Prop := ∀ v, ∃ w, G.edges.Adj v w

/-- Axiom 5, the No-Crossing Constraint in [jardine-2016-diss]'s general path
    form: no two association edges whose endpoints straddle in opposite precedence
    order. -/
def IsPlanar : Prop :=
  ∀ ⦃v v' w w'⦄, G.edges.Adj v v' → G.edges.Adj w w' → G.arcs.Adj v w → ¬ G.arcs.Adj w' v'

/-- Axiom 6, the OCP on melody tier `m`: precedence-adjacent vertices on `m` bear
    distinct labels. Needs the labeling `ℓ` and its tier assignment `t`. -/
def IsOCPClean (ℓ : V → S) (t : S → ι) (m : ι) : Prop :=
  ∀ ⦃v w⦄, G.arcs.Adj v w → t (ℓ v) = m → ℓ v ≠ ℓ w

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
structure MixedGraphCat (S : Type*) where
  /-- The vertex type. -/
  V : Type*
  /-- The mixed graph: undirected association edges and directed order arcs. -/
  graph : MixedGraph V
  /-- The labeling (`ℓ`). -/
  label : V → S

namespace MixedGraphCat

variable {X Y Z : MixedGraphCat S}

/-- The tier of a vertex under a tier assignment on the alphabet. -/
def tier (t : S → ι) (X : MixedGraphCat S) : X.V → ι := t ∘ X.label

/-! ### Morphisms -/

/-- A label- and association-preserving map of labeled mixed graphs. Precedence
    is deliberately *not* required — reassociation analyses move material across
    the order — so this is the broad morphism class where the coproduct and the
    OCP repair live; the precedence-preserving maps form the wide morphism class
    `precPreserving` (the legacy `AR.Hom` vs `PrecAR` split, at the foundation). -/
@[ext]
structure Hom (X Y : MixedGraphCat S) where
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
def Hom.id (X : MixedGraphCat S) : Hom X X :=
  ⟨_root_.id, fun _ _ h => h, fun _ => rfl⟩

/-- Composition of morphisms. -/
def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, fun _ _ h => g.edge_map (f.edge_map h),
    fun v => (g.label_comp _).trans (f.label_comp v)⟩

/-! ### Isomorphism -/

/-- A label- and relation-preserving equivalence of labeled mixed graphs. -/
structure Iso (X Y : MixedGraphCat S) extends X.V ≃ Y.V where
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
def Iso.refl (X : MixedGraphCat S) : Iso X X :=
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
def empty (S : Type*) : MixedGraphCat S := ⟨PEmpty, ⟨⊥, ⊥⟩, PEmpty.elim⟩

theorem empty_isTierOrdered (t : S → ι) : IsTierOrdered (empty S).graph ((empty S).tier t) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun v => v.elim⟩

theorem empty_noInternalAssoc : NoInternalAssoc (empty S).graph := fun v => v.elim

/-! ### Tier-bridging concatenation

Per tier class, concatenation is the ordinal sum: blockwise arcs plus a bridging
arc from every `X`-vertex of a class to every same-class `Y`-vertex.
[jardine-2019] glosses `A` as representing *the order* on each string, but its
operative concatenation bridges a single pair per tier — `(last X Γᵢ, first Y Γᵢ)`,
with `first`/`last` partial — so its composites carry generator-style arcs. This
axiom class instead takes the order-*closed* representative of that same
precedence relation (interconvertible with the generator form via Hasse diagram ↔
transitive closure on the finite per-tier strict orders); the complete same-class
bridge is chosen because it is total and functorial where `first`/`last` are
partial and not hom-preserved, and its monoid laws unconditional where the
successor form's associativity is conditional on the tier classes being string
graphs (the paper's Lemma 1 remark). On the definability relationship between the
two signatures cf. [jardine-2017-complexity]; subgraph-based notions such as
`ASL.lean`'s forbidden-factor grammars are signature-sensitive and do not transfer
for free. -/

section Concat
variable (t : S → ι)

/-- Concatenation ([jardine-heinz-2015] Definition 2, minus the `R_ID` melody
    merge, in the precedence signature): stock disjoint sum on edges; on arcs the
    per-tier ordinal sum — blockwise arcs plus a bridge from each `X`-vertex to
    each same-tier `Y`-vertex. -/
def concat (X Y : MixedGraphCat S) : MixedGraphCat S where
  V := X.V ⊕ Y.V
  graph :=
    { edges := X.graph.edges ⊕g Y.graph.edges
      arcs :=
        ⟨fun v w =>
          match v, w with
          | .inl v, .inl w => X.graph.arcs.Adj v w
          | .inr v, .inr w => Y.graph.arcs.Adj v w
          | .inl v, .inr w => X.tier t v = Y.tier t w
          | .inr _, .inl _ => False⟩ }
  label := Sum.elim X.label Y.label

@[simp] theorem concat_label_inl (v : X.V) : (concat t X Y).label (.inl v) = X.label v := rfl

@[simp] theorem concat_label_inr (v : Y.V) : (concat t X Y).label (.inr v) = Y.label v := rfl

@[simp] theorem concat_edges :
    (concat t X Y).graph.edges = X.graph.edges ⊕g Y.graph.edges := rfl

@[simp] theorem concat_arcs_inl_inl {v w : X.V} :
    (concat t X Y).graph.arcs.Adj (.inl v) (.inl w) ↔ X.graph.arcs.Adj v w := Iff.rfl

@[simp] theorem concat_arcs_inr_inr {v w : Y.V} :
    (concat t X Y).graph.arcs.Adj (.inr v) (.inr w) ↔ Y.graph.arcs.Adj v w := Iff.rfl

/-! ### Unit laws ([jardine-heinz-2015] Theorem 1) -/

/-- Concatenation with the empty graph on the right, up to isomorphism. -/
def concat_empty_iso (X : MixedGraphCat S) : Iso (concat t X (empty S)) X where
  toEquiv := Equiv.sumEmpty X.V PEmpty
  edges_iff v w := by
    rcases v with v | v
    · rcases w with w | w
      · exact Iff.rfl
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
def empty_concat_iso (X : MixedGraphCat S) : Iso (concat t (empty S) X) X where
  toEquiv := Equiv.emptySum PEmpty X.V
  edges_iff v w := by
    rcases v with v | v
    · exact v.elim
    · rcases w with w | w
      · exact w.elim
      · exact Iff.rfl
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
  · rintro (u | u) (v | v) (w | w) huv hvw
    · exact h₁.trans huv hvw
    · exact (h₁.tier_eq huv).trans hvw
    · exact (hvw : False).elim
    · exact huv.trans (h₂.tier_eq hvw)
    · exact (huv : False).elim
    · exact (huv : False).elim
    · exact (hvw : False).elim
    · exact h₂.trans huv hvw

/-- Concatenation preserves Axiom 3: the disjoint edge sum adds no cross
    edges. -/
theorem noInternalAssoc_concat (h₁ : NoInternalAssoc X.graph) (h₂ : NoInternalAssoc Y.graph) :
    NoInternalAssoc (concat t X Y).graph := by
  rintro (v | v) (w | w) hadj harc
  · exact h₁ hadj harc
  · exact absurd hadj (by simp)
  · exact absurd hadj (by simp)
  · exact h₂ hadj harc

/-- Concatenation preserves the No-Crossing Constraint ([jardine-2019]'s
    headline [jardine-heinz-2015] result): plain factor planarity suffices.
    Association edges are blockwise, so a straddle needs both edges in one block —
    reducing to the factor's `IsPlanar` — or one per block, where the required
    return arc runs `inr → inl` and does not exist. -/
theorem isPlanar_concat (h₁ : IsPlanar X.graph) (h₂ : IsPlanar Y.graph) :
    IsPlanar (concat t X Y).graph := by
  rintro (v | v) (v' | v') (w | w) (w' | w') hvv' hww' hvw hw'v'
  · exact h₁ hvv' hww' hvw hw'v'
  · exact absurd hww' (by simp)
  · exact absurd hww' (by simp)
  · exact (hw'v' : False).elim
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact absurd hvv' (by simp)
  · exact (hvw : False).elim
  · exact absurd hww' (by simp)
  · exact absurd hww' (by simp)
  · exact h₂ hvv' hww' hvw hw'v'

/-! #### Functoriality of concatenation -/

/-- Concatenation of morphisms is `Sum.map`: blockwise preservation from the
    factors, and label preservation transports the bridge's tier equality. Domain and codomain
    of each factor may have independent vertex types, as morphisms in `MixedGraphCat S` do. -/
def Hom.sumMap {X₁ Y₁ X₂ Y₂ : MixedGraphCat S}
    (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) : Hom (concat t X₁ X₂) (concat t Y₁ Y₂) where
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
def concat_assoc_iso (X Y Z : MixedGraphCat S) :
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
coproduct of the broad category (`MixedGraphCat`), but it does **not** stay in
the axiom class: whenever both factors occupy a common tier, Axiom 2's totality
fails across the seam (`not_isTierOrdered_sum`) — `concat`'s bridges are the
minimal repair that keeps concatenation inside `Representation`. -/

/-- The bridge-free blockwise sum. -/
def sum (X Y : MixedGraphCat S) : MixedGraphCat S where
  V := X.V ⊕ Y.V
  graph :=
    { edges := X.graph.edges ⊕g Y.graph.edges
      arcs :=
        ⟨fun v w =>
          match v, w with
          | .inl v, .inl w => X.graph.arcs.Adj v w
          | .inr v, .inr w => Y.graph.arcs.Adj v w
          | _, _ => False⟩ }
  label := Sum.elim X.label Y.label

@[simp] theorem sum_edges : (sum X Y).graph.edges = X.graph.edges ⊕g Y.graph.edges := rfl

/-- Copairing out of the bridge-free sum. -/
def sumDesc (f : Hom X Z) (g : Hom Y Z) : Hom (sum X Y) Z where
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
theorem not_isTierOrdered_sum (t : S → ι) (v : X.V) (w : Y.V)
    (htier : X.tier t v = Y.tier t w) :
    ¬ IsTierOrdered (sum X Y).graph ((sum X Y).tier t) := fun h =>
  (h.total (v := .inl v) (w := .inr w) (by simp) htier).elim (fun hp => hp) fun hp => hp

/-! ### The category of labeled mixed graphs -/

open CategoryTheory Limits

instance : Category (MixedGraphCat S) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := f.comp g
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

instance (Y : MixedGraphCat S) : Subsingleton (empty S ⟶ Y) :=
  ⟨fun _ _ => Hom.ext (funext fun v => v.elim)⟩

instance (Y : MixedGraphCat S) : Nonempty (empty S ⟶ Y) :=
  ⟨⟨PEmpty.elim, fun v => v.elim, fun v => v.elim⟩⟩

instance : HasInitial (MixedGraphCat S) := hasInitial_of_unique (empty S)

/-- Left coprojection. -/
def inl (X Y : MixedGraphCat S) : X ⟶ sum X Y :=
  ⟨Sum.inl, fun _ _ h => h, fun _ => rfl⟩

/-- Right coprojection. -/
def inr (X Y : MixedGraphCat S) : Y ⟶ sum X Y :=
  ⟨Sum.inr, fun _ _ h => h, fun _ => rfl⟩

/-- Copairing out of the bridge-free sum. -/
def desc (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
  sumDesc f g

/-- The bridge-free sum is the categorical coproduct of the broad category
    (contrast `not_isTierOrdered_sum`: it leaves the axiom class, which is why
    `Representation`'s tensor is the bridged `concat` instead). -/
instance (X Y : MixedGraphCat S) : HasBinaryCoproduct X Y :=
  HasColimit.mk
    { cocone := BinaryCofan.mk (inl X Y) (inr X Y)
      isColimit := BinaryCofan.IsColimit.mk _ (fun f g => desc f g)
        (fun f g => Hom.ext rfl)
        (fun f g => Hom.ext rfl)
        (fun f g m h₁ h₂ => Hom.ext (funext fun v => by
          rcases v with v | v
          · exact congrArg (fun φ => Hom.toFun φ v) h₁
          · exact congrArg (fun φ => Hom.toFun φ v) h₂)) }

instance : HasBinaryCoproducts (MixedGraphCat S) := hasBinaryCoproducts_of_hasColimit_pair _

end MixedGraphCat

open CategoryTheory

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
  IsTierOrdered X.graph (X.tier t) ∧ NoInternalAssoc X.graph

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
  ⟨MixedGraphCat.empty S, MixedGraphCat.empty_isTierOrdered t,
    MixedGraphCat.empty_noInternalAssoc⟩

/-- The tensor: morpheme concatenation, staying in the axiom class by
    `isTierOrdered_concat`/`noInternalAssoc_concat`. -/
def tensor (X Y : Representation t) : Representation t :=
  ⟨MixedGraphCat.concat t X.obj Y.obj,
    MixedGraphCat.isTierOrdered_concat t X.property.1 Y.property.1,
    MixedGraphCat.noInternalAssoc_concat t X.property.2 Y.property.2⟩

/-- Under the structural axioms the tier map properly colors the association
    graph: same-tier vertices are precedence-related (Axioms 1–2) and associated
    vertices never are (Axiom 3), so associated vertices lie on distinct tiers.
    Goldsmith's bipartite two-tier geometry is the two-colorable case. -/
def tierColoring (X : Representation t) : X.obj.graph.edges.Coloring ι :=
  SimpleGraph.Coloring.mk (X.obj.tier t) fun {_ _} hadj htier =>
    (X.property.1.total hadj.ne htier).elim (X.property.2 hadj) (X.property.2 hadj.symm)

/-- A representation's association graph is colorable by its tiers: tier arity
    bounds the chromatic number of the association pattern. -/
theorem edges_colorable [Fintype ι] (X : Representation t) :
    X.obj.graph.edges.Colorable (Fintype.card ι) :=
  (tierColoring X).colorable

/-- A graph isomorphism as an isomorphism of representations. -/
def mkIso {X Y : Representation t} (e : MixedGraphCat.Iso X.obj Y.obj) : X ≅ Y :=
  InducedCategory.isoMk
    ⟨e.toHom, e.symm.toHom,
      MixedGraphCat.Hom.ext (funext fun v => e.toEquiv.symm_apply_apply v),
      MixedGraphCat.Hom.ext (funext fun v => e.toEquiv.apply_symm_apply v)⟩

/-- The tensor on morphisms, as a representation morphism. -/
def tensorHomAux {X₁ Y₁ X₂ Y₂ : Representation t} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensor X₁ X₂ ⟶ tensor Y₁ Y₂ :=
  InducedCategory.homMk (MixedGraphCat.Hom.sumMap (X₁ := X₁.obj) (Y₁ := Y₁.obj)
    (X₂ := X₂.obj) (Y₂ := Y₂.obj) t f.hom g.hom)

/-- Left whiskering, as a representation morphism. -/
def whiskerLeftAux (X : Representation t) {Y₁ Y₂ : Representation t} (f : Y₁ ⟶ Y₂) :
    tensor X Y₁ ⟶ tensor X Y₂ :=
  InducedCategory.homMk (MixedGraphCat.Hom.sumMap (X₁ := X.obj) (Y₁ := X.obj)
    (X₂ := Y₁.obj) (Y₂ := Y₂.obj) t (MixedGraphCat.Hom.id X.obj) f.hom)

/-- Right whiskering, as a representation morphism. -/
def whiskerRightAux {X₁ X₂ : Representation t} (f : X₁ ⟶ X₂) (Y : Representation t) :
    tensor X₁ Y ⟶ tensor X₂ Y :=
  InducedCategory.homMk (MixedGraphCat.Hom.sumMap (X₁ := X₁.obj) (Y₁ := X₂.obj)
    (X₂ := Y.obj) (Y₂ := Y.obj) t f.hom (MixedGraphCat.Hom.id Y.obj))

@[simps] instance instMonoidalStruct : MonoidalCategoryStruct (Representation t) where
  tensorObj := tensor
  tensorUnit := unit
  tensorHom := tensorHomAux
  whiskerLeft := whiskerLeftAux
  whiskerRight := whiskerRightAux
  associator X Y Z := mkIso (MixedGraphCat.concat_assoc_iso t X.obj Y.obj Z.obj)
  leftUnitor X := mkIso (MixedGraphCat.empty_concat_iso t X.obj)
  rightUnitor X := mkIso (MixedGraphCat.concat_empty_iso t X.obj)

/-- The category of autosegmental representations is monoidal under morpheme
    concatenation — [jardine-heinz-2015] Theorems 1 and 3 packaged as coherence,
    with every proof a componentwise `rfl` over the concrete sum maps. -/
instance : MonoidalCategory (Representation t) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by rcases (v : _ ⊕ _) with v | v <;> rfl)))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by rcases (v : _ ⊕ _) with v | v <;> rfl)))
    (associator_naturality := fun _ _ _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rcases (v : _ ⊕ _) with v | v <;> rfl
        · rfl)))
    (leftUnitor_naturality := fun _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · exact v.elim
        · rfl)))
    (rightUnitor_naturality := fun _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rfl
        · exact v.elim)))
    (pentagon := fun _ _ _ _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rcases (v : _ ⊕ _) with v | v
          · rcases (v : _ ⊕ _) with v | v <;> rfl
          · rfl
        · rfl)))
    (triangle := fun _ _ => InducedCategory.hom_ext
      (MixedGraphCat.Hom.ext (funext fun v => by
        rcases (v : _ ⊕ _) with v | v
        · rcases (v : _ ⊕ _) with v | v
          · rfl
          · exact v.elim
        · rfl)))

end Representation

end Autosegmental
