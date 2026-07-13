/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Labeled mixed graphs

A labeled mixed graph `⟨V, E, A, ℓ⟩` has labeled vertices, undirected
association edges, and directed order arcs — the autosegmental representation
of [jardine-2019], with no further structure. `Graph S` carries the quadruple
as fields: a vertex type, a `SimpleGraph` of association edges, a `Digraph` of
order arcs, and a labeling `ℓ : V → S`. Tiers are
not part of the object: a tier assignment `t : S → ι` on the labels induces a
vertex coloring `X.tier t`, and the §4.2 well-formedness axioms (`AR.lean`)
carve the representations out of the raw graphs relative to it.

## Main definitions

* `Graph S`: the labeled mixed graph ([jardine-2019]'s `GR(Γ)`) and the
  category thereof, with `HasInitial` and `HasBinaryCoproducts`;
  `Graph.Hom` are label- and association-preserving maps, `precPreserving`
  marks the full-structure homomorphisms, `Graph.Iso` the full-structure
  equivalences.
* `Graph.concat t`: concatenation — the vertex sum with a same-tier
  bridge, [jardine-heinz-2015] Definition 2 in the order signature, minus its
  `R_ID` merge (`OCP.collapse`); `Graph.sum` is the bridge-free coproduct.

## Main results

* `concatEmptyIso`, `emptyConcatIso`, `concatAssocIso`:
  [jardine-heinz-2015] Theorems 1 and 3 up to `Iso`, unconditional in the
  order signature.

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
-/

namespace Autosegmental

variable {S ι : Type*}

/-! ### The category of labeled mixed graphs -/

/-- An object of the category of labeled mixed graphs over `S` — the
    literature's labeled mixed graph `⟨V, E, A, ℓ⟩` / [jardine-2019]'s `GR(Γ)`,
    carried fieldwise. -/
structure Graph (S : Type*) where
  /-- The vertex type. -/
  V : Type*
  /-- The undirected association edges (`E`). -/
  edges : SimpleGraph V
  /-- The directed order arcs (`A`). -/
  arcs : Digraph V
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
  edge_map : ∀ ⦃v w⦄, X.edges.Adj v w → Y.edges.Adj (toFun v) (toFun w)
  /-- Labels are preserved. -/
  label_comp : ∀ v, Y.label (toFun v) = X.label v

/-- The edge face of a morphism, a stock graph homomorphism. -/
def Hom.edgesHom (f : Hom X Y) : X.edges →g Y.edges :=
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
  edges_iff : ∀ v w, Y.edges.Adj (toEquiv v) (toEquiv w) ↔ X.edges.Adj v w
  /-- Order arcs correspond. -/
  arcs_iff : ∀ v w, Y.arcs.Adj (toEquiv v) (toEquiv w) ↔ X.arcs.Adj v w
  /-- Labels are preserved. -/
  label_comp : ∀ v, Y.label (toEquiv v) = X.label v

/-- The edge face of an isomorphism, as a stock `SimpleGraph.Iso`. -/
def Iso.edgesIso (e : Iso X Y) : X.edges ≃g Y.edges :=
  ⟨e.toEquiv, e.edges_iff _ _⟩

/-- The arc face of an isomorphism, as a stock `RelIso`. -/
def Iso.arcsIso (e : Iso X Y) : X.arcs.Adj ≃r Y.arcs.Adj :=
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
def empty (S : Type*) : Graph S := ⟨PEmpty, ⊥, ⊥, PEmpty.elim⟩

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
  edges := X.edges ⊕g Y.edges
  arcs :=
    ⟨fun
      | .inl v, .inl w => X.arcs.Adj v w
      | .inr v, .inr w => Y.arcs.Adj v w
      | .inl v, .inr w => X.tier t v = Y.tier t w
      | .inr _, .inl _ => False⟩
  label := Sum.elim X.label Y.label

@[simp] theorem concat_label_inl (v : X.V) : (concat t X Y).label (.inl v) = X.label v := rfl

@[simp] theorem concat_label_inr (v : Y.V) : (concat t X Y).label (.inr v) = Y.label v := rfl

@[simp] theorem concat_edges :
    (concat t X Y).edges = X.edges ⊕g Y.edges := rfl

@[simp] theorem concat_arcs_inl_inl {v w : X.V} :
    (concat t X Y).arcs.Adj (.inl v) (.inl w) ↔ X.arcs.Adj v w := Iff.rfl

@[simp] theorem concat_arcs_inr_inr {v w : Y.V} :
    (concat t X Y).arcs.Adj (.inr v) (.inr w) ↔ Y.arcs.Adj v w := Iff.rfl

@[simp] theorem concat_arcs_inl_inr {v : X.V} {w : Y.V} :
    (concat t X Y).arcs.Adj (.inl v) (.inr w) ↔ X.tier t v = Y.tier t w := Iff.rfl

@[simp] theorem not_concat_arcs_inr_inl {v : Y.V} {w : X.V} :
    ¬ (concat t X Y).arcs.Adj (.inr v) (.inl w) := fun h => h

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

/-! ### The bridge-free sum

The plain blockwise sum carries no bridging arcs: the categorical coproduct of
the broad category. Why `concat` bridges instead — Axiom 2's totality fails
across the seam — is `not_isTierOrdered_sum` (`AR.lean`). -/

/-- The bridge-free blockwise sum. -/
def sum (X Y : Graph S) : Graph S where
  V := X.V ⊕ Y.V
  edges := X.edges ⊕g Y.edges
  arcs :=
    ⟨fun
      | .inl v, .inl w => X.arcs.Adj v w
      | .inr v, .inr w => Y.arcs.Adj v w
      | _, _ => False⟩
  label := Sum.elim X.label Y.label

@[simp] theorem sum_edges : (sum X Y).edges = X.edges ⊕g Y.edges := rfl

@[simp] theorem sum_label_inl (v : X.V) : (sum X Y).label (.inl v) = X.label v := rfl

@[simp] theorem sum_label_inr (v : Y.V) : (sum X Y).label (.inr v) = Y.label v := rfl

@[simp] theorem sum_arcs_inl_inl {v w : X.V} :
    (sum X Y).arcs.Adj (.inl v) (.inl w) ↔ X.arcs.Adj v w := Iff.rfl

@[simp] theorem sum_arcs_inr_inr {v w : Y.V} :
    (sum X Y).arcs.Adj (.inr v) (.inr w) ↔ Y.arcs.Adj v w := Iff.rfl

@[simp] theorem not_sum_arcs_inl_inr {v : X.V} {w : Y.V} :
    ¬ (sum X Y).arcs.Adj (.inl v) (.inr w) := fun h => h

@[simp] theorem not_sum_arcs_inr_inl {v : Y.V} {w : X.V} :
    ¬ (sum X Y).arcs.Adj (.inr v) (.inl w) := fun h => h

/-- Copairing out of the bridge-free sum. -/
def sumDesc (f : Hom X Z) (g : Hom Y Z) : Hom (sum X Y) Z where
  toFun := Sum.elim f.toFun g.toFun
  edge_map := by
    rintro (v | v) (w | w) h
    exacts [f.edge_map h, absurd h (by simp), absurd h (by simp), g.edge_map h]
  label_comp := by
    rintro (v | v)
    exacts [f.label_comp v, g.label_comp v]

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

/-- The property of morphisms that also preserve the order arcs; such maps are the
    model-theoretic full-structure homomorphisms. -/
def precPreserving : MorphismProperty (Graph S) := fun X Y f =>
  ∀ ⦃v w⦄, X.arcs.Adj v w → Y.arcs.Adj (f.toFun v) (f.toFun w)

instance : (precPreserving (S := S)).IsMultiplicative where
  id_mem _ := fun _ _ h => h
  comp_mem _ _ hf hg := fun _ _ h => hg (hf h)

/-- A full isomorphism's underlying morphism preserves precedence. -/
theorem Iso.toHom_precPreserving {X Y : Graph S} (e : Iso X Y) : precPreserving e.toHom :=
  fun _ _ h => (e.arcs_iff _ _).mpr h

/-- The concatenation of precedence-preserving morphisms preserves precedence. -/
theorem Hom.concatMap_precPreserving (t : S → ι) {X₁ Y₁ X₂ Y₂ : Graph S}
    {f : Hom X₁ Y₁} {g : Hom X₂ Y₂} (hf : precPreserving f) (hg : precPreserving g) :
    precPreserving (f.concatMap t g) := by
  rintro (v | v) (w | w) h
  exacts [hf h,
    (congrArg t (f.label_comp v)).trans ((h : _ = _).trans (congrArg t (g.label_comp w)).symm),
    h.elim, hg h]

end Graph

end Autosegmental
