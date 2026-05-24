/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Graph

/-!
# The autosegmental category `AR α β`

`AR α β` is the bundled type of **well-formed autosegmental
representations**: a `Graph α β` paired with proofs that the link
set is in-bounds and that the representation is planar (satisfies
@cite{goldsmith-1976}'s No-Crossing Constraint, equivalently
@cite{pulleyblank-1986}'s reformulated Well-Formedness Condition).

In mathlib's pattern (`Group` → `Grp`, `Module` → `ModuleCat`),
`Graph α β` is the underlying object type and `AR α β` is the
*bundled* type that carries the autosegmental well-formedness
invariants — the canonical objects of the category of autosegmental
representations. The bundled name `AR` matches the field's standard
abbreviation across @cite{jardine-2017},
@cite{chandlee-jardine-2019}, @cite{burness-mcmullin-2020} and the
broader Heinz-Jardine-Chandlee tradition.

## Main definitions (this file)

* `AR α β` — the bundled well-formed AR type (Graph + InBounds + Planar).
* `AR.empty`, `AR.concat` — lifted from Graph; concat preserves the
  invariants because @cite{jardine-heinz-2015} Theorem 4 + our
  `inBounds_concat` lemma carry both invariants through.
* `AR.Hom A B := Graph.Hom A.toGraph B.toGraph` — morphisms are
  just graph homomorphisms on the underlying graphs.
* `AR.Hom.id`, `AR.Hom.comp` — delegated to `Graph.Hom`.

## What this file does NOT yet define

Sibling files in the same directory will add:

* `AR.tensorHom` and functoriality (via `Graph.Hom.concatMap`) — the
  bifunctor on `Hom` corresponding to concatenation.
* `CategoryTheory.Category (AR α β)` — the formal category instance.
* `CategoryTheory.MonoidalCategory (AR α β)` — with `concat` as the
  tensor product, `empty` as the tensor unit, and the associator /
  unitors derived from the strict equalities `concat_assoc`,
  `empty_concat`, `concat_empty`.

These complete "the category of autosegmental representations" as a
formal mathlib monoidal category. They will land as separate commits.
-/

namespace Phonology.Autosegmental

/-! ### The bundled type `AR`

`AR α β` extends `Graph α β` with structural well-formedness
proofs. The Pulleyblank-1986 WFC is **planarity (NCC) alone**;
@cite{goldsmith-1979}'s saturation is language-particular and is
*not* carried as a structural invariant here. `InBounds` is a
substrate-level requirement (Graph doesn't enforce links to fall
within tier lengths structurally; the subtype does).
-/

/-- A well-formed autosegmental representation: a `Graph` whose link
    set is in-bounds (`InBounds`) and which satisfies the No-Crossing
    Constraint (`IsPlanar`). Per @cite{pulleyblank-1986}, planarity is
    the sole universal structural well-formedness condition on
    autosegmental representations; @cite{goldsmith-1979}'s additional
    saturation requirements are language-particular and live at the
    consumer level, not in this subtype. -/
@[ext]
structure AR (α β : Type*) extends Graph α β where
  inBounds : toGraph.InBounds
  planar : toGraph.IsPlanar

namespace AR

variable {α β : Type*}

/-! ### Construction -/

/-- The empty AR (no tier elements, no associations). Trivially
    in-bounds (no links to check) and planar. -/
def empty : AR α β where
  toGraph := Graph.empty
  inBounds := Graph.inBounds_empty
  planar := Graph.isPlanar_empty

/-- Concatenation of ARs (@cite{jardine-heinz-2015}): tiers are
    concatenated, link sets are unioned with B's shifted by A's tier
    lengths. The InBounds invariant is preserved by
    `Graph.inBounds_concat`; planarity is preserved by
    `Graph.isPlanar_concat` (using A's `InBounds`). -/
def concat (A B : AR α β) : AR α β where
  toGraph := A.toGraph.concat B.toGraph
  inBounds := Graph.inBounds_concat A.inBounds B.inBounds
  planar := Graph.isPlanar_concat _ _ A.inBounds A.planar B.planar

/-! ### Morphisms -/

/-- A morphism in the autosegmental category is just a graph
    homomorphism on the underlying graphs. The well-formedness
    invariants (`InBounds`, `Planar`) are properties of objects, not
    of morphisms — a graph homomorphism between well-formed ARs
    automatically lands inside a well-formed AR. -/
abbrev Hom (A B : AR α β) := Graph.Hom A.toGraph B.toGraph

namespace Hom

variable {A B C D : AR α β}

/-- Identity morphism on an AR. Delegated to `Graph.Hom.id`. -/
def id (A : AR α β) : Hom A A := Graph.Hom.id A.toGraph

/-- Composition (diagrammatic order: `f.comp g` is "f first, then g").
    Delegated to `Graph.Hom.comp`. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C := Graph.Hom.comp f g

/-! #### Category laws (inherited from Graph) -/

theorem id_comp (f : Hom A B) : (Hom.id A).comp f = f :=
  Graph.Hom.id_comp f

theorem comp_id (f : Hom A B) : f.comp (Hom.id B) = f :=
  Graph.Hom.comp_id f

theorem comp_assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Graph.Hom.comp_assoc f g h

end Hom

/-! ### Tensor on morphisms (the bifunctor underlying `MonoidalCategory`) -/

/-- The concatenation tensor on AR morphisms. Lifts
    `Graph.Hom.concatMap` using the `inBounds` proof carried by the
    AR object — so the `InBounds` hypothesis the underlying
    `Graph.Hom.concatMap` requires is automatically supplied. This is
    the bifunctor `(⊗) : Hom A A' → Hom B B' → Hom (A ⊗ B) (A' ⊗ B')`
    of `MonoidalCategory (AR α β)`. -/
def tensorHom {A A' B B' : AR α β}
    (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') :=
  Graph.Hom.concatMap A.inBounds f g

/-! #### Functoriality of `tensorHom` -/

/-- `tensorHom (id A) (id B) = id (A ⊗ B)` — the `tensor_id` law of
    mathlib's `MonoidalCategory`. -/
theorem tensorHom_id (A B : AR α β) :
    tensorHom (Hom.id A) (Hom.id B) = Hom.id (A.concat B) :=
  Graph.Hom.concatMap_id A.inBounds

/-- `tensorHom (f₁ ; g₁) (f₂ ; g₂) = tensorHom f₁ f₂ ; tensorHom g₁ g₂`
    — the `tensor_comp` law of mathlib's `MonoidalCategory`. -/
theorem tensorHom_comp {A A' A'' B B' B'' : AR α β}
    (f : Hom A A') (f' : Hom A' A'')
    (g : Hom B B') (g' : Hom B' B'') :
    (tensorHom f g).comp (tensorHom f' g') =
      tensorHom (f.comp f') (g.comp g') :=
  Graph.Hom.concatMap_comp A.inBounds A'.inBounds f f' g g'

/-! ### Strict monoid structure (associativity + unitors as equalities)

The underlying `Graph` operations satisfy `concat_assoc`,
`empty_concat`, `concat_empty` as *equalities* (@cite{jardine-heinz-2015}
Theorems 1 + 3). The bundled `AR` lifts these directly: the underlying
graphs are equal by `Graph.concat_assoc` etc., and the `inBounds` /
`planar` proofs match by proof irrelevance (they're propositions of
the same `Graph`).

These strict equalities mean the `MonoidalCategory`'s associator and
unitor natural isomorphisms can be constructed as `eqToIso`, which
trivialises the naturality conditions.
-/

/-- Two ARs are equal iff their underlying `Graph`s are equal —
    the `inBounds` and `planar` proofs match by proof irrelevance.
    Cheap helper for lifting Graph-level equalities to AR. -/
theorem ext_toGraph {A B : AR α β} (h : A.toGraph = B.toGraph) : A = B := by
  cases A; cases B
  simp only at h
  subst h
  rfl

/-- Concatenation is associative on AR (lifted from `Graph.concat_assoc`). -/
theorem concat_assoc (A B C : AR α β) :
    (A.concat B).concat C = A.concat (B.concat C) :=
  ext_toGraph (Graph.concat_assoc A.toGraph B.toGraph C.toGraph)

/-- `empty` is a left identity for `concat` on AR (lifted from
    `Graph.empty_concat`). -/
theorem empty_concat (A : AR α β) : empty.concat A = A :=
  ext_toGraph (Graph.empty_concat A.toGraph)

/-- `empty` is a right identity for `concat` on AR (lifted from
    `Graph.concat_empty`). -/
theorem concat_empty (A : AR α β) : A.concat empty = A :=
  ext_toGraph (Graph.concat_empty A.toGraph)

end AR

end Phonology.Autosegmental
