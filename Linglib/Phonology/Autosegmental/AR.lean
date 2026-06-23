/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.GraphHom
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The autosegmental category `AR α β`

`AR α β` is the bundled type of **well-formed autosegmental
representations**: a `Graph α β` paired with proofs that the link
set is in-bounds and that the representation is planar (satisfies
[goldsmith-1976]'s No-Crossing Constraint, equivalently
[pulleyblank-1986]'s reformulated Well-Formedness Condition).

In mathlib's pattern (`Group` → `Grp`, `Module` → `ModuleCat`),
`Graph α β` is the underlying object type and `AR α β` is the
*bundled* type that carries the autosegmental well-formedness
invariants — the canonical objects of the category of autosegmental
representations. The bundled name `AR` matches the field's standard
abbreviation across [jardine-2017],
[chandlee-jardine-2019], [burness-mcmullin-2020] and the
broader Heinz-Jardine-Chandlee tradition.

## Main definitions (this file)

* `AR α β` — the bundled well-formed AR type (Graph + InBounds + Planar).
* `AR.empty`, `AR.concat` — lifted from Graph; concat preserves the
  invariants because [jardine-heinz-2015] Theorem 4 + our
  `inBounds_concat` lemma carry both invariants through.
* `AR.Hom A B := Graph.Hom A.toGraph B.toGraph`, `AR.Hom.id`/`AR.Hom.comp` —
  morphisms are graph homomorphisms on the underlying graphs, delegated
  to `Graph.Hom`.
* `Monoid (AR α β)` — the concatenation monoid ([jardine-heinz-2015]
  Theorems 1, 3).
* `CategoryTheory.MonoidalCategory (AR α β)` — `concat` as the tensor,
  `empty` as the unit, `tensorHom` the concatenation bifunctor; the
  associator and unitors are `eqToIso` of the `Monoid` laws
  (`mul_assoc`/`one_mul`/`mul_one`), so `AR` is strict monoidal over its
  object-monoid.
-/

namespace Autosegmental

/-! ### The bundled type `AR`

`AR α β` extends `Graph α β` with structural well-formedness
proofs. The Pulleyblank-1986 WFC is **planarity (NCC) alone**;
[goldsmith-1979]'s saturation is language-particular and is
*not* carried as a structural invariant here. `InBounds` is a
substrate-level requirement (Graph doesn't enforce links to fall
within tier lengths structurally; the subtype does).
-/

/-- A well-formed autosegmental representation: a `Graph` whose link
    set is in-bounds (`InBounds`) and which satisfies the No-Crossing
    Constraint (`IsPlanar`). Per [pulleyblank-1986], planarity is
    the sole universal structural well-formedness condition on
    autosegmental representations; [goldsmith-1979]'s additional
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

/-- Concatenation of ARs ([jardine-heinz-2015]): tiers are
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

/-! ### Monoid structure

`AR α β` is a `Monoid` under concatenation ([jardine-heinz-2015] Theorems 1, 3):
the laws lift the `Graph` monoid laws (`Graph.concat_assoc` etc.) through
`ext_toGraph` — the `inBounds`/`planar` proofs match by proof irrelevance. So
associativity and the unit laws are the `Monoid` API's `mul_assoc`/`one_mul`/`mul_one`.

Because those hold as strict equalities, the `MonoidalCategory`'s associator and
unitors are `eqToIso` of the monoid laws — `AR` is strict monoidal over its
object-monoid (the `Discrete.monoidal` pattern), so the coherence laws reduce to
`eqToHom` algebra.
-/

/-- Two ARs are equal iff their underlying `Graph`s are equal —
    the `inBounds` and `planar` proofs match by proof irrelevance.
    Cheap helper for lifting Graph-level equalities to AR. -/
theorem ext_toGraph {A B : AR α β} (h : A.toGraph = B.toGraph) : A = B := by
  cases A; cases B
  simp only at h
  subst h
  rfl

/-- ARs form a monoid under concatenation, with the empty AR as unit
    ([jardine-heinz-2015] Theorems 1, 3): the laws lift the `Graph` monoid laws
    through `ext_toGraph` (the `inBounds`/`planar` proofs match by proof
    irrelevance), so associativity and the unit laws are the `Monoid` API's
    `mul_assoc`/`one_mul`/`mul_one`. The underlying-graph map `AR.toGraph` is a
    monoid morphism (injective by `ext_toGraph`). -/
instance instMonoid : Monoid (AR α β) where
  mul := concat
  one := empty
  mul_assoc A B C := ext_toGraph (Graph.concat_assoc A.toGraph B.toGraph C.toGraph)
  one_mul A := ext_toGraph (Graph.empty_concat A.toGraph)
  mul_one A := ext_toGraph (Graph.concat_empty A.toGraph)

@[simp] theorem mul_eq_concat (A B : AR α β) : A * B = A.concat B := rfl

@[simp] theorem one_eq_empty : (1 : AR α β) = empty := rfl

/-! ### Category instance

`AR α β` is a `CategoryTheory.Category`: objects are well-formed
ARs, morphisms are graph homomorphisms. The category laws
(`id_comp`, `comp_id`, `assoc`) are inherited verbatim from
`Graph.Hom`.
-/

instance : CategoryTheory.CategoryStruct (AR α β) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance : CategoryTheory.Category (AR α β) where
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-! ### MonoidalCategory instance

`(AR α β, concat, empty)` is a monoidal category. The tensor product
is concatenation; the unit is the empty AR. Because `concat_assoc`,
`empty_concat`, and `concat_empty` hold as *strict equalities* on the
underlying graphs (and lift to AR equalities), the associator and
unitor natural isomorphisms are constructed via `eqToIso`, which
makes the naturality + coherence laws (pentagon, triangle) discharge
mechanically.
-/

open CategoryTheory

/-- The index maps of an `eqToHom` between ARs are the identity. -/
@[simp] theorem eqToHom_fUpper {A B : AR α β} (h : A = B) :
    (eqToHom h).fUpper = _root_.id := by cases h; rfl

@[simp] theorem eqToHom_fLower {A B : AR α β} (h : A = B) :
    (eqToHom h).fLower = _root_.id := by cases h; rfl

@[simp] theorem comp_fUpper {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fUpper = g.fUpper ∘ f.fUpper := rfl

@[simp] theorem comp_fLower {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fLower = g.fLower ∘ f.fLower := rfl

@[simp] theorem id_fUpper {A : AR α β} : (𝟙 A : Hom A A).fUpper = _root_.id := rfl

@[simp] theorem id_fLower {A : AR α β} : (𝟙 A : Hom A A).fLower = _root_.id := rfl

/-- Tensoring an identity with an `eqToHom` (right) is an `eqToHom`. -/
theorem tensorHom_id_eqToHom {W X Y : AR α β} (h : X = Y) :
    AR.tensorHom (𝟙 W) (eqToHom h) = eqToHom (congrArg (W.concat ·) h) := by
  cases h; simp only [eqToHom_refl]; exact tensorHom_id W X

/-- Tensoring an `eqToHom` with an identity (left) is an `eqToHom`. -/
theorem tensorHom_eqToHom_id {W X Y : AR α β} (h : X = Y) :
    AR.tensorHom (eqToHom h) (𝟙 W) = eqToHom (congrArg (·.concat W) h) := by
  cases h; simp only [eqToHom_refl]; exact tensorHom_id X W

/-- The associator and unitors are `eqToIso` of the `Monoid` laws `mul_assoc`/
    `one_mul`/`mul_one` (`AR` is strict monoidal over its object-monoid, the
    `Discrete.monoidal` pattern). -/
@[simps] instance instMonoidalStruct : MonoidalCategoryStruct (AR α β) where
  tensorObj := AR.concat
  tensorUnit := AR.empty
  tensorHom := AR.tensorHom
  whiskerLeft X _ _ f := AR.tensorHom (Hom.id X) f
  whiskerRight f Y := AR.tensorHom f (Hom.id Y)
  associator A B C := eqToIso (mul_assoc A B C)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)

instance : MonoidalCategory (AR α β) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := AR.tensorHom_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => AR.tensorHom_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intros
      apply Graph.Hom.ext <;> funext i <;>
        (simp [AR.tensorHom, Graph.Hom.concatMap, AR.concat, Graph.concat, Nat.sub_add_eq] <;>
         (first | rfl | omega | (split_ifs <;> first | rfl | omega))))
    (leftUnitor_naturality := by
      intros
      apply Graph.Hom.ext <;> funext i <;>
        (simp [AR.tensorHom, Graph.Hom.concatMap, AR.concat, AR.empty, Graph.concat, Graph.empty,
           List.length_nil, Nat.sub_zero, Nat.add_zero] <;>
         (first | rfl | omega | (split_ifs <;> first | rfl | omega))))
    (rightUnitor_naturality := by
      intros
      apply Graph.Hom.ext <;> funext i <;>
        (simp [AR.tensorHom, Graph.Hom.concatMap, AR.concat, AR.empty, Graph.concat, Graph.empty] <;>
         (first | rfl | omega | (split_ifs <;> first | rfl | omega) |
           (intro h; first | rw [Graph.Hom.upper_canonical _ _ h] |
             rw [Graph.Hom.lower_canonical _ _ h]))))
    (pentagon := by
      intros
      simp [tensorHom_id_eqToHom, tensorHom_eqToHom_id, eqToHom_trans])
    (triangle := by
      intros
      simp [tensorHom_id_eqToHom, tensorHom_eqToHom_id, eqToHom_trans])

end AR

end Autosegmental
