/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Monoidal.Category
import Linglib.Core.Data.Fin.Tuple.Basic
import Linglib.Phonology.Autosegmental.Graph

/-!
# The monoidal category of autosegmental representations

`Autosegmental.AR α β` is the base object of the autosegmental category: an
in-bounds `Graph α β`. In-boundedness is constitutive; planarity
([goldsmith-1976]'s No-Crossing Constraint) is the *constraint* carving out the
full monoidal subcategory `WellFormedAR` (`WellFormedAR.lean`). The monoidal
product is morpheme concatenation ([jardine-heinz-2015]) with the empty
representation as unit; associator and unitors are `eqToIso` of the object
`Monoid` laws, so `AR` is strict monoidal over its object-monoid.

## Main definitions

* `AR α β` — the in-bounds autosegmental graph; the base object.
* `AR.Hom A B` — a label/link-preserving morphism whose tier maps are
  `LabeledTuple.Hom`s; `Category (AR α β)` via `id`/`comp`.
* `AR.concat` — morpheme concatenation; `AR.empty` the unit (`Monoid (AR α β)`).
* `AR.Hom.concatMap` — the concatenation bifunctor on morphisms (`tensorHom`);
  its tier action delegates to `LabeledTuple.Hom.concatMap`.
* `MonoidalCategory (AR α β)` — `concat` as `⊗`, `empty` as `𝟙_`.
-/

namespace Autosegmental

open Graph CategoryTheory

variable {α β : Type*}

/-- The base object of the autosegmental category: an **in-bounds** autosegmental
    graph (every association line falls within the tier lengths). Planarity is
    *not* carried here — it is the constraint defining the subcategory `WellFormedAR`. -/
structure AR (α β : Type*) extends Graph α β where
  inBounds : toGraph.InBounds

namespace AR

/-- `Fin` index of a link's upper endpoint (in bounds by `A.inBounds`). -/
def upperIdx (A : AR α β) {p : ℕ × ℕ} (hp : p ∈ A.links) : Fin A.upper.len :=
  ⟨p.1, (A.inBounds p hp).1⟩

/-- `Fin` index of a link's lower endpoint. -/
def lowerIdx (A : AR α β) {p : ℕ × ℕ} (hp : p ∈ A.links) : Fin A.lower.len :=
  ⟨p.2, (A.inBounds p hp).2⟩

@[simp] theorem upperIdx_val (A : AR α β) {p : ℕ × ℕ} (hp : p ∈ A.links) :
    (A.upperIdx hp : ℕ) = p.1 := rfl

@[simp] theorem lowerIdx_val (A : AR α β) {p : ℕ × ℕ} (hp : p ∈ A.links) :
    (A.lowerIdx hp : ℕ) = p.2 := rfl

/-! ### Morphisms -/

/-- A label- and link-preserving morphism. The tier maps are `LabeledTuple.Hom`s
    (each bundles a position map with its label-preservation `b.label ∘ f = a.label`);
    link preservation routes a link's (in-bounds) endpoints through those maps. -/
@[ext]
structure Hom (A B : AR α β) where
  /-- Vertex map on the upper tier (a label-preserving `LabeledTuple` morphism). -/
  fU : LabeledTuple.Hom A.upper B.upper
  /-- Vertex map on the lower tier. -/
  fL : LabeledTuple.Hom A.lower B.lower
  /-- Association lines are preserved. -/
  links_preserve : ∀ {i j : ℕ} (hi : i < A.upper.len) (hj : j < A.lower.len),
    (i, j) ∈ A.links → ((fU.toFun ⟨i, hi⟩ : ℕ), (fL.toFun ⟨j, hj⟩ : ℕ)) ∈ B.links

namespace Hom
variable {A B C : AR α β}

/-- The identity morphism. -/
def id (A : AR α β) : Hom A A where
  fU := LabeledTuple.Hom.id A.upper
  fL := LabeledTuple.Hom.id A.lower
  links_preserve _ _ h := h

/-- Composition of morphisms (diagrammatic: `f` then `g`). -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  fU := f.fU.comp g.fU
  fL := f.fL.comp g.fL
  links_preserve hi hj h := by
    have key := g.links_preserve (f.fU.toFun ⟨_, hi⟩).isLt (f.fL.toFun ⟨_, hj⟩).isLt
      (f.links_preserve hi hj h)
    simpa [LabeledTuple.Hom.comp] using key

@[simp] theorem id_fU (A : AR α β) : (Hom.id A).fU = LabeledTuple.Hom.id A.upper := rfl
@[simp] theorem id_fL (A : AR α β) : (Hom.id A).fL = LabeledTuple.Hom.id A.lower := rfl
@[simp] theorem comp_fU (f : Hom A B) (g : Hom B C) : (f.comp g).fU = f.fU.comp g.fU := rfl
@[simp] theorem comp_fL (f : Hom A B) (g : Hom B C) : (f.comp g).fL = f.fL.comp g.fL := rfl

end Hom

instance : CategoryStruct (AR α β) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g

instance : Category (AR α β) where
  id_comp _ := by apply Hom.ext <;> rfl
  comp_id _ := by apply Hom.ext <;> rfl
  assoc _ _ _ := by apply Hom.ext <;> rfl

@[simp] theorem id_fU' (A : AR α β) : (𝟙 A : Hom A A).fU = 𝟙 A.upper := rfl
@[simp] theorem id_fL' (A : AR α β) : (𝟙 A : Hom A A).fL = 𝟙 A.lower := rfl
@[simp] theorem comp_fU' {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fU = f.fU.comp g.fU := rfl
@[simp] theorem comp_fL' {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fL = f.fL.comp g.fL := rfl

/-! ### Concatenation: the tensor object -/

/-- Morpheme concatenation ([jardine-heinz-2015]): the tier-concatenated,
    index-shifted graph, in-bounds by `Graph.inBounds_concat`. -/
def concat (A B : AR α β) : AR α β where
  toGraph := A.toGraph.concat B.toGraph
  inBounds := Graph.inBounds_concat A.inBounds B.inBounds

@[simp] theorem concat_toGraph (A B : AR α β) :
    (A.concat B).toGraph = A.toGraph.concat B.toGraph := rfl

@[simp] theorem concat_upper (A B : AR α β) :
    (A.concat B).upper = A.upper.concat B.upper := rfl

@[simp] theorem concat_lower (A B : AR α β) :
    (A.concat B).lower = A.lower.concat B.lower := rfl

theorem links_concat (A B : AR α β) :
    (A.concat B).links =
      A.links ∪ B.links.image (shiftLink A.upper.len A.lower.len) := rfl

/-! ### The concatenation bifunctor `concatMap` (the tensor on morphisms)

The tier action delegates to the keystone `LabeledTuple.Hom.concatMap`; only link
preservation is bespoke, routing the A-block through `f` (unshifted) and the
B-block through `g` (shifted past `A'`) via `Fin.appendMap_val`. -/

namespace Hom
variable {A A' B B' : AR α β}

/-- The concatenation bifunctor on morphisms (`f ⊗ g`): `f` on the A-block,
    `g` (shifted) on the B-block. Tiers via `LabeledTuple.Hom.concatMap`. -/
def concatMap (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') where
  fU := LabeledTuple.Hom.concatMap f.fU g.fU
  fL := LabeledTuple.Hom.concatMap f.fL g.fL
  links_preserve {i j} hi hj h := by
    simp only [links_concat, Finset.mem_union, Finset.mem_image, shiftLink,
      Prod.exists, Prod.mk.injEq, LabeledTuple.Hom.concatMap_toFun] at h ⊢
    rcases h with hA | ⟨a, b, hab, hai, hbj⟩
    · obtain ⟨hiu, hjl⟩ := A.inBounds (i, j) hA
      left
      rw [Fin.appendMap_val, dif_pos hiu, Fin.appendMap_val, dif_pos hjl]
      exact f.links_preserve hiu hjl hA
    · obtain ⟨hau, hbl⟩ := B.inBounds (a, b) hab
      subst hai hbj
      right
      refine ⟨(g.fU.toFun ⟨a, hau⟩ : ℕ), (g.fL.toFun ⟨b, hbl⟩ : ℕ),
        g.links_preserve hau hbl hab, ?_, ?_⟩
      · rw [Fin.appendMap_val, dif_neg (show ¬ (a + A.upper.len) < A.upper.len by omega)]
        congr 2; apply Fin.ext; simp
      · rw [Fin.appendMap_val, dif_neg (show ¬ (b + A.lower.len) < A.lower.len by omega)]
        congr 2; apply Fin.ext; simp

@[simp] theorem concatMap_fU (f : Hom A A') (g : Hom B B') :
    (concatMap f g).fU = LabeledTuple.Hom.concatMap f.fU g.fU := rfl

@[simp] theorem concatMap_fL (f : Hom A A') (g : Hom B B') :
    (concatMap f g).fL = LabeledTuple.Hom.concatMap f.fL g.fL := rfl

/-- The concat bifunctor preserves identities (`tensor_id`). -/
theorem concatMap_id (A B : AR α β) :
    concatMap (Hom.id A) (Hom.id B) = Hom.id (A.concat B) := by
  apply Hom.ext <;>
    simp only [concatMap_fU, concatMap_fL, id_fU, id_fL, LabeledTuple.Hom.concatMap_id,
      concat_upper, concat_lower]

/-- The concat bifunctor preserves composition (`tensor_comp`). -/
theorem concatMap_comp {A A' A'' B B' B'' : AR α β}
    (f : Hom A A') (f' : Hom A' A'') (g : Hom B B') (g' : Hom B' B'') :
    (concatMap f g).comp (concatMap f' g') = concatMap (f.comp f') (g.comp g') := by
  apply Hom.ext
  · simp only [comp_fU, concatMap_fU]
    exact (LabeledTuple.Hom.concatMap_comp f.fU f'.fU g.fU g'.fU).symm
  · simp only [comp_fL, concatMap_fL]
    exact (LabeledTuple.Hom.concatMap_comp f.fL f'.fL g.fL g'.fL).symm

end Hom

/-! ### Monoid structure on objects -/

/-- The empty (unit) object: no tiers, no links. -/
def empty : AR α β where
  toGraph := Graph.empty
  inBounds := Graph.inBounds_empty

/-- Two ARs are equal iff their underlying graphs are (`inBounds` by proof
    irrelevance). -/
theorem ext_toGraph {A B : AR α β} (h : A.toGraph = B.toGraph) : A = B := by
  cases A; cases B; simp only at h; subst h; rfl

/-- Objects form a `Monoid` under concatenation, with `empty` as unit
    ([jardine-heinz-2015] Theorems 1, 3): the laws lift the `Graph` monoid laws
    through `ext_toGraph`. -/
instance instMonoid : Monoid (AR α β) where
  mul := concat
  one := empty
  mul_assoc A B C := ext_toGraph (Graph.concat_assoc A.toGraph B.toGraph C.toGraph)
  one_mul A := ext_toGraph (Graph.empty_concat A.toGraph)
  mul_one A := ext_toGraph (Graph.concat_empty A.toGraph)

@[simp] theorem mul_eq_concat (A B : AR α β) : A * B = A.concat B := rfl

@[simp] theorem one_eq_empty : (1 : AR α β) = empty := rfl

/-! ### Monoidal category structure

`(AR α β, concat, empty)` is a monoidal category. Because the object `Monoid`
laws hold as strict equalities, the associator and unitors are `eqToIso` of
`mul_assoc`/`one_mul`/`mul_one`, so the coherence laws reduce to `eqToHom`
algebra (pentagon, triangle) or `Fin`-index arithmetic (naturalities).
-/

open CategoryTheory MonoidalCategory

/-- The upper tier map of an `eqToHom`, as a function: the length-cast `Fin.cast`
    (goes straight to the `len` level, avoiding a nested `LabeledTuple` `eqToHom`). -/
@[simp] theorem eqToHom_fU_toFun {A B : AR α β} (h : A = B) :
    (eqToHom h).fU.toFun = Fin.cast (congrArg (fun X => X.upper.len) h) := by
  cases h; rfl

/-- The lower tier map of an `eqToHom`, as a function. -/
@[simp] theorem eqToHom_fL_toFun {A B : AR α β} (h : A = B) :
    (eqToHom h).fL.toFun = Fin.cast (congrArg (fun X => X.lower.len) h) := by
  cases h; rfl

/-- Tensoring an identity (left) with an `eqToHom` (right) is an `eqToHom`. -/
@[simp] theorem concatMap_id_eqToHom {W X Y : AR α β} (h : X = Y) :
    Hom.concatMap (𝟙 W) (eqToHom h) = eqToHom (congrArg (W.concat ·) h) := by
  cases h; simp only [eqToHom_refl]; exact Hom.concatMap_id W X

/-- Tensoring an `eqToHom` (left) with an identity (right) is an `eqToHom`. -/
@[simp] theorem concatMap_eqToHom_id {W X Y : AR α β} (h : X = Y) :
    Hom.concatMap (eqToHom h) (𝟙 W) = eqToHom (congrArg (·.concat W) h) := by
  cases h; simp only [eqToHom_refl]; exact Hom.concatMap_id X W

/-- The tensor is `concat`; associator and unitors are `eqToIso` of the object
    `Monoid` laws (`AR` is strict monoidal over its object-monoid). -/
@[simps] instance instMonoidalStruct : MonoidalCategoryStruct (AR α β) where
  tensorObj := AR.concat
  tensorUnit := AR.empty
  tensorHom f g := Hom.concatMap f g
  whiskerLeft X _ _ f := Hom.concatMap (Hom.id X) f
  whiskerRight f Y := Hom.concatMap f (Hom.id Y)
  associator A B C := eqToIso (mul_assoc A B C)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)

instance : MonoidalCategory (AR α β) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := Hom.concatMap_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => Hom.concatMap_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply Hom.ext <;>
        · apply LabeledTuple.Hom.ext
          funext x
          apply Fin.ext
          simp [Fin.appendMap_val, Nat.sub_sub]
          split_ifs <;> omega)
    (leftUnitor_naturality := by
      intro X Y f
      apply Hom.ext <;>
        · apply LabeledTuple.Hom.ext
          funext x
          apply Fin.ext
          simp [Fin.appendMap_val, empty, Graph.empty]
          rfl)
    (rightUnitor_naturality := by
      intro X Y f
      apply Hom.ext <;>
        · apply LabeledTuple.Hom.ext
          funext x
          apply Fin.ext
          simp [Fin.appendMap_val, empty, Graph.empty])
    (pentagon := by intros; simp [eqToHom_trans])
    (triangle := by intros; simp [eqToHom_trans])

end AR

end Autosegmental
