/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Monoidal.Category
import Linglib.Phonology.Autosegmental.Graph

/-!
# The monoidal category of autosegmental representations

`Autosegmental.AR α β` is the base object of the autosegmental category: an
in-bounds `Graph α β` (an `upper` tier of `α`s, a `lower` tier of `β`s, and a
finite set of association lines, with every line falling within the tier
lengths). In-boundedness is *constitutive* — a graph with an out-of-range link
is junk, not an object — whereas planarity ([goldsmith-1976]'s No-Crossing
Constraint) is a *constraint* that carves out a full monoidal subcategory
(`WellFormedAR`, in `WellFormed.lean`).

Morphisms are `Fin`-indexed, label- and link-preserving vertex maps
(`AR.Hom`). The monoidal product is morpheme concatenation
([jardine-heinz-2015]), with the empty representation as unit; the associator
and unitors are `eqToIso` of the underlying object `Monoid` laws, so `AR` is
strict monoidal over its object-monoid.

## Main definitions

* `AR α β` — the in-bounds autosegmental graph; the base object.
* `AR.Hom A B` — a `Fin`-indexed label- and link-preserving morphism;
  `Hom.id`/`Hom.comp` make `AR α β` a `Category`.
* `AR.concat` — morpheme concatenation; `AR.empty` the unit
  (`Monoid (AR α β)`).
* `AR.Hom.concatMap` — the concatenation bifunctor on morphisms (`tensorHom`).
* `MonoidalCategory (AR α β)` — `concat` as `⊗`, `empty` as `𝟙_`.

## Implementation notes

Tiers are `Fin`-indexed in the *morphisms* (`fUpper : Fin A.upper.length →
Fin B.upper.length`), giving extensionality for free, while the *object*'s
`links : Finset (ℕ × ℕ)` stays raw-`ℕ`-indexed (matching the `MonovaryOn`-based
planarity substrate). The bridge between the two is `AR.upperIdx`/`lowerIdx`,
which read a link's in-bounds endpoints as `Fin` indices via the `inBounds`
field. `concatMap`'s index maps are assembled from `finSumFinEquiv` and
`finCongr` (the non-definitional `(A.concat B).length = A.length + B.length`);
their behaviour is pinned by the value-characterisation lemmas
`concatUpper_val`/`concatLower_val`.
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
def upperIdx (A : AR α β) {p : ℕ × ℕ} (hp : p ∈ A.links) : Fin A.upper.length :=
  ⟨p.1, (A.inBounds p hp).1⟩

/-- `Fin` index of a link's lower endpoint. -/
def lowerIdx (A : AR α β) {p : ℕ × ℕ} (hp : p ∈ A.links) : Fin A.lower.length :=
  ⟨p.2, (A.inBounds p hp).2⟩

/-! ### Morphisms -/

/-- A label- and link-preserving morphism, `Fin`-indexed on the tiers. The
    label conditions use total `getElem` (no `Option`); link preservation reads
    the endpoints as `Fin` indices via `upperIdx`/`lowerIdx`. -/
@[ext]
structure Hom (A B : AR α β) where
  /-- Vertex map on the upper tier. -/
  fUpper : Fin A.upper.length → Fin B.upper.length
  /-- Vertex map on the lower tier. -/
  fLower : Fin A.lower.length → Fin B.lower.length
  /-- The upper map preserves labels. -/
  upper_label : ∀ i, B.upper[fUpper i] = A.upper[i]
  /-- The lower map preserves labels. -/
  lower_label : ∀ j, B.lower[fLower j] = A.lower[j]
  /-- Association lines are preserved. -/
  links_preserve : ∀ {p : ℕ × ℕ} (hp : p ∈ A.links),
    ((fUpper (A.upperIdx hp) : ℕ), (fLower (A.lowerIdx hp) : ℕ)) ∈ B.links

namespace Hom
variable {A B C : AR α β}

/-- The identity morphism. -/
def id (A : AR α β) : Hom A A where
  fUpper := _root_.id
  fLower := _root_.id
  upper_label _ := rfl
  lower_label _ := rfl
  links_preserve hp := hp

/-- Composition of morphisms (diagrammatic order: `f.comp g` is `f` then `g`). -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  fUpper := g.fUpper ∘ f.fUpper
  fLower := g.fLower ∘ f.fLower
  upper_label i := by simp only [Function.comp_apply, g.upper_label, f.upper_label]
  lower_label j := by simp only [Function.comp_apply, g.lower_label, f.lower_label]
  links_preserve hp := g.links_preserve (f.links_preserve hp)

end Hom

instance : CategoryStruct (AR α β) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g

instance : Category (AR α β) where
  id_comp _ := by apply Hom.ext <;> rfl
  comp_id _ := by apply Hom.ext <;> rfl
  assoc _ _ _ := by apply Hom.ext <;> rfl

/-! ### Concatenation: the tensor object -/

/-- Morpheme concatenation ([jardine-heinz-2015]): the tier-concatenated,
    index-shifted graph, in-bounds by `Graph.inBounds_concat`. -/
def concat (A B : AR α β) : AR α β where
  toGraph := A.toGraph.concat B.toGraph
  inBounds := Graph.inBounds_concat A.inBounds B.inBounds

theorem concat_upper_len (A B : AR α β) :
    (A.concat B).upper.length = A.upper.length + B.upper.length := by
  show (A.toGraph.concat B.toGraph).upper.length = _
  simp [Graph.upper_concat]

theorem concat_lower_len (A B : AR α β) :
    (A.concat B).lower.length = A.lower.length + B.lower.length := by
  show (A.toGraph.concat B.toGraph).lower.length = _
  simp [Graph.lower_concat]

theorem upper_concat (A B : AR α β) : (A.concat B).upper = A.upper ++ B.upper := rfl

theorem lower_concat (A B : AR α β) : (A.concat B).lower = A.lower ++ B.lower := rfl

theorem links_concat (A B : AR α β) :
    (A.concat B).links =
      A.links ∪ B.links.image (shiftLink A.upper.length A.lower.length) := rfl

/-! ### The concatenation bifunctor `concatMap` (the tensor on morphisms) -/

namespace Hom
variable {A A' B B' : AR α β}

/-- Underlying upper index map of the concat bifunctor: `f` on the A-block,
    `g` (shifted) on the B-block, via `finSumFinEquiv`. -/
def concatUpper (f : Hom A A') (g : Hom B B') :
    Fin (A.concat B).upper.length → Fin (A'.concat B').upper.length :=
  finCongr (concat_upper_len A' B').symm ∘ finSumFinEquiv ∘
    Sum.map f.fUpper g.fUpper ∘ finSumFinEquiv.symm ∘ finCongr (concat_upper_len A B)

/-- Underlying lower index map of the concat bifunctor. -/
def concatLower (f : Hom A A') (g : Hom B B') :
    Fin (A.concat B).lower.length → Fin (A'.concat B').lower.length :=
  finCongr (concat_lower_len A' B').symm ∘ finSumFinEquiv ∘
    Sum.map f.fLower g.fLower ∘ finSumFinEquiv.symm ∘ finCongr (concat_lower_len A B)

/-- Value characterisation of `concatUpper`: A-indices route through `f`,
    B-indices (shifted) through `g`. -/
theorem concatUpper_val (f : Hom A A') (g : Hom B B')
    (i : Fin (A.concat B).upper.length) :
    (concatUpper f g i : ℕ) =
      if h : (i : ℕ) < A.upper.length then (f.fUpper ⟨i, h⟩ : ℕ)
      else (g.fUpper ⟨(i : ℕ) - A.upper.length,
        by have e := concat_upper_len A B; have := i.2; omega⟩ : ℕ) + A'.upper.length := by
  obtain ⟨i', rfl⟩ : ∃ i', i = (finCongr (concat_upper_len A B)).symm i' :=
    ⟨finCongr (concat_upper_len A B) i, by simp⟩
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i'
  · rw [dif_pos (by simp)]; simp [concatUpper]
  · rw [dif_neg (by simp)]; simp [concatUpper]; omega

theorem concatLower_val (f : Hom A A') (g : Hom B B')
    (j : Fin (A.concat B).lower.length) :
    (concatLower f g j : ℕ) =
      if h : (j : ℕ) < A.lower.length then (f.fLower ⟨j, h⟩ : ℕ)
      else (g.fLower ⟨(j : ℕ) - A.lower.length,
        by have e := concat_lower_len A B; have := j.2; omega⟩ : ℕ) + A'.lower.length := by
  obtain ⟨j', rfl⟩ : ∃ j', j = (finCongr (concat_lower_len A B)).symm j' :=
    ⟨finCongr (concat_lower_len A B) j, by simp⟩
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j'
  · rw [dif_pos (by simp)]; simp [concatLower]
  · rw [dif_neg (by simp)]; simp [concatLower]; omega

/-- `concatUpper` routes an A-tier index through `f`. -/
theorem concatUpper_lt (f : Hom A A') (g : Hom B B')
    (i : Fin (A.concat B).upper.length) (h : (i : ℕ) < A.upper.length) :
    (concatUpper f g i : ℕ) = (f.fUpper ⟨i, h⟩ : ℕ) := by
  rw [concatUpper_val, dif_pos h]

/-- `concatUpper` routes a B-tier index through `g`, shifted past `A'`. -/
theorem concatUpper_ge (f : Hom A A') (g : Hom B B')
    (i : Fin (A.concat B).upper.length) (h : ¬ (i : ℕ) < A.upper.length) :
    (concatUpper f g i : ℕ) =
      (g.fUpper ⟨(i : ℕ) - A.upper.length,
        by have e := concat_upper_len A B; have := i.2; omega⟩ : ℕ) + A'.upper.length := by
  rw [concatUpper_val, dif_neg h]

theorem concatLower_lt (f : Hom A A') (g : Hom B B')
    (j : Fin (A.concat B).lower.length) (h : (j : ℕ) < A.lower.length) :
    (concatLower f g j : ℕ) = (f.fLower ⟨j, h⟩ : ℕ) := by
  rw [concatLower_val, dif_pos h]

theorem concatLower_ge (f : Hom A A') (g : Hom B B')
    (j : Fin (A.concat B).lower.length) (h : ¬ (j : ℕ) < A.lower.length) :
    (concatLower f g j : ℕ) =
      (g.fLower ⟨(j : ℕ) - A.lower.length,
        by have e := concat_lower_len A B; have := j.2; omega⟩ : ℕ) + A'.lower.length := by
  rw [concatLower_val, dif_neg h]

/-- The concatenation bifunctor on morphisms (`f ⊗ g`): `f` on the A-block,
    `g` (shifted) on the B-block. -/
def concatMap (f : Hom A A') (g : Hom B B') : Hom (A.concat B) (A'.concat B') where
  fUpper := concatUpper f g
  fLower := concatLower f g
  upper_label i := by
    show (A'.upper ++ B'.upper)[concatUpper f g i] = (A.upper ++ B.upper)[i]
    rw [Fin.getElem_fin, Fin.getElem_fin]
    rcases lt_or_ge (i : ℕ) A.upper.length with h | h
    · have hb : (concatUpper f g i : ℕ) < A'.upper.length := by
        rw [concatUpper_lt f g i h]; exact (f.fUpper ⟨i, h⟩).isLt
      rw [List.getElem_append_left hb, List.getElem_append_left h]
      have hl := f.upper_label ⟨i, h⟩
      rw [Fin.getElem_fin, Fin.getElem_fin] at hl
      rw [← hl]; congr 1; exact concatUpper_lt f g i h
    · have hb : A'.upper.length ≤ (concatUpper f g i : ℕ) := by
        rw [concatUpper_ge f g i (by omega)]; omega
      rw [List.getElem_append_right hb, List.getElem_append_right h]
      have hl := g.upper_label ⟨(i : ℕ) - A.upper.length, by
        have e := concat_upper_len A B; have := i.2; omega⟩
      rw [Fin.getElem_fin, Fin.getElem_fin] at hl
      rw [← hl]; congr 1; rw [concatUpper_ge f g i (by omega)]; omega
  lower_label j := by
    show (A'.lower ++ B'.lower)[concatLower f g j] = (A.lower ++ B.lower)[j]
    rw [Fin.getElem_fin, Fin.getElem_fin]
    rcases lt_or_ge (j : ℕ) A.lower.length with h | h
    · have hb : (concatLower f g j : ℕ) < A'.lower.length := by
        rw [concatLower_lt f g j h]; exact (f.fLower ⟨j, h⟩).isLt
      rw [List.getElem_append_left hb, List.getElem_append_left h]
      have hl := f.lower_label ⟨j, h⟩
      rw [Fin.getElem_fin, Fin.getElem_fin] at hl
      rw [← hl]; congr 1; exact concatLower_lt f g j h
    · have hb : A'.lower.length ≤ (concatLower f g j : ℕ) := by
        rw [concatLower_ge f g j (by omega)]; omega
      rw [List.getElem_append_right hb, List.getElem_append_right h]
      have hl := g.lower_label ⟨(j : ℕ) - A.lower.length, by
        have e := concat_lower_len A B; have := j.2; omega⟩
      rw [Fin.getElem_fin, Fin.getElem_fin] at hl
      rw [← hl]; congr 1; rw [concatLower_ge f g j (by omega)]; omega
  links_preserve {p} hp := by
    show ((concatUpper f g ((A.concat B).upperIdx hp) : ℕ),
          (concatLower f g ((A.concat B).lowerIdx hp) : ℕ)) ∈ (A'.concat B').links
    have hmem : p ∈ A.links ∪ B.links.image (shiftLink A.upper.length A.lower.length) := hp
    rw [Finset.mem_union] at hmem
    rw [links_concat, Finset.mem_union]
    rcases hmem with hA | hB
    · left
      obtain ⟨hAu, hAl⟩ := A.inBounds p hA
      rw [concatUpper_lt f g _ hAu, concatLower_lt f g _ hAl]
      exact f.links_preserve hA
    · right
      rw [Finset.mem_image] at hB ⊢
      obtain ⟨q, hq, rfl⟩ := hB
      refine ⟨(↑(g.fUpper (B.upperIdx hq)), ↑(g.fLower (B.lowerIdx hq))),
        g.links_preserve hq, ?_⟩
      rw [concatUpper_ge f g _ (by simp [AR.upperIdx, shiftLink]),
        concatLower_ge f g _ (by simp [AR.lowerIdx, shiftLink])]
      simp only [shiftLink, Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;>
        · congr 2
          apply Fin.ext
          simp [AR.upperIdx, AR.lowerIdx]

@[simp] theorem concatMap_fUpper (f : Hom A A') (g : Hom B B') :
    (concatMap f g).fUpper = concatUpper f g := rfl

@[simp] theorem concatMap_fLower (f : Hom A A') (g : Hom B B') :
    (concatMap f g).fLower = concatLower f g := rfl

/-- The concat bifunctor preserves identities (`tensor_id`). -/
theorem concatMap_id (A B : AR α β) :
    concatMap (Hom.id A) (Hom.id B) = Hom.id (A.concat B) := by
  apply Hom.ext <;>
    · funext x; apply Fin.ext; simp [concatMap, concatUpper, concatLower, Hom.id]

/-- The concat bifunctor preserves composition (`tensor_comp`). -/
theorem concatMap_comp {A A' A'' B B' B'' : AR α β}
    (f : Hom A A') (f' : Hom A' A'') (g : Hom B B') (g' : Hom B' B'') :
    (concatMap f g).comp (concatMap f' g') = concatMap (f.comp f') (g.comp g') := by
  apply Hom.ext <;>
    · funext x; apply Fin.ext
      simp [concatMap, concatUpper, concatLower, comp, Function.comp_def, Sum.map_map]

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

@[simp] theorem id_fUpper (A : AR α β) : (𝟙 A : Hom A A).fUpper = _root_.id := rfl
@[simp] theorem id_fLower (A : AR α β) : (𝟙 A : Hom A A).fLower = _root_.id := rfl

@[simp] theorem comp_fUpper {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fUpper = g.fUpper ∘ f.fUpper := rfl
@[simp] theorem comp_fLower {A B C : AR α β} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).fLower = g.fLower ∘ f.fLower := rfl

/-- The upper index map of an `eqToHom` is the length-cast `finCongr`. -/
@[simp] theorem eqToHom_fUpper {A B : AR α β} (h : A = B) :
    (eqToHom h).fUpper = finCongr (congrArg (fun X => X.upper.length) h) := by
  cases h; rfl

/-- The lower index map of an `eqToHom` is the length-cast `finCongr`. -/
@[simp] theorem eqToHom_fLower {A B : AR α β} (h : A = B) :
    (eqToHom h).fLower = finCongr (congrArg (fun X => X.lower.length) h) := by
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
        · funext x
          apply Fin.ext
          simp [Hom.concatUpper_val, Hom.concatLower_val, concat_upper_len,
            concat_lower_len, Nat.sub_sub]
          split_ifs <;> omega)
    (leftUnitor_naturality := by
      intro X Y f
      apply Hom.ext <;>
        · funext x
          apply Fin.ext
          simp [Hom.concatUpper_val, Hom.concatLower_val, empty, Graph.empty]
          rfl)
    (rightUnitor_naturality := by
      intro X Y f
      apply Hom.ext
      · funext x
        apply Fin.ext
        simp [Hom.concatUpper_val, empty, Graph.empty]
        rw [dif_pos (lt_of_lt_of_eq x.isLt (by simp [upper_concat, empty, Graph.empty]))]
        rfl
      · funext x
        apply Fin.ext
        simp [Hom.concatLower_val, empty, Graph.empty]
        rw [dif_pos (lt_of_lt_of_eq x.isLt (by simp [lower_concat, empty, Graph.empty]))]
        rfl)
    (pentagon := by intros; simp [eqToHom_trans])
    (triangle := by intros; simp [eqToHom_trans])

end AR

end Autosegmental
