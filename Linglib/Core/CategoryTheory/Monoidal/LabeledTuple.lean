/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Linglib.Core.Data.Fin.Tuple.Basic

/-!
# The monoidal category of labeled finite tuples

`[UPSTREAM]` candidate for `Mathlib/CategoryTheory/Monoidal/`. A `LabeledTuple α`
is a finite tuple of `α`s: a length `n` and a labeling `Fin n → α`. Morphisms are
**label-preserving position maps** (`f : Fin a.len → Fin b.len` with
`b.label ∘ f = a.label`); this is a skeleton of `Over α` (finite `α`-labeled
sets) on `Fin`-objects.

Concatenation (`Fin.append` on labels, `+` on lengths) is the **categorical
coproduct** and `empty` the **initial object**, so the category is *cocartesian*:
its `MonoidalCategory` and `SymmetricCategory` are obtained for free from
`monoidalOfHasFiniteCoproducts`/`symmetricOfHasFiniteCoproducts` (unlike
`AugmentedSimplexCategory`, whose monotone maps make its ordinal sum *not* a
coproduct, forcing a bespoke monoidal structure). The tensor is `concat` up to
the chosen-coproduct isomorphism.

The concrete `Fin`-skeletal `concat`/`Hom.concatMap` defs (with their
`Fin.appendMap` action) are kept alongside: downstream clients that need the
literal `Fin (a.len + b.len)` carrier — e.g. autosegmental tiers with typed
links — consume those directly rather than the opaque coproduct tensor.

## Main definitions

* `LabeledTuple α` — a length-indexed labeled tuple; the object.
* `LabeledTuple.Hom a b` — a label-preserving position map.
* `LabeledTuple.concat` — concatenation; `LabeledTuple.empty` the unit.
* `LabeledTuple.Hom.concatMap` — the concatenation bifunctor on morphisms.
* `MonoidalCategory`/`SymmetricCategory (LabeledTuple α)` — the cocartesian
  structure: `concat` as `⊗` (up to coproduct iso), `empty` as `𝟙_`.
-/

universe u

open CategoryTheory MonoidalCategory

/-- A finite tuple of `α`s: a length and a labeling. -/
structure LabeledTuple (α : Type u) where
  /-- The length of the tuple. -/
  len : ℕ
  /-- The labeling of the positions. -/
  label : Fin len → α

namespace LabeledTuple

variable {α : Type u}

/-- Tuples are comparable when labels are: compare lengths, then the labelings
    (decidable as `Fin len` is a `Fintype`). Reduces under `decide`. -/
instance [DecidableEq α] : DecidableEq (LabeledTuple α)
  | ⟨la, fa⟩, ⟨lb, fb⟩ =>
    if h : la = lb then by subst h; exact decidable_of_iff (fa = fb) (by simp)
    else isFalse fun he => h (congrArg len he)

/-- A label-preserving position map. -/
@[ext]
structure Hom (a b : LabeledTuple α) where
  /-- The underlying position map. -/
  toFun : Fin a.len → Fin b.len
  /-- The map preserves labels. -/
  label_comp : b.label ∘ toFun = a.label

namespace Hom
variable {a b c : LabeledTuple α}

/-- The identity morphism. -/
def id (a : LabeledTuple α) : Hom a a := ⟨_root_.id, Function.comp_id a.label⟩

/-- Composition of morphisms (diagrammatic: `f` then `g`). -/
def comp (f : Hom a b) (g : Hom b c) : Hom a c :=
  ⟨g.toFun ∘ f.toFun, by rw [← Function.comp_assoc, g.label_comp, f.label_comp]⟩

@[simp] theorem id_toFun (a : LabeledTuple α) : (Hom.id a).toFun = _root_.id := rfl
@[simp] theorem comp_toFun (f : Hom a b) (g : Hom b c) :
    (f.comp g).toFun = g.toFun ∘ f.toFun := rfl

/-- A `Hom` is a label-preserving position map; bundle it as `FunLike` so `f i`
    applies it and the mathlib hom machinery (`DFunLike.ext`, …) is available. -/
instance : FunLike (Hom a b) (Fin a.len) (Fin b.len) where
  coe := Hom.toFun
  coe_injective _ _ h := Hom.ext h

@[simp] theorem coe_toFun (f : Hom a b) : ⇑f = f.toFun := rfl

end Hom

instance : Category (LabeledTuple α) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp _ := by apply Hom.ext; rfl
  comp_id _ := by apply Hom.ext; rfl
  assoc _ _ _ := by apply Hom.ext; rfl

@[simp] theorem id_toFun' (a : LabeledTuple α) : (𝟙 a : Hom a a).toFun = _root_.id := rfl
@[simp] theorem comp_toFun' {a b c : LabeledTuple α} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

/-- The index map of an `eqToHom` is the length-cast `finCongr`. -/
@[simp] theorem eqToHom_toFun {a b : LabeledTuple α} (h : a = b) :
    (eqToHom h).toFun = finCongr (congrArg len h) := by cases h; rfl

/-! ### Concatenation -/

/-- Concatenation of labeled tuples: lengths add, labels `Fin.append`. -/
def concat (a b : LabeledTuple α) : LabeledTuple α where
  len := a.len + b.len
  label := Fin.append a.label b.label

/-- The empty tuple — the monoidal unit. -/
def empty : LabeledTuple α where
  len := 0
  label := Fin.elim0

@[simp] theorem empty_len : (empty : LabeledTuple α).len = 0 := rfl

/-- The labeled tuple of a list: its length, positionally labeled. The ergonomic
    bridge for clients that build tiers from `List` literals. -/
def ofList (l : List α) : LabeledTuple α := ⟨l.length, l.get⟩

@[simp] theorem ofList_len (l : List α) : (ofList l).len = l.length := rfl
@[simp] theorem ofList_label (l : List α) : (ofList l).label = l.get := rfl

/-- The underlying list of labels, in position order. -/
def toList (a : LabeledTuple α) : List α := List.ofFn a.label

@[simp] theorem toList_length (a : LabeledTuple α) : a.toList.length = a.len := by
  simp [toList]

@[simp] theorem toList_ofList (l : List α) : (ofList l).toList = l := by
  simp [toList, ofList]

/-- Raw `ℕ`-indexed access, out-of-range to `none`: the positional view for
    clients that index tiers by `ℕ` (subgraph embedding, surface bookkeeping). -/
def get? (a : LabeledTuple α) (i : ℕ) : Option α :=
  if h : i < a.len then some (a.label ⟨i, h⟩) else none

@[simp] theorem ofList_get? (l : List α) (i : ℕ) : (ofList l).get? i = l[i]? := by
  simp only [get?, ofList_len, ofList_label]
  split <;> rename_i h
  · rw [List.getElem?_eq_getElem h, List.get_eq_getElem]
  · rw [List.getElem?_eq_none (by omega)]

theorem get?_eq_getElem? (a : LabeledTuple α) (i : ℕ) : a.get? i = a.toList[i]? := by
  unfold get?
  split <;> rename_i h
  · rw [List.getElem?_eq_getElem (by simpa using h)]; simp [toList, List.getElem_ofFn]
  · rw [List.getElem?_eq_none (by simpa using h)]

@[simp] theorem concat_len (a b : LabeledTuple α) : (a.concat b).len = a.len + b.len := rfl
@[simp] theorem concat_label (a b : LabeledTuple α) :
    (a.concat b).label = Fin.append a.label b.label := rfl

@[simp] theorem toList_concat (a b : LabeledTuple α) :
    (a.concat b).toList = a.toList ++ b.toList := by
  unfold toList
  rw [concat_label]
  exact List.ofFn_fin_append a.label b.label

/-- Raw access into a concatenation: left block through `a`, right through `b`. -/
theorem get?_concat_left {a b : LabeledTuple α} {i : ℕ} (h : i < a.len) :
    (a.concat b).get? i = a.get? i := by
  rw [get?_eq_getElem?, toList_concat, get?_eq_getElem?,
    List.getElem?_append_left (by simpa using h)]

theorem get?_concat_right (a b : LabeledTuple α) (j : ℕ) :
    (a.concat b).get? (a.len + j) = b.get? j := by
  rw [get?_eq_getElem?, toList_concat, get?_eq_getElem?,
    List.getElem?_append_right (by simp)]
  simp [toList_length]

/-- The concatenation bifunctor on morphisms: `Fin.appendMap` of the position
    maps. Label preservation is exactly `Fin`-append naturality. -/
def Hom.concatMap {a a' b b' : LabeledTuple α} (f : Hom a a') (g : Hom b b') :
    Hom (a.concat b) (a'.concat b') :=
  ⟨Fin.appendMap f.toFun g.toFun, Fin.append_comp_appendMap f.label_comp g.label_comp⟩

@[simp] theorem Hom.concatMap_toFun {a a' b b' : LabeledTuple α} (f : Hom a a') (g : Hom b b') :
    (f.concatMap g).toFun = Fin.appendMap f.toFun g.toFun := rfl

theorem Hom.concatMap_id (a b : LabeledTuple α) :
    (Hom.id a).concatMap (Hom.id b) = Hom.id (a.concat b) := by
  apply Hom.ext; simp [concatMap, Hom.id]

theorem Hom.concatMap_comp {a a' a'' b b' b'' : LabeledTuple α}
    (f : Hom a a') (f' : Hom a' a'') (g : Hom b b') (g' : Hom b' b'') :
    (f.comp f').concatMap (g.comp g') = (f.concatMap g).comp (f'.concatMap g') := by
  apply Hom.ext; simp [concatMap, Hom.comp, Fin.appendMap_comp]

/-! ### Monoid structure on objects -/

/-- Extensionality via a length equality and a cast-compatible labeling. The
    auto-generated structure `ext` would demand an unusable `HEq` on `label`
    (which depends on `len`), and the cast dependency here defeats the `@[ext]`
    generator, so this is a plain extensionality lemma. -/
theorem ext {a b : LabeledTuple α} (hlen : a.len = b.len)
    (hlabel : a.label = b.label ∘ Fin.cast hlen) : a = b := by
  obtain ⟨la, fa⟩ := a; obtain ⟨lb, fb⟩ := b
  cases hlen
  simp only [Fin.cast_refl, Function.comp_id] at hlabel
  subst hlabel; rfl

@[simp] theorem ofList_toList (a : LabeledTuple α) : ofList a.toList = a := by
  apply ext (by simp [ofList, toList])
  funext i
  simp only [ofList_label, toList, List.get_ofFn]
  congr 1

theorem concat_assoc (a b c : LabeledTuple α) :
    (a.concat b).concat c = a.concat (b.concat c) :=
  ext (Nat.add_assoc ..) (by simp only [concat_label]; exact Fin.append_assoc ..)

theorem empty_concat (a : LabeledTuple α) : empty.concat a = a :=
  ext (Nat.zero_add _) (by simp only [concat_label]; exact Fin.elim0_append _)

theorem concat_empty (a : LabeledTuple α) : a.concat empty = a :=
  ext (Nat.add_zero _) (by simp only [concat_label]; exact Fin.append_elim0 _)

/-- Objects form a `Monoid` under concatenation, with `empty` as unit. -/
instance instMonoid : Monoid (LabeledTuple α) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

@[simp] theorem mul_eq_concat (a b : LabeledTuple α) : a * b = a.concat b := rfl
@[simp] theorem one_eq_empty : (1 : LabeledTuple α) = empty := rfl

/-! ### Cocartesian monoidal structure

`empty` is the initial object and `concat` the categorical coproduct (with
coprojections `Fin.castAdd`/`Fin.natAdd`), so the category is cocartesian and its
`MonoidalCategory`/`SymmetricCategory` come for free. -/

open Limits

instance (Y : LabeledTuple α) : Subsingleton (empty ⟶ Y) :=
  ⟨fun _ _ => by apply Hom.ext; funext i; exact i.elim0⟩

instance (Y : LabeledTuple α) : Nonempty (empty ⟶ Y) :=
  ⟨⟨Fin.elim0, by funext i; exact i.elim0⟩⟩

instance : HasInitial (LabeledTuple α) :=
  hasInitial_of_unique empty

/-- The left coprojection `a ⟶ a.concat b`. -/
def inl (a b : LabeledTuple α) : Hom a (a.concat b) :=
  ⟨Fin.castAdd b.len, by funext i; exact Fin.append_left a.label b.label i⟩

/-- The right coprojection `b ⟶ a.concat b`. -/
def inr (a b : LabeledTuple α) : Hom b (a.concat b) :=
  ⟨Fin.natAdd a.len, by funext i; exact Fin.append_right a.label b.label i⟩

@[simp] theorem inl_toFun (a b : LabeledTuple α) : (inl a b).toFun = Fin.castAdd b.len := rfl
@[simp] theorem inr_toFun (a b : LabeledTuple α) : (inr a b).toFun = Fin.natAdd a.len := rfl

/-- The copairing of `f : a ⟶ T` and `g : b ⟶ T`, glued by `Fin.append`. -/
def coprodDesc {a b T : LabeledTuple α} (f : Hom a T) (g : Hom b T) : Hom (a.concat b) T where
  toFun := Fin.append f.toFun g.toFun
  label_comp := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using congrFun f.label_comp j
    · simpa using congrFun g.label_comp j

@[simp] theorem coprodDesc_toFun {a b T : LabeledTuple α} (f : Hom a T) (g : Hom b T) :
    (coprodDesc f g).toFun = Fin.append f.toFun g.toFun := rfl

/-- `concat` is the categorical coproduct, with `inl`/`inr` the coprojections. -/
instance (a b : LabeledTuple α) : HasBinaryCoproduct a b :=
  HasColimit.mk
    { cocone := BinaryCofan.mk (inl a b) (inr a b)
      isColimit := BinaryCofan.IsColimit.mk _ (fun f g => coprodDesc f g)
        (fun f g => by apply Hom.ext; funext i; simp)
        (fun f g => by apply Hom.ext; funext i; simp)
        (fun f g m h₁ h₂ => by
          apply Hom.ext; funext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · simpa using congrFun (congrArg Hom.toFun h₁) j
          · simpa using congrFun (congrArg Hom.toFun h₂) j) }

instance : HasBinaryCoproducts (LabeledTuple α) := hasBinaryCoproducts_of_hasColimit_pair _

noncomputable instance : MonoidalCategory (LabeledTuple α) :=
  monoidalOfHasFiniteCoproducts _

noncomputable instance : SymmetricCategory (LabeledTuple α) :=
  symmetricOfHasFiniteCoproducts _

end LabeledTuple
