module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Indexical fields

This file defines indexical fields, the social meanings of the variants of a linguistic
variable in the sense of [eckert-2008]. An indexical field assigns each variant the set of
meanings, stances, qualities or persona traits, that a use of the variant may activate. An
association field grades the assignment, giving each variant a signed strength toward each
trait, positive when the variant indexes the trait and negative when it indexes away from it,
and the traits a variant indexes toward form its indexical field.

## Main definitions

* `IndexicalField`: the meanings each variant of a variable indexes.
* `AssociationField`: the signed strength with which each variant indexes each trait, a matrix
  over an ordered ring.
* `AssociationField.Indexes`: a variant indexes a trait, the strength being positive.
* `AssociationField.Antipodal`: two variants index every trait in opposite directions.
* `AssociationField.support`: the indexical field of the traits a variant indexes.

## Main results

* `AssociationField.Antipodal.indexes_iff`: an antipodal pair index a trait in opposite
  directions.
* `AssociationField.Antipodal.disjoint_support`: an antipodal pair index no trait in common.

## Implementation notes

An association field is a `Matrix`, so composing associations through a mediating domain, the
indirect indexicality of [ochs-1992], is matrix multiplication, and inheriting a field along a
map of variant spaces is `Matrix.submatrix`. The carrier is any type with a zero and an order,
`SignType` for the sign-valued fields of [beltrama-solt-burnett-2023], an ordered semiring for
strengths that compose; the grounded fields of [burnett-2019] are indexical fields over the
Stereotype Content Model properties.

## References

* [eckert-2008]
* [ochs-1992]
* [beltrama-solt-burnett-2023]
* [burnett-2019]
-/

@[expose] public section

namespace SocialMeaning

/-- An indexical field assigns each variant of a variable the meanings it indexes. -/
abbrev IndexicalField (Variant Meaning : Type*) := Variant → Finset Meaning

/-- An association field assigns each variant of a variable a signed strength toward each
trait, positive when the variant indexes the trait and negative when it indexes away. -/
abbrev AssociationField (Variant Trait R : Type*) := Matrix Variant Trait R

namespace AssociationField

variable {Variant Trait R : Type*} {v v₁ v₂ : Variant} {t : Trait}

section Indexes

variable [Zero R] [LT R] (M : AssociationField Variant Trait R)

/-- A variant indexes a trait when its association with the trait is positive. -/
def Indexes (v : Variant) (t : Trait) : Prop := 0 < M v t

instance [DecidableLT R] : DecidableRel M.Indexes := λ _ _ => inferInstanceAs (Decidable (_ < _))

variable [Fintype Trait] [DecidableLT R]

/-- The support of a variant is the indexical field of the traits it indexes. -/
def support (v : Variant) : Finset Trait := Finset.univ.filter (M.Indexes v)

@[simp] theorem mem_support : t ∈ M.support v ↔ M.Indexes v t := by simp [support]

end Indexes

section Antipodal

variable [InvolutiveNeg R] (M : AssociationField Variant Trait R)

/-- Two variants are antipodal when they index every trait in opposite directions. -/
def Antipodal (v₁ v₂ : Variant) : Prop := M v₁ = -M v₂

variable {M}

theorem Antipodal.symm (h : M.Antipodal v₁ v₂) : M.Antipodal v₂ v₁ := (neg_eq_iff_eq_neg.2 h).symm

theorem antipodal_comm : M.Antipodal v₁ v₂ ↔ M.Antipodal v₂ v₁ := ⟨Antipodal.symm, Antipodal.symm⟩

end Antipodal

section AddGroup

variable [AddGroup R] [Preorder R] [AddLeftStrictMono R] {M : AssociationField Variant Trait R}

/-- An antipodal pair index a trait in opposite directions. -/
theorem Antipodal.indexes_iff (h : M.Antipodal v₁ v₂) : M.Indexes v₁ t ↔ M v₂ t < 0 := by
  rw [Indexes, h, Pi.neg_apply, neg_pos]

/-- An antipodal pair index no trait in common. -/
theorem Antipodal.disjoint_support [Fintype Trait] [DecidableLT R] (h : M.Antipodal v₁ v₂) :
    Disjoint (M.support v₁) (M.support v₂) :=
  Finset.disjoint_left.2 λ _ h₁ h₂ =>
    lt_asymm (M.mem_support.1 h₂) (h.indexes_iff.1 (M.mem_support.1 h₁))

end AddGroup

end AssociationField

end SocialMeaning
