import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Hom.Basic
import Linglib.Core.Scale

/-!
# Category of Comparative Scales

Objects are bundled types with a preorder and `ComparativeScale` metadata
(boundedness classification). Morphisms are `OrderHom` (bundled monotone
maps from Mathlib).

The boundedness tag is metadata attached to objects — morphisms are
order-preserving but do not need to preserve boundedness. This mirrors
the relationship between `MereoDim` (injective monotone = `StrictMono`)
and `Monotone`: `MereoCat` requires strict monotonicity, while `ScaleCat`
uses the weaker `Monotone`.

Mathlib's `Preord` (category of preorders) is the underlying category;
`ScaleCat` adds the `ComparativeScale` annotation.
-/

universe u

namespace Core.Categorical

/-- Bundled comparative scale: a preordered type with boundedness metadata. -/
structure ScaleObj where
  /-- The carrier type. -/
  α : Type u
  /-- The preorder on the carrier. -/
  [preord : Preorder α]
  /-- The comparative scale metadata. -/
  scale : @Core.Scale.ComparativeScale α preord

attribute [instance] ScaleObj.preord

instance : CategoryTheory.Category ScaleObj.{u} where
  Hom A B := @OrderHom A.α B.α A.preord B.preord
  id A := @OrderHom.id A.α A.preord
  comp f g := @OrderHom.comp _ _ _ _ _ _ g f
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

/-- Extract the boundedness classification of a scale object. -/
def ScaleObj.boundedness (S : ScaleObj) : Core.Scale.Boundedness :=
  S.scale.boundedness

/-- The licensing prediction for a scale object. -/
def ScaleObj.isLicensed (S : ScaleObj) : Bool :=
  S.scale.isLicensed

/-- A morphism between scales with the same boundedness preserves licensing. -/
theorem ScaleObj.licensing_invariant (A B : ScaleObj)
    (h : A.boundedness = B.boundedness) :
    A.isLicensed = B.isLicensed :=
  congrArg Core.Scale.Boundedness.isLicensed h

end Core.Categorical
