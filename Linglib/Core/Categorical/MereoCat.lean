import Mathlib.CategoryTheory.Category.Basic
import Linglib.Core.MereoDim

/-!
# Category of Mereological Domains

Category with partially ordered types as objects and strictly monotone
(`MereoDim`) maps as morphisms. `StrictMono.id` and `StrictMono.comp`
from Mathlib provide the categorical identity and composition.

The `DimensionChain.toMereoMor` bridge connects the existing dimension
chain infrastructure to categorical morphisms, enabling the coherence
results in `Events/DimensionCoherence.lean`.
-/

universe u

namespace Core.Categorical

/-- Bundled partially ordered type: an object of the mereological category. -/
structure MereoObj where
  /-- The carrier type. -/
  α : Type u
  /-- The partial order on the carrier. -/
  [ord : PartialOrder α]

attribute [instance] MereoObj.ord

/-- A morphism in the mereological category: a bundled strictly monotone map.
    Corresponds to `MereoDim` in `Core/MereoDim.lean`. -/
structure MereoMor (A B : MereoObj.{u}) where
  /-- The underlying function. -/
  toFun : A.α → B.α
  /-- Strict monotonicity witness. -/
  strict_mono' : StrictMono toFun

namespace MereoMor

variable {A B C : MereoObj.{u}}

@[ext]
theorem ext {f g : MereoMor A B} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  obtain ⟨f, _⟩ := f; obtain ⟨g, _⟩ := g; congr; funext x; exact h x

/-- Identity morphism: the identity function is strictly monotone. -/
protected def id (A : MereoObj.{u}) : MereoMor A A where
  toFun := _root_.id
  strict_mono' := strictMono_id

/-- Composition of morphisms (diagrammatic order: f then g). -/
protected def comp (f : MereoMor A B) (g : MereoMor B C) : MereoMor A C where
  toFun := g.toFun ∘ f.toFun
  strict_mono' := g.strict_mono'.comp f.strict_mono'

/-- A `MereoMor` is monotone (forgetful map to the category of preorders). -/
theorem monotone (f : MereoMor A B) : Monotone f.toFun :=
  f.strict_mono'.monotone

end MereoMor

instance : CategoryTheory.Category MereoObj.{u} where
  Hom := MereoMor
  id := MereoMor.id
  comp f g := MereoMor.comp f g
  id_comp _ := MereoMor.ext (λ _ => rfl)
  comp_id _ := MereoMor.ext (λ _ => rfl)
  assoc _ _ _ := MereoMor.ext (λ _ => rfl)

end Core.Categorical

namespace Mereology

open Core.Categorical

/-- A `DimensionChain` yields a composite morphism in `MereoObj`.

    Given a chain `Source →f Inter →μ Measure` where both legs are `MereoDim`,
    the composition `μ ∘ f` is a morphism `⟨Source⟩ ⟶ ⟨Measure⟩` in the
    mereological category. -/
def DimensionChain.toMereoMor
    {Source Inter Measure : Type u}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}
    (dc : DimensionChain f μ) :
    MereoMor ⟨Source⟩ ⟨Measure⟩ where
  toFun := μ ∘ f
  strict_mono' := dc.composed.toStrictMono

/-- Each leg of a `DimensionChain` is individually a `MereoMor`. -/
def DimensionChain.leg₁ToMereoMor
    {Source Inter Measure : Type u}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}
    (dc : DimensionChain f μ) :
    MereoMor ⟨Source⟩ ⟨Inter⟩ where
  toFun := f
  strict_mono' := dc.leg₁.toStrictMono

def DimensionChain.leg₂ToMereoMor
    {Source Inter Measure : Type u}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}
    (dc : DimensionChain f μ) :
    MereoMor ⟨Inter⟩ ⟨Measure⟩ where
  toFun := μ
  strict_mono' := dc.leg₂.toStrictMono

/-- The composite morphism equals the categorical composition of the legs. -/
theorem DimensionChain.comp_eq
    {Source Inter Measure : Type u}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}
    (dc : DimensionChain f μ) :
    dc.toMereoMor =
    MereoMor.comp dc.leg₁ToMereoMor dc.leg₂ToMereoMor :=
  MereoMor.ext (λ _ => rfl)

end Mereology
