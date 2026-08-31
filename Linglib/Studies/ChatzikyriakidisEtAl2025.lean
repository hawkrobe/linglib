import Linglib.Data.Examples.Schema
import Mathlib.Logic.Equiv.Defs

/-!
# Chatzikyriakidis, Cooper, Gregoromichelaki and Sutton 2025: intentional identity in TTR

This file formalizes the treatment of [geach-1967]'s Hob–Nob sentence — *Hob thinks a witch has
blighted Bob's mare, and Nob wonders whether she (the same witch) killed Cob's sow* — in
[chatzikyriakidis-etal-2025] §2.3.2, following [ranta-1994]'s belief contexts as recast by
[cooper-2023] with record types. The discourse is acceptable although no witch need exist and
neither attitude holder need know of the other, so what the two attitudes share cannot be an
individual. On this account it is a type: Hob's and Nob's contents both have the witch type as a
component, and types are individuated intensionally, so the two contents can share it while
remaining distinct and while the type is empty. The datum is
`Data/Examples/ChatzikyriakidisEtAl2025.json`.

The full analysis also aligns labels across the two belief contexts, giving sameness of discourse
referent rather than merely of type; that needs dependent record substrate.

## Main definitions

* `Tag`, `IType` — a carrier with an identity beyond its extension
* `IType.extEquiv`, `IType.intEq`, `IType.meet` — extensional equivalence, intensional identity,
  and the meet that preserves it
* `witchType`, `hobContent`, `nobContent`, `SharesComponent` — the model and component sharing

## Main results

* `extEquiv_not_intEq` — the two contents are extensionally equivalent and intensionally distinct,
  which a possible-worlds content cannot manage
* `intentional_identity` — they share the witch type, remain distinct, and the type is empty

## References

* [chatzikyriakidis-etal-2025]
* [geach-1967]
* [ranta-1994]
* [cooper-2023]
-/

namespace ChatzikyriakidisEtAl2025

/-! ### Intensional types

[cooper-2023] §1.3: types are individuated beyond their extensions — a
name-tagged wrapper over a Lean carrier suffices for the Hob–Nob model. -/

/-- The atoms of the model, and their meets: what individuates a type beyond its extension. -/
inductive Tag where
  /-- The witch. -/
  | witch
  /-- Blighting Bob's mare. -/
  | blightBobsMare
  /-- Killing Cob's sow. -/
  | killCobsSow
  /-- The meet of two tags. -/
  | meet (a b : Tag)
  deriving DecidableEq, Repr

/-- An intensional type: a carrier tagged with an identity beyond its
extension ([cooper-2023] §1.3). -/
structure IType where
  /-- The underlying Lean type (extension carrier) -/
  carrier : Type
  /-- Intensional identity tag -/
  name : Tag

/-- Extensional equivalence: equivalent carriers. -/
def IType.extEquiv (T₁ T₂ : IType) : Prop := Nonempty (T₁.carrier ≃ T₂.carrier)

/-- Intensional identity. -/
def IType.intEq (T₁ T₂ : IType) : Prop := T₁ = T₂

/-- Meet: pair the carriers, compose the names — intensional identity is
preserved through meet. -/
def IType.meet (T₁ T₂ : IType) : IType :=
  ⟨T₁.carrier × T₂.carrier, .meet T₁.name T₂.name⟩

/-! ### TTR model of the Hob–Nob puzzle -/

/-- The shared witch type: empty carrier (no witch exists), individuated
intensionally by its name. -/
def witchType : IType := ⟨Empty, .witch⟩

/-- "blighted Bob's mare" as a predicate type. -/
def blightBobsMare : IType := ⟨Unit, .blightBobsMare⟩

/-- "killed Cob's sow" as a predicate type. -/
def killCobsSow : IType := ⟨Unit, .killCobsSow⟩

/-- Hob's belief content: a witch who blighted Bob's mare. -/
def hobContent : IType := witchType.meet blightBobsMare

/-- Nob's wonder content: the *same* witch type, met with killing Cob's sow. -/
def nobContent : IType := witchType.meet killCobsSow

/-- `C` has `T` as its left meet component: witnesses of `C` are pairs whose
first coordinate inhabits `T`. Two contents stand in intentional identity
when they share a component in this sense. -/
def SharesComponent (T C : IType) : Prop := ∃ X, C = T.meet X

theorem sharesComponent_hobContent : SharesComponent witchType hobContent :=
  ⟨blightBobsMare, rfl⟩

theorem sharesComponent_nobContent : SharesComponent witchType nobContent :=
  ⟨killCobsSow, rfl⟩

/-- The witch type is empty: no witch exists. -/
theorem isFalse_witchType : IsEmpty witchType.carrier :=
  show IsEmpty Empty from inferInstance

/-- The two contents are intensionally distinct (their event components
differ), even though both are empty. -/
theorem hobContent_ne_nobContent : ¬ hobContent.intEq nobContent :=
  λ h => absurd (congrArg IType.name (h : hobContent = nobContent)) (by decide)

/-- The contents are extensionally equivalent (both carriers are empty) yet
intensionally distinct — extensional equivalence does not entail
intensional identity. An extensional semantics (`Set W`-style
contents) identifies the two attitudes; TTR keeps them apart. -/
theorem extEquiv_not_intEq :
    hobContent.extEquiv nobContent ∧ ¬ hobContent.intEq nobContent :=
  ⟨⟨Equiv.refl _⟩, hobContent_ne_nobContent⟩

/-- Intentional identity, TTR-style: Hob's and Nob's contents share the witch
type as a common intensional component, are intensionally distinct contents,
and the shared type is empty — both attitudes are "about the same witch-type"
although no witch exists. -/
theorem intentional_identity :
    SharesComponent witchType hobContent ∧
    SharesComponent witchType nobContent ∧
    ¬ hobContent.intEq nobContent ∧
    IsEmpty witchType.carrier :=
  ⟨sharesComponent_hobContent, sharesComponent_nobContent,
   hobContent_ne_nobContent, isFalse_witchType⟩

end ChatzikyriakidisEtAl2025
