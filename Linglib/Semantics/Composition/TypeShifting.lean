import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Definiteness.Maximality

/-!
# Type-shifting between the noun-phrase types

The three noun-phrase denotation types of [partee-1987], entities `E`, predicates `E → Prop`
and quantifiers `Quantifier E`, and the shifts between them. The total shifts are the Montague
lift `Quantification.individual`, the singleton property `ident`, existential closure
`Quantification.A` and predicative content `Quantification.BE`; the partial ones are the
Russellian `Definiteness.russellIota`, its lift `THE`, and `lower`, defined on the principal
ultrafilters. This file proves the two commuting faces of Partee's triangle, `BE ∘ individual
= ident` and `A ∘ ident = individual`, and that each partial shift inverts its total one; the
uniqueness of `BE` as a Boolean homomorphism is in `Studies/Partee1987.lean`.

## Main definitions

* `ident j`: the singleton property `{j}`.
* `lower Q`: the entity whose Montague lift is `Q`, when there is one.
* `THE P`: the Montague lift of the unique `P`, when there is one, the presuppositional
  definite article.

## Main results

* `BE_individual_eq_ident`, `A_ident_eq_individual`: the faces of the triangle.
* `russellIota_ident`, `lower_individual`, `THE_ident`: each partial shift inverts its total
  one.

## Implementation notes

The setting is extensional, so [chierchia-1984]'s `pred` and `nom`, the correlates of entities
and properties, coincide with `ident` and `russellIota`; their intensional generalizations are
`Genericity.Kind.up` and `Genericity.Property.down`. The partial shifts are `Option`-valued,
`none` where the paper's operator is undefined. Existential closure `A` ranges over a listed
domain, so `A_ident_eq_individual` asks that the entity lie in it.

## References

* [partee-1987]
* [chierchia-1984]
-/

namespace Semantics.Composition.TypeShifting

open Quantification Definiteness

variable {E : Type*}

/-- The singleton property of an entity, `ident j = {j}`. -/
def ident (j : E) : E → Prop := (· = j)

theorem ident_injective : Function.Injective (ident (E := E)) := Set.singleton_injective

/-- `BE ∘ individual = ident`, the right face of the triangle. -/
theorem BE_individual_eq_ident (j : E) : BE (individual j) = ident j :=
  funext λ _ => propext eq_comm

/-- `A ∘ ident = individual` on the domain, the left face of the triangle. -/
theorem A_ident_eq_individual (domain : List E) (j : E) (hj : j ∈ domain) :
    A domain (ident j) = individual j := by
  funext P
  exact propext ⟨λ ⟨_, _, rfl, hP⟩ => hP, λ hP => ⟨j, hj, rfl, hP⟩⟩

/-! ### The partial shifts -/

/-- The entity whose Montague lift is `Q`, when `Q` is a principal ultrafilter. -/
noncomputable def lower (Q : Quantifier E) : Option E := russellIota λ j => Q = individual j

/-- The presuppositional definite article, the Montague lift of the unique `P`. -/
noncomputable def THE (P : E → Prop) : Option (Quantifier E) := (russellIota P).map individual

theorem russellIota_ident (j : E) : russellIota (ident j) = some j :=
  (russellIota_eq_some_iff _ _).2 ⟨rfl, λ _ h => h⟩

theorem lower_individual (j : E) : lower (individual j) = some j :=
  (russellIota_eq_some_iff _ _).2 ⟨rfl, λ _ h => (individual_injective h).symm⟩

theorem THE_ident (j : E) : THE (ident j) = some (individual j) := by
  rw [THE, russellIota_ident]; rfl

end Semantics.Composition.TypeShifting
