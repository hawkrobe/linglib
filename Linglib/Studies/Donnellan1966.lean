/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Reference.Character
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Definiteness.Maximality

/-!
# Donnellan (1966): Reference and Definite Descriptions

This file formalizes the two uses of a definite description in [donnellan-1966]. Used
attributively, *the φ* denotes at each world whoever uniquely satisfies φ there, the Russellian
iota taken pointwise (`attributive`, `attributive_eq_some_iff`), and as a nominal denotation
its only presupposition is that the iota is defined (`attributiveNominal`,
`attributiveNominal_assertion`). Used referentially, it denotes the individual the speaker has
in mind whatever the world: the constant character (`Character.const`), whose content is rigid.
The two uses come apart in Donnellan's scene of the man with the martini: when the intended
referent fails the description at a world where someone else uniquely satisfies it, the
attributive use denotes that other individual and the referential use the intended one
(`attributive_ne_const_of_misfit`).

## Implementation notes

Whether the referential use is semantic or pragmatic, the dispute with [kripke-1977], is not
decided here: the file gives Donnellan's truth conditions for each use.

## References

* [donnellan-1966]
* [kripke-1977]
* [russell-1905]
-/

namespace Donnellan1966

open Reference Definiteness

variable {W E : Type*} {domain : List E} {φ : E → W → Prop} [∀ e w, Decidable (φ e w)]
  {w : W} {e intended : E}

/-- The attributive use: at each world, the unique satisfier of the description there. -/
def attributive (domain : List E) (φ : E → W → Prop) [∀ e w, Decidable (φ e w)] :
    W → Option E :=
  λ w => russellIotaList domain λ e => decide (φ e w)

theorem attributive_eq_some_iff :
    attributive domain φ w = some e ↔ domain.filter (λ e => decide (φ e w)) = [e] :=
  russellIotaList_eq_some_iff ..

/-- The attributive use as a nominal denotation: the selector is the pointwise iota and there
is no presupposition beyond its definedness. -/
def attributiveNominal (domain : List E) (φ : E → W → Prop) [∀ e w, Decidable (φ e w)] :
    NominalDenot Unit W E :=
  .ofReferent (attributive domain φ)

/-- Where the description picks out `e`, the attributive use of *the φ is ψ* asserts `ψ e`. -/
theorem attributiveNominal_assertion (ψ : E → W → Prop) (h : attributive domain φ w = some e) :
    ((attributiveNominal domain φ).resolve ψ ()).assertion w ↔ ψ e w := by
  simp [attributiveNominal, NominalDenot.resolve, NominalDenot.ofReferent,
    Presupposition.PartialProp.presupOfReferent, h]

/-- Donnellan's scene: the description uniquely fits `e` at `w` while the speaker intends
someone else, so the attributive use denotes `e` and the referential use, the constant
character at the intended referent, does not. -/
theorem attributive_ne_const_of_misfit (h : attributive domain φ w = some e)
    (hne : e ≠ intended) :
    attributive domain φ w ≠ some (Character.const intended () w) := by
  simpa [h] using hne

end Donnellan1966
