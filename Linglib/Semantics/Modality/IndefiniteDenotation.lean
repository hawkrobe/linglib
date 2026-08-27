import Linglib.Syntax.Category.Determiner.ModalIndefinite
import Linglib.Semantics.Presupposition.Defs

/-!
# Denotation of modal indefinites

This file defines the existential-with-modal-component denotation of a modal indefinite
anchored to a modal source: some member of the domain satisfies restrictor and scope, and
every restrictor member satisfies the scope in some world the source projects
([alonso-ovalle-menendez-benito-2018] for *uno cualquiera*, [alonso-ovalle-royer-2024] (59)
for *yalnhej*). The item's anchor constraint is the presupposition of its denotation and its
upper bound strengthens the assertion.

## Main definitions

* `modalIndefiniteSat`, `upperBoundedSat` — the modal component with and without an
  upper bound.
* `ModalIndefinite.denotation` — the item's `PartialProp`.

## References

* [alonso-ovalle-menendez-benito-2018]
* [alonso-ovalle-royer-2024]
-/

namespace Modality

open Modality.Kratzer Presupposition

variable {W E : Type*} (src : ModalSource W) (D : Finset E) (P Q : E → W → Prop) (w : W)

/-- Some member of `D` satisfies restrictor and scope, and every restrictor member satisfies
the scope in some world the source projects. -/
def modalIndefiniteSat : Prop :=
  (∃ x ∈ D, P x w ∧ Q x w) ∧ ∀ y ∈ D, P y w → simplePossibility src.background (Q y) w

/-- The upper-bounded component: not every restrictor member satisfies the scope. -/
def upperBoundedSat : Prop := modalIndefiniteSat src D P Q w ∧ ¬ ∀ x ∈ D, P x w → Q x w

theorem modalIndefiniteSat_of_upperBoundedSat (h : upperBoundedSat src D P Q w) :
    modalIndefiniteSat src D P Q w := h.1

/-- The denotation of a modal indefinite anchored to `src`: defined when the item's anchor
constraint admits the source, asserting the modal component with the item's upper bound. -/
def ModalIndefinite.denotation (mi : ModalIndefinite) : PartialProp W where
  presup _ := ∀ c ∈ mi.anchorConstraint, c.Admits src
  assertion w :=
    if mi.upperBounded then upperBoundedSat src D P Q w else modalIndefiniteSat src D P Q w

end Modality
