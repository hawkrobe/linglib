import Mathlib.Data.Set.Basic
import Linglib.Theories.Semantics.Gradability.Classification

/-!
# Modification-time coercion (NVP + HPP)
@cite{kamp-partee-1995} @cite{partee-2010}

Type-level architecture for noun coercion under modifier-head
composition. The Non-Vacuity Principle (NVP) and Head Primacy Principle
(HPP) of @cite{kamp-partee-1995} jointly license a shift of the head's
extension when direct interpretation of `adj N` would violate
non-vacuity within the head's local domain.

This file fixes the *types*: `NonVacuous`, `HPPDomain`, and the
`LicensedCoercion` structure of admissible shifts. The substantive
operational theorems — that every Kamp-privative adjective admits such
a coercion (@cite{partee-2010} §4) — live in the consuming study file
`Phenomena/Gradability/Studies/Partee2010.lean` and are currently open
(`sorry`-marked).

## Scope

NVP and HPP are general modification-time principles, not gradability-
specific. They live here, alongside `TypeShifting.lean` and
`Modification.lean`, rather than under `Gradability/`. Sutton2024's
`ComplementCoercion` class (currently inline in
`Phenomena/Polysemy/Studies/Sutton2024.lean`) covers a sibling
phenomenon (telic-quale coercion of complements) and would belong
here on a future consolidation pass; not in scope now.
-/

namespace Semantics.Composition.Coercion

open Semantics.Gradability.Classification

variable {W E : Type*}

/-- Non-Vacuity Principle (@cite{kamp-partee-1995}, formula 18, p. 161).
    A predicate `P` is non-vacuous at world `w` within local domain `d`
    iff both its positive and negative extensions intersect `d`. The
    paraphrase: "try to interpret any predicate so that both its
    positive and negative extension are non-empty." -/
def NonVacuous (P : Property W E) (w : W) (d : Set E) : Prop :=
  (∃ x ∈ d, P w x) ∧ (∃ x ∈ d, ¬ P w x)

/-- Head Primacy Principle (@cite{kamp-partee-1995}, formula 20, p. 161)
    — local domain. "In a modifier-head structure, the head is
    interpreted relative to the context of the whole constituent, and
    the modifier is interpreted relative to the local context created
    from the former context by the interpretation of the head."

    Operationally: the head's extension at `w` fixes the domain in
    which the modifier is interpreted. -/
def HPPDomain (N : Property W E) (w : W) : Set E := fun x => N w x

/-- A licensed coercion of noun `N` under adjective `adj` at world `w`:
    a wider extension `shift` of `N` under which `adj`'s interpretation
    satisfies NVP within the local HPP domain of `shift`.

    Per @cite{partee-2010} §4, NVP forces this shift exactly when
    direct interpretation of `adj N` would yield a vacuous predicate
    in the head's local domain — explaining why "fake gun" coerces
    "gun" to include fake guns, but "alleged president" cannot be
    rescued by N-coercion (its non-extensional modal contribution
    is orthogonal to `N`'s extension). -/
structure LicensedCoercion (N : Property W E) (adj : AdjMeaning W E) (w : W) where
  /-- The shifted (widened) noun extension. -/
  shift : Property W E
  /-- The shift extends, not replaces, the original noun. -/
  ext_of : ∀ x, N w x → shift w x
  /-- NVP is satisfied at the shifted extension. -/
  satisfies_nvp : NonVacuous (adj shift) w (HPPDomain shift w)

end Semantics.Composition.Coercion
