import Mathlib.Data.Set.Basic
import Linglib.Semantics.Degree.Gradability.Classification

/-!
# Modification-time coercion (NVP + HPP)

`LicensedCoercion` and `ParteeReanalysis`: type-level architecture for
noun-extension shifts under the Non-Vacuity Principle and Head Primacy
Principle of [kamp-partee-1995]. Consumed by
`Studies/Partee2010.lean`.

## Main definitions

* `NonVacuous P w d`: NVP at world `w` within local domain `d`.
* `LicensedCoercion N adj w`: NVP-licensed widening of `N`.
* `ParteeReanalysis adj_classical`: reanalysis as subsective-after-coercion.

## References

* [kamp-partee-1995] formulae 18 (NVP), 20 (HPP), p. 161.
* [partee-2010] § 4.
-/

namespace Semantics.Composition.Coercion

open Degree.Classification

variable {W E : Type*}

/-- Both positive and negative extensions of `P` at `w` intersect `d`. -/
def NonVacuous (P : Property W E) (w : W) (d : Set E) : Prop :=
  ({x | P w x} ∩ d).Nonempty ∧ ({x | ¬ P w x} ∩ d).Nonempty

/-- A wider noun extension `shift ⊇ N` at `w` under which `adj shift`
    is non-vacuous in `shift`'s extension (the HPP local domain). -/
structure LicensedCoercion (N : Property W E) (adj : AdjMeaning W E) (w : W) where
  shift : Property W E
  shift_supseteq : {x | N w x} ⊆ {x | shift w x}
  satisfies_nvp : NonVacuous (adj shift) w {x | shift w x}

/-- Reanalysis of `adj_classical` as subsective-after-coercion. The
    coercion is NVP-conditional: `shift_inert` requires `noun_shift N =
    N` whenever direct application is already non-vacuous, so the
    structure does not coerce gratuitously. -/
structure ParteeReanalysis (adj_classical : AdjMeaning W E) where
  noun_shift : Property W E → Property W E
  adj_subsective : AdjMeaning W E
  shift_supseteq : ∀ (N : Property W E) (w : W),
    {x | N w x} ⊆ {x | noun_shift N w x}
  is_subsective : isSubsective adj_subsective
  shift_inert : ∀ (N : Property W E) (w : W),
    NonVacuous (adj_classical N) w {x | N w x} → noun_shift N = N

end Semantics.Composition.Coercion
