import Linglib.Fragments.Mayan.Tseltalan

/-!
# Tseltal Agreement Fragment
@cite{polian-2013} @cite{aissen-polian-2025}

Agreement morphology for Tseltal (Tseltalan, Mayan). Tseltal and Tsotsil
are closely related languages within the Tseltalan subgroup of Western
Mayan. They share most syntactic properties relevant to possessor
extraction (@cite{aissen-polian-2025}).

## The System

Tseltal has the same two agreement paradigms as Tsotsil:
- **Set A** (ERG/GEN): prefixes cross-referencing transitive agent and possessor.
- **Set B** (ABS): consistently suffixal in Tseltal, cross-referencing the
  absolutive argument (intransitive subject and transitive patient).

The key difference from Tsotsil is Set B position: Tseltal Set B markers
are consistently suffixal, whereas Tsotsil Set B markers can be prefixal
or suffixal depending on context.

3rd person singular Set B has no overt exponent (∅).

Grammatical function classification is shared across Tseltalan — see
`Fragments.Mayan.Tseltalan` for the shared definitions.
-/

namespace Fragments.Mayan.Tseltal

open Fragments.Mayan (MarkerSet)

-- Re-export shared Tseltalan types
export Fragments.Mayan.Tseltalan (GramFunction)

-- ============================================================================
-- § 1: Agreement Marker Position
-- ============================================================================

/-- Set A markers in Tseltal are prefixal. -/
def setAPosition : String := "prefixal"

/-- Set B markers in Tseltal are consistently suffixal. -/
def setBPosition : String := "suffixal"

-- ============================================================================
-- § 2: Set A/B Exponents (Oxchuc Tseltal)
-- ============================================================================

/-- Person-number values for Tseltal agreement. -/
inductive PersonNumber where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, Repr

/-- Set A (ERG/GEN) exponents for Oxchuc Tseltal.
    Prefixes on the verb or possessed noun. -/
def setAExponent : PersonNumber → String
  | .p1sg => "k-/j-"
  | .p2sg => "a-/aw-"
  | .p3sg => "s-/y-"
  | .p1pl => "k-/j-"
  | .p2pl => "a-/aw-"
  | .p3pl => "s-/y-"

/-- Set B (ABS) exponents for Oxchuc Tseltal.
    Suffixes on the verb stem. 3rd person singular is ∅. -/
def setBExponent : PersonNumber → String
  | .p1sg => "-on"
  | .p2sg => "-at"
  | .p3sg => "∅"
  | .p1pl => "-otik"
  | .p2pl => "-ex"
  | .p3pl => "-ik"

/-- Tseltal Set B differs from Tsotsil in position (suffixal vs
    prefixal/suffixal), though the marker set assignment is identical. -/
theorem setB_is_suffixal : setBPosition = "suffixal" := rfl

end Fragments.Mayan.Tseltal
