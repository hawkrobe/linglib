import Linglib.Fragments.Mayan.Tseltalan

/-!
# Tsotsil Agreement Fragment
@cite{polian-2013} @cite{aissen-polian-2025}

Agreement morphology for Zinacantec Tsotsil (Tseltalan, Mayan).

## The System

Tsotsil has two agreement paradigms on the verb:
- **Set A** (ERG/GEN): prefixes cross-referencing the transitive agent
  (ergative) and the possessor (genitive). Ergative and genitive are
  homophonous (@cite{polian-2013}).
- **Set B** (ABS): prefixes or suffixes cross-referencing the absolutive
  argument (intransitive subject and transitive patient). Position varies
  by dialect and morphosyntactic context; in Zinacantec Tsotsil, Set B
  markers occur either prefixally or suffixally.

Canonical word order is VOA (verb-initial), though both arguments are
usually unpronounced unless topicalized or focused.

3rd person singular Set B has no overt exponent (∅).

Grammatical function classification is shared across Tseltalan — see
`Fragments.Mayan.Tseltalan` for the shared definitions.
-/

namespace Fragments.Mayan.Tsotsil

open Fragments.Mayan (MarkerSet)

-- Re-export shared Tseltalan types
export Fragments.Mayan.Tseltalan (GramFunction)

-- ============================================================================
-- § 1: Agreement Marker Position
-- ============================================================================

/-- Set A markers in Tsotsil are prefixal. -/
def setAPosition : String := "prefixal"

/-- Set B markers in Tsotsil are prefixal or suffixal, depending on
    dialect and morphosyntactic context. -/
def setBPosition : String := "prefixal/suffixal"

-- ============================================================================
-- § 2: Set A/B Exponents (Zinacantec Tsotsil)
-- ============================================================================

/-- Person-number values for Tsotsil agreement. -/
inductive PersonNumber where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, Repr

/-- Set A (ERG/GEN) exponents for Zinacantec Tsotsil.
    These are prefixes on the verb (for ERG) or the possessed noun (for GEN).
    Forms vary by following segment; simplified here. -/
def setAExponent : PersonNumber → String
  | .p1sg => "k-/j-"
  | .p2sg => "a-/av-"
  | .p3sg => "s-/y-"
  | .p1pl => "k-/j-"
  | .p2pl => "a-/av-"
  | .p3pl => "s-/y-"

/-- Set B (ABS) exponents for Zinacantec Tsotsil.
    3rd person singular has no overt exponent. -/
def setBExponent : PersonNumber → String
  | .p1sg => "-on/-un"
  | .p2sg => "-ot/-at"
  | .p3sg => "∅"
  | .p1pl => "-otik/-utik"
  | .p2pl => "-oxuk"
  | .p3pl => "-ik"

end Fragments.Mayan.Tsotsil
