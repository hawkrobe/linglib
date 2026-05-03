import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Theories.Interfaces.Morphosyntax.Extraction

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

## Alignment

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per @cite{polian-2013}).
-/

namespace Fragments.Mayan.Tsotsil

open Fragments.Mayan (MarkerSet PersonNumber MarkerLinearity)

-- Re-export shared Tseltalan types
export Fragments.Mayan.Tseltalan (GramFunction)

-- ============================================================================
-- § 1: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Tsotsil clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Case assignment for Tsotsil. Definitionally equal to
    `Fragments.Mayan.caseTseltalan .Perf`, which derives from
    `Alignment.ergative.assignCase`. Tseltalan has no aspect-conditioned
    split. -/
abbrev ArgPosition.case : ArgPosition → Core.Case :=
  Fragments.Mayan.caseTseltalan .Perf

/-- Non-perfective case assignment for Tsotsil. Identical to perfective
    (no aspect split per @cite{polian-2013}). -/
abbrev ArgPosition.accCase : ArgPosition → Core.Case :=
  Fragments.Mayan.caseTseltalan .Imp

-- ============================================================================
-- § 2: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Tsotsil's absolutive morphemes appear in low (post-stem) position
    when suffixal, consistent with Tseltalan being LOW-ABS. The
    prefixal-or-suffixal alternation is conditioned by morphosyntactic
    context (see `setBLinearity`); the LOW-ABS classification refers to
    the structural position of the licensing head, not the linear
    position of every Set B exponent. -/
def absPosition : Fragments.Mayan.ABSPosition := .low

-- ============================================================================
-- § 3: Agreement Marker Linearity
-- ============================================================================

/-- Set A markers in Tsotsil are prefixal (per @cite{aissen-polian-2025}
    Table 1; pan-Mayan invariant). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B markers in Tsotsil are prefixal or suffixal, depending on
    dialect and morphosyntactic context (@cite{aissen-polian-2025}
    Table 1). The Tsotsil-vs-Tseltal contrast in Set B linearity is the
    headline Tseltalan-internal divergence. -/
def setBLinearity : MarkerLinearity := .either

-- ============================================================================
-- § 4: Set A/B Exponents (Zinacantec Tsotsil)
-- ============================================================================

/-- Set A (ERG/GEN) exponents for Zinacantec Tsotsil
    (@cite{polian-2013}). Prefixes on the verb (for ERG) or the possessed
    noun (for GEN). Forms vary by following segment; shown as
    `pre-C/pre-V` allomorph pairs. -/
def setAExponent : PersonNumber → String
  | .p1sg => "k-/j-"
  | .p2sg => "a-/av-"
  | .p3sg => "s-/y-"
  | .p1pl => "k-/j-"
  | .p2pl => "a-/av-"
  | .p3pl => "s-/y-"

/-- Set B (ABS) exponents for Zinacantec Tsotsil (@cite{polian-2013}).
    3rd person singular has no overt exponent (`-∅`). Some forms show
    allomorphic alternation depending on suffix harmony. -/
def setBExponent : PersonNumber → String
  | .p1sg => "-on/-un"
  | .p2sg => "-ot/-at"
  | .p3sg => "-∅"
  | .p1pl => "-otik/-utik"
  | .p2pl => "-oxuk"
  | .p3pl => "-ik"

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches per @cite{kaufman-norman-1984} Table 8. **Not**
    pan-Mayan: see Mam exception via `MayanLang.isStandard`. -/
theorem p3sg_abs_null : setBExponent .p3sg = "-∅" := rfl

-- ============================================================================
-- § 5: Extraction Profile
-- ============================================================================

/-- Tsotsil's extraction profile: no Agent Focus morphology required for
    A-extraction, consistent with Tsotsil being LOW-ABS. -/
def extractionProfile : Interfaces.ExtractionProfile :=
  { language := "Tsotsil"
  , strategy := .none
  , markedPositions := []
  , distinguishesPosition := false
  , notes := "LOW-ABS Tseltalan; no AF morphology" }

end Fragments.Mayan.Tsotsil
