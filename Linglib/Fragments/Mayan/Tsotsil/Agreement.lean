import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Syntax.Extraction

/-!
# Tsotsil Agreement Fragment
[polian-2013] [aissen-polian-2025]

Agreement morphology for Zinacantec Tsotsil (Tseltalan, Mayan).

## The System

Tsotsil has two agreement paradigms on the verb:
- **Set A** (ERG/GEN): prefixes cross-referencing the transitive agent
  (ergative) and the possessor (genitive). Ergative and genitive are
  homophonous ([polian-2013]).
- **Set B** (ABS): prefixes or suffixes cross-referencing the absolutive
  argument (intransitive subject and transitive patient). Position varies
  by dialect and morphosyntactic context; in Zinacantec Tsotsil, Set B
  markers occur either prefixally or suffixally.

Canonical word order is VOA (verb-initial), though both arguments are
usually unpronounced unless topicalized or focused.

3rd person singular Set B has no overt exponent (∅).

Grammatical function classification is shared across Tseltalan — see
`Mayan.Tseltalan` for the shared definitions.

## Alignment

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per [polian-2013]).
-/

namespace Tsotsil

open Mayan (MarkerSet MarkerLinearity ExponentTable)
open Agreement

-- Re-export shared Tseltalan types
export Mayan.Tseltalan (GramFunction)

-- ============================================================================
-- § 1: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Tsotsil clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Case assignment for Tsotsil. Definitionally equal to
    `Mayan.caseTseltalan .Perf`, which derives from
    `Alignment.ergative.assignCase`. Tseltalan has no aspect-conditioned
    split. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.caseTseltalan .Perf

/-- Non-perfective case assignment for Tsotsil. Identical to perfective
    (no aspect split per [polian-2013]). -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.caseTseltalan .Imp

-- ============================================================================
-- § 2: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Tsotsil's absolutive morphemes appear in low (post-stem) position
    when suffixal, consistent with Tseltalan being LOW-ABS. The
    prefixal-or-suffixal alternation is conditioned by morphosyntactic
    context (see `setBLinearity`); the LOW-ABS classification refers to
    the structural position of the licensing head, not the linear
    position of every Set B exponent. -/
def absPosition : Mayan.ABSPosition := .low

-- ============================================================================
-- § 3: Agreement Marker Linearity
-- ============================================================================

/-- Set A markers in Tsotsil are prefixal (per [aissen-polian-2025]
    Table 1; pan-Mayan invariant). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B markers in Tsotsil are prefixal or suffixal, depending on
    dialect and morphosyntactic context ([aissen-polian-2025]
    Table 1). The Tsotsil-vs-Tseltal contrast in Set B linearity is the
    headline Tseltalan-internal divergence. -/
def setBLinearity : MarkerLinearity := .either

-- ============================================================================
-- § 4: Set A/B Exponents (Zinacantec Tsotsil)
-- ============================================================================

/-- Set A (ERG/GEN) exponents for Zinacantec Tsotsil
    ([polian-2013]). Prefixes on the verb (for ERG) or the possessed
    noun (for GEN). Forms vary by following segment; shown as
    `pre-C/pre-V` allomorph pairs. -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "k-/j-"), (.pn .second .Sing, "a-/av-"), (.pn .third .Sing, "s-/y-"),
   (.pn .first .Plur, "k-/j-"), (.pn .second .Plur, "a-/av-"), (.pn .third .Plur, "s-/y-")]

/-- Set B (ABS) exponents for Zinacantec Tsotsil ([polian-2013]).
    3rd person singular has no overt exponent (`-∅`). Some forms show
    allomorphic alternation depending on suffix harmony. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "-on/-un"), (.pn .second .Sing, "-ot/-at"), (.pn .third .Sing, "-∅"),
   (.pn .first .Plur, "-otik/-utik"), (.pn .second .Plur, "-oxuk"), (.pn .third .Plur, "-ik")]

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches per [kaufman-norman-1984] Table 8. **Not**
    pan-Mayan: see Mam exception via `MayanLang.isStandard`. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some "-∅" := rfl

-- ============================================================================
-- § 5: Extraction Profile
-- ============================================================================

/-- Tsotsil's extraction profile (language "Tsotsil"): no Agent Focus
    morphology required for A-extraction, consistent with Tsotsil being
    LOW-ABS. Notes: LOW-ABS Tseltalan; no AF morphology. -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .unmarked
def extractionMarkedPositions : List Extraction.ExtractionTarget := []
def extractionDistinguishesPosition : Bool := false

end Tsotsil
