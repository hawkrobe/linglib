import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Syntax.Extraction

/-!
# Tseltal Agreement Fragment
[polian-2013] [aissen-polian-2025]

Agreement morphology for Tseltal (Tseltalan, Mayan). Tseltal and Tsotsil
are closely related languages within the Tseltalan subgroup of Western
Mayan. They share most syntactic properties relevant to possessor
extraction ([aissen-polian-2025]).

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
`Mayan.Tseltalan` for the shared definitions.

## Alignment

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per [polian-2013]).
Set A indicates A; Set B indicates S and P alike.
-/

namespace Tseltal

open Mayan (MarkerSet MarkerLinearity ExponentTable)
open Agreement

-- Re-export shared Tseltalan types
export Mayan.Tseltalan (GramFunction)

-- ============================================================================
-- § 1: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Tseltal clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Case assignment for Tseltal. Definitionally equal to
    `Mayan.caseTseltalan .Perf`, which derives from
    `Alignment.ergative.assignCase`. Tseltalan has no aspect-conditioned
    split, so a single case function suffices for both perfective and
    non-perfective. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.caseTseltalan .Perf

/-- Non-perfective case assignment for Tseltal. Identical to perfective
    (no aspect split per [polian-2013]). Provided for cross-Mayan
    shape-uniformity with the other Mayan fragments. -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.caseTseltalan .Imp

-- ============================================================================
-- § 2: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Tseltal's absolutive morphemes appear in low (post-stem) position,
    consistent with Tseltalan being LOW-ABS. -/
def absPosition : Mayan.ABSPosition := .low

-- ============================================================================
-- § 3: Agreement Marker Linearity
-- ============================================================================

/-- Set A markers in Tseltal are prefixal (per [aissen-polian-2025]
    Table 1; pan-Mayan invariant). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B markers in Tseltal are consistently suffixal. Contrasts with
    Tsotsil Set B, which is prefixal or suffixal depending on context
    ([aissen-polian-2025] Table 1, footnote 9). -/
def setBLinearity : MarkerLinearity := .suffixal

-- ============================================================================
-- § 4: Set A/B Exponents (Oxchuc Tseltal)
-- ============================================================================

/-- Set A (ERG/GEN) exponents for Oxchuc Tseltal ([polian-2013]).
    Prefixes on the verb or possessed noun. Forms shown as
    `pre-C/pre-V` allomorph pairs. -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "k-/j-"), (.pn .second .Sing, "a-/aw-"), (.pn .third .Sing, "s-/y-"),
   (.pn .first .Plur, "k-/j-"), (.pn .second .Plur, "a-/aw-"), (.pn .third .Plur, "s-/y-")]

/-- Set B (ABS) exponents for Oxchuc Tseltal ([polian-2013]).
    Suffixes on the verb stem. 3rd person singular is null (`-∅`). -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "-on"), (.pn .second .Sing, "-at"), (.pn .third .Sing, "-∅"),
   (.pn .first .Plur, "-otik"), (.pn .second .Plur, "-ex"), (.pn .third .Plur, "-ik")]

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches per [kaufman-norman-1984] Table 8. **Not**
    pan-Mayan: see Mam exception via `MayanLang.isStandard`. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some "-∅" := rfl

/-- Tseltal Set B differs from Tsotsil in linearity (suffixal vs
    prefixal-or-suffixal); the marker set assignment is identical. -/
theorem setB_is_suffixal : setBLinearity = .suffixal := rfl

-- ============================================================================
-- § 5: Extraction Profile
-- ============================================================================

/-- Tseltal's extraction data: no Agent Focus morphology required for
    A-extraction (`extractionStrategy = .unmarked`), consistent with
    Tseltal being LOW-ABS. -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .unmarked
def extractionMarkedPositions : List Extraction.ExtractionTarget := []
def extractionDistinguishesPosition : Bool := false

end Tseltal
