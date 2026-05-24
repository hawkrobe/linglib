import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Typology.Extraction

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

## Alignment

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per @cite{polian-2013}).
Set A indicates A; Set B indicates S and P alike.
-/

namespace Fragments.Mayan.Tseltal

open Fragments.Mayan (MarkerSet PersonNumber MarkerLinearity)

-- Re-export shared Tseltalan types
export Fragments.Mayan.Tseltalan (GramFunction)

-- ============================================================================
-- § 1: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Tseltal clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Case assignment for Tseltal. Definitionally equal to
    `Fragments.Mayan.caseTseltalan .Perf`, which derives from
    `Alignment.ergative.assignCase`. Tseltalan has no aspect-conditioned
    split, so a single case function suffices for both perfective and
    non-perfective. -/
abbrev ArgPosition.case : ArgPosition → Features.Case :=
  Fragments.Mayan.caseTseltalan .Perf

/-- Non-perfective case assignment for Tseltal. Identical to perfective
    (no aspect split per @cite{polian-2013}). Provided for cross-Mayan
    shape-uniformity with the other Mayan fragments. -/
abbrev ArgPosition.accCase : ArgPosition → Features.Case :=
  Fragments.Mayan.caseTseltalan .Imp

-- ============================================================================
-- § 2: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Tseltal's absolutive morphemes appear in low (post-stem) position,
    consistent with Tseltalan being LOW-ABS. -/
def absPosition : Fragments.Mayan.ABSPosition := .low

-- ============================================================================
-- § 3: Agreement Marker Linearity
-- ============================================================================

/-- Set A markers in Tseltal are prefixal (per @cite{aissen-polian-2025}
    Table 1; pan-Mayan invariant). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B markers in Tseltal are consistently suffixal. Contrasts with
    Tsotsil Set B, which is prefixal or suffixal depending on context
    (@cite{aissen-polian-2025} Table 1, footnote 9). -/
def setBLinearity : MarkerLinearity := .suffixal

-- ============================================================================
-- § 4: Set A/B Exponents (Oxchuc Tseltal)
-- ============================================================================

/-- Set A (ERG/GEN) exponents for Oxchuc Tseltal (@cite{polian-2013}).
    Prefixes on the verb or possessed noun. Forms shown as
    `pre-C/pre-V` allomorph pairs. -/
def setAExponent : PersonNumber → String
  | .p1sg => "k-/j-"
  | .p2sg => "a-/aw-"
  | .p3sg => "s-/y-"
  | .p1pl => "k-/j-"
  | .p2pl => "a-/aw-"
  | .p3pl => "s-/y-"

/-- Set B (ABS) exponents for Oxchuc Tseltal (@cite{polian-2013}).
    Suffixes on the verb stem. 3rd person singular is null (`-∅`). -/
def setBExponent : PersonNumber → String
  | .p1sg => "-on"
  | .p2sg => "-at"
  | .p3sg => "-∅"
  | .p1pl => "-otik"
  | .p2pl => "-ex"
  | .p3pl => "-ik"

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches per @cite{kaufman-norman-1984} Table 8. **Not**
    pan-Mayan: see Mam exception via `MayanLang.isStandard`. -/
theorem p3sg_abs_null : setBExponent .p3sg = "-∅" := rfl

/-- Tseltal Set B differs from Tsotsil in linearity (suffixal vs
    prefixal-or-suffixal); the marker set assignment is identical. -/
theorem setB_is_suffixal : setBLinearity = .suffixal := rfl

-- ============================================================================
-- § 5: Extraction Profile
-- ============================================================================

/-- Tseltal's extraction profile: no Agent Focus morphology required for
    A-extraction, consistent with Tseltal being LOW-ABS. -/
def extractionProfile : Typology.ExtractionProfile :=
  { language := "Tseltal"
  , strategy := .unmarked
  , markedPositions := []
  , distinguishesPosition := false
  , notes := "LOW-ABS Tseltalan; no AF morphology" }

end Fragments.Mayan.Tseltal
