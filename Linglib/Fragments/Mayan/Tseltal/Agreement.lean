import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Morphology.Realization
import Linglib.Syntax.Extraction

/-!
# Tseltal Agreement Fragment

Agreement morphology for Tseltal (Tseltalan, Mayan). Tseltal and Tsotsil are
closely related within the Tseltalan subgroup of Western Mayan, sharing most
syntactic properties relevant to possessor extraction ([aissen-polian-2025];
[polian-2013]).

## Main declarations

* `Tseltal.ArgPosition` with `.case`, `.accCase`: argument positions and
  their case (ergative-absolutive, no aspect split).
* `Tseltal.setALinearity`, `Tseltal.setBLinearity`: prefixal Set A,
  consistently suffixal Set B.
* `Tseltal.setAExponent`, `Tseltal.setBExponent`: Oxchuc Tseltal exponent
  tables ([polian-2013]).
* `Tseltal.Extraction.realize`: unmarked extraction (no Agent Focus).

## Implementation notes

Tseltal has the same two agreement paradigms as Tsotsil: Set A (ERG/GEN)
prefixes cross-reference the transitive agent and possessor; Set B (ABS)
markers, consistently suffixal in Tseltal, cross-reference the absolutive
argument (intransitive subject and transitive patient). The key difference
from Tsotsil is Set B position — consistently suffixal in Tseltal, prefixal
or suffixal by context in Tsotsil. 3rd person singular Set B has no overt
exponent (∅). Grammatical-function classification is shared across Tseltalan
(`Mayan.Tseltalan`).

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per [polian-2013]): Set A
indicates A, Set B indicates S and P alike.
-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy)

namespace Tseltal

open Mayan (MarkerSet MarkerLinearity ExponentTable)
open Agreement

-- Re-export shared Tseltalan types
export Mayan.Tseltalan (GramFunction)

/-! ### Argument positions -/

/-- Argument positions in a Tseltal clause, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Case assignment for Tseltal: `Mayan.caseTseltalan .Perf`
    (A → ERG, S/P → ABS). No aspect-conditioned split, so a single function
    covers perfective and non-perfective. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.caseTseltalan .Perf

/-- Non-perfective case assignment for Tseltal: identical to perfective
    (no aspect split, [polian-2013]); provided for cross-Mayan
    shape-uniformity. -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.caseTseltalan .Imp

/-! ### Absolutive position (LOW-ABS) -/

/-- Tseltal's absolutive morphemes appear in low (post-stem) position,
    consistent with Tseltalan being LOW-ABS. -/
def absPosition : Mayan.ABSPosition := .low

/-! ### Agreement marker linearity -/

/-- Set A markers in Tseltal are prefixal (per [aissen-polian-2025]
    Table 1; pan-Mayan invariant). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B markers in Tseltal are consistently suffixal, contrasting with
    Tsotsil (prefixal or suffixal by context; [aissen-polian-2025] Table 1,
    footnote 9). -/
def setBLinearity : MarkerLinearity := .suffixal

/-! ### Set A/B exponents (Oxchuc Tseltal) -/

/-- Set A (ERG/GEN) exponents for Oxchuc Tseltal ([polian-2013]): prefixes
    on the verb or possessed noun, shown as `pre-C/pre-V` allomorph pairs. -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "k-/j-"), (.pn .second .Sing, "a-/aw-"), (.pn .third .Sing, "s-/y-"),
   (.pn .first .Plur, "k-/j-"), (.pn .second .Plur, "a-/aw-"), (.pn .third .Plur, "s-/y-")]

/-- Set B (ABS) exponents for Oxchuc Tseltal ([polian-2013]): suffixes on
    the verb stem; 3rd person singular is null (`-∅`). -/
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

/-! ### Extraction marking -/

namespace Extraction

/-- No Agent Focus morphology is required for A-extraction, consistent
    with Tseltal being LOW-ABS. -/
def realize : ExtractionTarget → List (Morphology.Reflex Empty) :=
  fun _ => []

/-- WALS-style label: extraction is unmarked. -/
def strategy : ExtractionMarkingStrategy := .unmarked

end Extraction

end Tseltal
