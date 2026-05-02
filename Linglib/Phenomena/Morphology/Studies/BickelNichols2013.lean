import Linglib.Core.Morphology.MorphProfile
import Linglib.Fragments.English.Morph
import Linglib.Fragments.Mandarin.Morph
import Linglib.Fragments.Japanese.Morph
import Linglib.Fragments.Turkish.Morph
import Linglib.Fragments.Finnish.Morph
import Linglib.Fragments.Slavic.Russian.Morph
import Linglib.Fragments.Swahili.Morph
import Linglib.Fragments.Arabic.Egyptian.Morph
import Linglib.Fragments.Hindi.Morph
import Linglib.Fragments.Tagalog.Morph
import Linglib.Fragments.Quechua.Morph
import Linglib.Fragments.Hungarian.Morph
import Linglib.Fragments.Georgian.Morph
import Linglib.Fragments.Thai.Morph
import Linglib.Fragments.Indonesian.Morph
import Linglib.Fragments.Korean.Morph
import Linglib.Fragments.German.Morph
import Linglib.Fragments.Spanish.Morph

/-!
# Phenomena.Morphology.Studies.BickelNichols2013
@cite{bickel-nichols-2013a} @cite{bickel-nichols-2013b} @cite{bickel-nichols-2013c}
@cite{bickel-nichols-2001}

Cross-linguistic analyses anchored on Bickel & Nichols's WALS chapters
(Ch 20 fusion, Ch 21 exponence, Ch 22 inflectional synthesis) and their
2001 paper on the orthogonality of fusion and flexivity. The 18-language
`MorphProfile` sample is the testbed.

## Bickel & Nichols's central insight

The traditional 1D typological scale `isolating > agglutinating > fusional
> polysynthetic` conflates two orthogonal parameters: **fusion** (whether
formatives are concatenative, nonlinear, or isolating) and **flexivity**
(whether classes are predictable from form vs. arbitrary). Both
"agglutinating" (`concatenative + nonflexive`) and "fusional"
(`concatenative + flexive`) are attested in the sample, demonstrating the
two parameters are independent.

## Contents

- §1. The 18-language `MorphProfile` sample (drawn from per-language
  Fragment profiles).
- §2. Substantive structural / orthogonality theorems on the B&N
  decomposition: both flexivity values attested under concatenative;
  every concatenative language is agglutinating ∨ fusional; nonlinear
  cell witnessed by Arabic; isolating cell has no flexivity.

## Out of scope

The substrate types (`MorphProfile`, `Fusion`, `Flexivity`, ...) and WALS
converters live in `Core/Morphology/MorphProfile.lean`. Per-language B&N
classification commitments (e.g., "German is fusional") live in each
`Fragments/{Lang}/Morph.lean` as local bridge theorems.
@cite{ackerman-malouf-2013}'s E-complexity / I-complexity analysis lives
in `Studies/AckermanMalouf2013.lean`.

This file deliberately omits aggregate-count theorems (`sample_X_count = N`)
— exact counts go stale every time a Fragment is added to the sample. The
mutual-exclusion theorem `MorphProfile.agglutinating_fusional_exclusive`
is structural and lives in `Core/Morphology/MorphProfile.lean §6`.
-/

set_option autoImplicit false

namespace Phenomena.Morphology.Studies.BickelNichols2013

open Core.Morphology

-- ============================================================================
-- §1. The 18-language MorphProfile Sample
-- ============================================================================

/-! Per-language Fragment profiles, with values derived from WALS data
    via `Core.Morphology.wals*` lookup helpers. Aliases here for concise
    reference in theorems below. -/

private abbrev englishMorph    := Fragments.English.morphProfile
private abbrev mandarinMorph   := Fragments.Mandarin.morphProfile
private abbrev japaneseMorph   := Fragments.Japanese.morphProfile
private abbrev turkishMorph    := Fragments.Turkish.morphProfile
private abbrev finnishMorph    := Fragments.Finnish.morphProfile
private abbrev russianMorph    := Fragments.Slavic.Russian.morphProfile
private abbrev swahiliMorph    := Fragments.Swahili.morphProfile
private abbrev arabicMorph     := Fragments.Arabic.Egyptian.morphProfile
private abbrev hindiMorph      := Fragments.Hindi.morphProfile
private abbrev tagalogMorph    := Fragments.Tagalog.morphProfile
private abbrev quechuaMorph    := Fragments.Quechua.morphProfile
private abbrev hungarianMorph  := Fragments.Hungarian.morphProfile
private abbrev georgianMorph   := Fragments.Georgian.morphProfile
private abbrev thaiMorph       := Fragments.Thai.morphProfile
private abbrev indonesianMorph := Fragments.Indonesian.morphProfile
private abbrev koreanMorph     := Fragments.Korean.morphProfile
private abbrev germanMorph     := Fragments.German.morphProfile
private abbrev spanishMorph    := Fragments.Spanish.morphProfile

/-- 18-language morphological sample. -/
def allMorphProfiles : List MorphProfile :=
  [ englishMorph, mandarinMorph, japaneseMorph, turkishMorph, finnishMorph
  , russianMorph, swahiliMorph, arabicMorph, hindiMorph, tagalogMorph
  , quechuaMorph, hungarianMorph, georgianMorph, thaiMorph, indonesianMorph
  , koreanMorph, germanMorph, spanishMorph ]

/-- Sentry: ISO codes are pairwise distinct across the sample. Catches
    accidental cross-language duplicates (two Fragments stipulating the
    same ISO) that per-Fragment sentries cannot see. -/
theorem morph_iso_unique :
    (allMorphProfiles.map (·.iso)).eraseDups.length = allMorphProfiles.length := by decide

-- ============================================================================
-- §2. B&N Orthogonality and Cell-Population Theorems
-- ============================================================================

/-! @cite{bickel-nichols-2001} argue fusion and flexivity are orthogonal,
    and that the four cells of the (concatenative ∪ nonlinear ∪ isolating)
    × (flexive ∪ nonflexive ∪ none) space are independently attested. The
    theorems below witness the cells the sample populates. -/

/-- Key orthogonality test: among concatenative languages, both flexive
    and nonflexive are attested. This refutes the traditional 1D scale's
    claim that fusion-axis values determine flexivity-axis values. -/
theorem concatenative_admits_both_flexivities :
    let concats := allMorphProfiles.filter (fun p => decide p.IsConcatenative)
    (concats.filter (fun p => decide p.IsFlexive)).length > 0 ∧
    (concats.filter (fun p => decide p.IsNonflexive)).length > 0 := by decide

/-- Nonlinear cell witnessed by Arabic root-and-pattern morphology. The
    sample's only nonlinear member is also flexive and cumulative — the
    classic templatic profile. -/
theorem arabic_nonlinear_flexive :
    arabicMorph.IsNonlinear ∧ arabicMorph.IsFlexive ∧ arabicMorph.IsCumulative := by
  decide

/-- Isolating cell (Mandarin, Thai) has no flexivity / no exponence
    marking — the B&N parameters do not apply to isolating typology. -/
theorem isolating_no_flexivity :
    mandarinMorph.flexivity = none ∧ thaiMorph.flexivity = none := by decide

/-- WALS Exponence (Ch 21A, case-specific) and B&N ExponenceScope (general)
    are independent: both poly+sep (Finnish, Tagalog) and mono+cum (Hindi,
    Georgian, Spanish) are attested in the sample. -/
theorem exponence_scope_independent :
    (allMorphProfiles.filter (fun p =>
      decide (p.exponence = .polyexponential ∧ p.bnExponence = some .separative))).length > 0 ∧
    (allMorphProfiles.filter (fun p =>
      decide (p.exponence = .monoexponential ∧ p.bnExponence = some .cumulative))).length > 0 := by
  decide

set_option maxRecDepth 2000 in
/-- B&N decomposition is exhaustive on the concatenative dimension: every
    concatenative language in the sample is either agglutinating
    (concatenative + nonflexive + separative) or fusional (concatenative +
    flexive + cumulative). -/
theorem concatenative_partition :
    ∀ p ∈ allMorphProfiles, p.IsConcatenative →
      p.IsAgglutinating ∨ p.IsFusional := by decide

/-- Sample partition: every language falls into exactly one of agglutinating
    / fusional / nonlinear / isolating. The disjointness half lives in
    `Core/Morphology/MorphProfile.lean §6` as a structural theorem
    (`MorphProfile.agglutinating_fusional_exclusive`); this is the empirical
    claim that the four cells exhaust the sample. -/
theorem sample_type_exhaustive :
    allMorphProfiles.length =
    (allMorphProfiles.filter (fun p => decide p.IsAgglutinating)).length +
    (allMorphProfiles.filter (fun p => decide p.IsFusional)).length +
    (allMorphProfiles.filter (fun p => decide p.IsNonlinear)).length +
    (allMorphProfiles.filter (fun p => decide p.IsIsolating)).length := by decide

end Phenomena.Morphology.Studies.BickelNichols2013
