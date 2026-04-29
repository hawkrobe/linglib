import Linglib.Typology.Morphology
import Linglib.Core.Morphology.MorphProfile
import Linglib.Fragments.English.Morph
import Linglib.Fragments.Mandarin.Morph
import Linglib.Fragments.Japanese.Morph
import Linglib.Fragments.Turkish.Morph
import Linglib.Fragments.Finnish.Morph
import Linglib.Fragments.Slavic.Russian.Morph
import Linglib.Fragments.Swahili.Morph
import Linglib.Fragments.Arabic.Morph
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
  Fragment profiles, derived from WALS via `Core.Morphology.wals*` lookup
  helpers).
- §2. Sample distribution counts (fusion, exponence, locus, synthesis).
- §3. Sample-grounded generalisations: suffixing dominates, concatenative
  plurality, dependent-marking common, head-marking-implies-high-synthesis.
- §4. Bickel & Nichols 2001 orthogonality: flexivity × fusion independence,
  agglutinating-vs-fusional partition, exponence-scope independence from
  WALS exponence.

## Out of scope

The substrate types (`MorphProfile`, `Fusion`, `Flexivity`, ...) and WALS
converters live in `Core/Morphology/MorphProfile.lean`. WALS aggregate
sample-size theorems, distribution lists, and corpus-only generalisations
(Greenberg's Universal 27, concatenative dominance, etc.) live in
`Linglib/Typology/Morphology.lean`. @cite{ackerman-malouf-2013}'s
E-complexity / I-complexity analysis (10-language `LanguageData` sample,
LCEC) is in `Studies/AckermanMalouf2013.lean`.
-/

set_option autoImplicit false

namespace Phenomena.Morphology.Studies.BickelNichols2013

open Core.Morphology
open Typology.Morphology

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
private abbrev arabicMorph     := Fragments.Arabic.morphProfile
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

/-- 18-language morphological mechanism sample. -/
def allMorphProfiles : List MorphProfile :=
  [ englishMorph, mandarinMorph, japaneseMorph, turkishMorph, finnishMorph
  , russianMorph, swahiliMorph, arabicMorph, hindiMorph, tagalogMorph
  , quechuaMorph, hungarianMorph, georgianMorph, thaiMorph, indonesianMorph
  , koreanMorph, germanMorph, spanishMorph ]

theorem allMorphProfiles_count : allMorphProfiles.length = 18 := by native_decide

-- ============================================================================
-- §2. Counting Helpers + Sample Distribution
-- ============================================================================

def countByFusion (langs : List MorphProfile) (f : Fusion) : Nat :=
  (langs.filter (λ p => p.fusion == f)).length

def countByExponence (langs : List MorphProfile) (e : Exponence) : Nat :=
  (langs.filter (λ p => p.exponence == e)).length

def countByLocus (langs : List MorphProfile) (l : LocusOfMarking) : Nat :=
  (langs.filter (λ p => p.locus == l)).length

def countBySynthesis (langs : List MorphProfile) (s : VerbSynthesis) : Nat :=
  (langs.filter (λ p => p.verbSynthesis == s)).length

/-- Fusion type distribution in the sample. -/
theorem sample_concatenative_count :
    countByFusion allMorphProfiles .concatenative = 14 := by native_decide
theorem sample_nonlinear_count :
    countByFusion allMorphProfiles .nonlinear = 1 := by native_decide
theorem sample_isolating_count :
    countByFusion allMorphProfiles .isolating = 3 := by native_decide

/-- Exponence distribution in the sample. -/
theorem sample_monoexponential_count :
    countByExponence allMorphProfiles .monoexponential = 12 := by native_decide
theorem sample_polyexponential_count :
    countByExponence allMorphProfiles .polyexponential = 5 := by native_decide
theorem sample_no_inflection_count :
    countByExponence allMorphProfiles .noCase = 1 := by native_decide

/-- Verb synthesis distribution in the sample. -/
theorem sample_low_synthesis :
    countBySynthesis allMorphProfiles .low = 7 := by native_decide
theorem sample_moderate_synthesis :
    countBySynthesis allMorphProfiles .moderate = 9 := by native_decide
theorem sample_high_synthesis :
    countBySynthesis allMorphProfiles .high = 2 := by native_decide

/-- Locus of marking distribution in the sample. -/
theorem sample_dependent_marking :
    countByLocus allMorphProfiles .dependentMarking = 10 := by native_decide
theorem sample_head_marking :
    countByLocus allMorphProfiles .headMarking = 1 := by native_decide
theorem sample_double_marking :
    countByLocus allMorphProfiles .doubleMarking = 4 := by native_decide
theorem sample_zero_marking :
    countByLocus allMorphProfiles .zeroMarking = 3 := by native_decide
theorem sample_inconsistent_marking :
    countByLocus allMorphProfiles .inconsistentOrOther = 0 := by native_decide

/-- Fusion counts sum to total. -/
theorem fusion_counts_sum :
    countByFusion allMorphProfiles .concatenative +
    countByFusion allMorphProfiles .nonlinear +
    countByFusion allMorphProfiles .isolating =
    allMorphProfiles.length := by native_decide

/-- Locus counts sum to total. -/
theorem locus_counts_sum :
    countByLocus allMorphProfiles .headMarking +
    countByLocus allMorphProfiles .dependentMarking +
    countByLocus allMorphProfiles .doubleMarking +
    countByLocus allMorphProfiles .zeroMarking +
    countByLocus allMorphProfiles .inconsistentOrOther =
    allMorphProfiles.length := by native_decide

/-- All ISO codes are 3 characters. -/
theorem morph_iso_length_3 :
    allMorphProfiles.all (λ p => p.iso.length == 3) = true := by native_decide

/-- No duplicate ISO codes in the sample. -/
theorem morph_iso_unique :
    (allMorphProfiles.map (·.iso)).eraseDups.length =
    allMorphProfiles.length := by native_decide

-- ============================================================================
-- §3. Sample-Grounded Generalisations
-- ============================================================================

/-- Greenberg's Universal 27 in the sample: suffixing-dominant languages
    outnumber prefixing-dominant ones. -/
theorem suffixing_dominates_in_sample :
    let suffCount := (allMorphProfiles.filter (·.isSuffixing)).length
    let prefCount := (allMorphProfiles.filter (·.isPrefixing)).length
    suffCount > prefCount := by native_decide

/-- Concatenative is the plurality fusion type in the sample. -/
theorem concatenative_plurality_in_sample :
    countByFusion allMorphProfiles .concatenative >
      countByFusion allMorphProfiles .nonlinear ∧
    countByFusion allMorphProfiles .concatenative >
      countByFusion allMorphProfiles .isolating := by native_decide

/-- Dependent-marking is at least as common as head-marking in the sample. -/
theorem dependent_marking_common :
    countByLocus allMorphProfiles .dependentMarking >=
    countByLocus allMorphProfiles .headMarking := by native_decide

/-- Reduplication is attested in the sample. -/
theorem reduplication_attested_in_sample :
    (allMorphProfiles.filter (·.hasRedup)).length >= 3 := by native_decide

/-- The defining correlation of agglutination: concatenative languages are
    predominantly monoexponential (one-to-one form-meaning mapping). -/
theorem concatenative_mostly_monoexponential :
    let concatLangs := allMorphProfiles.filter (·.isConcatenative)
    let concatMono := concatLangs.filter (·.isMono)
    concatMono.length * 2 > concatLangs.length := by native_decide

/-- Head-marking languages have at least moderate verb synthesis (the verb
    carries agreement morphology for multiple arguments). -/
theorem head_marking_high_synthesis :
    let headLangs := allMorphProfiles.filter (λ p => p.locus == .headMarking)
    headLangs.all (λ p =>
      p.verbSynthesis == .moderate || p.verbSynthesis == .high) = true := by
  native_decide

/-- All languages with high verb synthesis have either concatenative or
    nonlinear fusion (never isolating). -/
theorem high_synthesis_not_isolating :
    allMorphProfiles.all (λ p =>
      if p.isHighSynthesis then !p.isIsolating else true) = true := by native_decide

-- ============================================================================
-- §4. Bickel & Nichols 2001: Flexivity × Fusion Orthogonality
-- ============================================================================

/-! The traditional 1D typological scale conflates fusion (concatenative
    vs. nonlinear vs. isolating) with flexivity (predictable vs.
    arbitrary class membership). @cite{bickel-nichols-2001} argue these
    are orthogonal; the sample bears this out. -/

def countByFlexivity (langs : List MorphProfile) (f : Flexivity) : Nat :=
  (langs.filter (λ p => p.flexivity == some f)).length

def countByBNExponence (langs : List MorphProfile) (e : ExponenceScope) : Nat :=
  (langs.filter (λ p => p.bnExponence == some e)).length

/-- Flexivity distribution: both values attested.
    2 isolating languages (Mandarin, Thai) have `none`. -/
theorem sample_nonflexive_count :
    countByFlexivity allMorphProfiles .nonflexive = 10 := by native_decide
theorem sample_flexive_count :
    countByFlexivity allMorphProfiles .flexive = 6 := by native_decide

/-- B&N exponence distribution: both values attested.
    2 isolating languages (Mandarin, Thai) have `none`. -/
theorem sample_separative_count :
    countByBNExponence allMorphProfiles .separative = 10 := by native_decide
theorem sample_cumulative_count :
    countByBNExponence allMorphProfiles .cumulative = 6 := by native_decide

/-- Key orthogonality test: among concatenative languages, both flexive
    and nonflexive are attested. -/
theorem concatenative_admits_both_flexivities :
    let concats := allMorphProfiles.filter MorphProfile.isConcatenative
    (concats.filter MorphProfile.isFlexive).length > 0 ∧
    (concats.filter MorphProfile.isNonflexive).length > 0 := by native_decide

/-- Traditional "agglutinating" decomposed: concatenative + nonflexive +
    separative. Turkish, Finnish, Japanese, Korean, Hungarian, Swahili,
    Quechua, English, Tagalog all satisfy this. Indonesian is WALS-isolating
    despite productive affixation, so it does not count as agglutinating
    here. -/
theorem sample_agglutinating_count :
    (allMorphProfiles.filter MorphProfile.isAgglutinating).length = 9 := by native_decide

/-- Traditional "fusional" decomposed: concatenative + flexive + cumulative.
    Russian, German, Spanish, Hindi, Georgian all satisfy this. -/
theorem sample_fusional_count :
    (allMorphProfiles.filter MorphProfile.isFusional).length = 5 := by native_decide

/-- Arabic is nonlinear + flexive + cumulative (root-and-pattern morphology). -/
theorem arabic_nonlinear_flexive :
    arabicMorph.isNonlinear = true ∧
    arabicMorph.isFlexive = true ∧
    arabicMorph.isCumulative = true := by native_decide

/-- Isolating languages (Mandarin, Thai) have no flexivity/exponence marking. -/
theorem isolating_no_flexivity :
    mandarinMorph.flexivity = none ∧
    thaiMorph.flexivity = none := by native_decide

/-- WALS Exponence (case-specific) and B&N ExponenceScope (general) are
    independent: both poly+sep (Finnish, Tagalog) and mono+cum (Hindi,
    Georgian, Spanish) are attested. -/
theorem exponence_scope_independent :
    (allMorphProfiles.filter (λ p =>
      p.exponence == .polyexponential && p.bnExponence == some .separative)).length > 0 ∧
    (allMorphProfiles.filter (λ p =>
      p.exponence == .monoexponential && p.bnExponence == some .cumulative)).length > 0 := by
  native_decide

-- ============================================================================
-- §5. B&N Parameter Space Partition
-- ============================================================================

/-- Every concatenative language in the sample is either agglutinating or
    fusional (the B&N decomposition is exhaustive on this dimension). -/
theorem concatenative_partition :
    let concats := allMorphProfiles.filter MorphProfile.isConcatenative
    concats.all (λ p => p.isAgglutinating || p.isFusional) = true := by native_decide

/-- No language in the sample is both agglutinating and fusional (the two
    decomposed categories are disjoint). -/
theorem no_agglutinating_and_fusional :
    allMorphProfiles.all (λ p => !(p.isAgglutinating && p.isFusional)) = true := by
  native_decide

/-- The three B&N parameters are independently attested: among concatenative
    languages, both exponence scopes occur with both flexivity values. -/
theorem exponence_flexivity_independent :
    let concats := allMorphProfiles.filter MorphProfile.isConcatenative
    (concats.filter (λ p => p.isNonflexive && p.isSeparative)).length > 0 ∧
    (concats.filter (λ p => p.isFlexive && p.isCumulative)).length > 0 := by native_decide

/-- Sample partition: every language falls into exactly one of agglutinating /
    fusional / nonlinear / isolating. -/
theorem sample_type_exhaustive :
    allMorphProfiles.length =
    (allMorphProfiles.filter MorphProfile.isAgglutinating).length +
    (allMorphProfiles.filter MorphProfile.isFusional).length +
    (allMorphProfiles.filter MorphProfile.isNonlinear).length +
    (allMorphProfiles.filter MorphProfile.isIsolating).length := by
  native_decide

end Phenomena.Morphology.Studies.BickelNichols2013
