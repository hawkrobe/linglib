import Linglib.Typology.Complementation

/-!
# Phenomena.Complementation.Studies.Dryer2013
@cite{dryer-2013-wals} @cite{dryer-haspelmath-2013}

Cross-linguistic subordination analysis anchored on @cite{dryer-2013-wals}'s
WALS chapters on subordinator order (Ch 94) and OV-adposition correlation
(Ch 95), augmented with three further dimensions (complementizer position,
relative clause position, purpose clause strategy). The 20-language
`SubordinationProfile` sample is the testbed.

## Dryer's central observation

Subordination is one of the strongest head-direction correlations in
typology. VO languages cluster with initial subordinators, prepositions,
and post-nominal RCs; OV languages cluster with final subordinators,
postpositions, and pre-nominal RCs. Disharmonic patterns (Persian,
Hindi-Urdu, Mandarin) are typologically interesting exceptions.

## Contents

- §1. The 20-language `SubordinationProfile` sample.
- §2. Per-language verification (subordinator order, complementizer position,
  RC position, OV-adposition cross-checks).
- §3. Q1--Q12 typological generalizations: head-direction correlations,
  RC-OV correlation, complementizer-subordinator mirroring, areal patterns.
- §4. Areal/disharmonic-language theorems.

## Out of scope

The substrate types (`SubordinatorOrder`, `OVAdpositionType`, `RelativeClause
Position`, `SubordinationProfile`, etc.) and corpus-only WALS generalizations
live in `Linglib/Typology/Complementation.lean`. The 19-language Cristofaro
ComplementationProfile sample lives in `Studies/Cristofaro2013.lean`.
Noonan's CTP per-verb data lives in `Studies/Noonan2007.lean`.
-/

set_option autoImplicit false

namespace Phenomena.Complementation.Studies.Dryer2013

open Typology.Complementation

-- ============================================================================
-- §1. The 20-Language SubordinationProfile Sample
-- ============================================================================

/-- English: VO with initial subordinators/complementizers, post-nominal RCs,
    infinitive purpose. Prototypical head-initial. -/
def subEnglish : SubordinationProfile :=
  { language := "English"
  , iso := "eng"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "SVO"
  , notes := "Prototypical head-initial subordination" }

/-- Japanese: OV with final subordinators/complementizers, pre-nominal RCs,
    nominalized purpose. Prototypical head-final. -/
def subJapanese : SubordinationProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , subordinatorOrder := .finalWord
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Prototypical head-final subordination; no relative pronouns" }

/-- Turkish: OV with subordinator suffixes, no overt complementizer
    (nominalized complements), pre-nominal RCs, nominalized purpose. -/
def subTurkish : SubordinationProfile :=
  { language := "Turkish"
  , iso := "tur"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .none
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Suffixal subordination; no complementizer; nominalized complements" }

/-- Hindi-Urdu: OV with initial subordinators (disharmonic), correlative
    RCs (South Asian areal), infinitive purpose. -/
def subHindiUrdu : SubordinationProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , subordinatorOrder := .initialWord
  , ovAdposition := .ovPostp
  , compPosition := .initial
  , rcPosition := .correlative
  , purposeStrategy := .infinitive
  , basicOrder := "SOV"
  , notes := "OV + initial subordinator (disharmonic); correlative RCs (South Asian areal)" }

/-- Mandarin Chinese: SVO but pre-nominal RCs (mixed headedness), serial
    verb purpose. -/
def subMandarin : SubordinationProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .none
  , rcPosition := .preNominal
  , purposeStrategy := .serialVerb
  , basicOrder := "SVO"
  , notes := "Mixed headedness: VO but pre-nominal RC; serial verb purpose clauses" }

/-- Arabic (MSA): VSO with initial subordinators/complementizers, post-
    nominal RCs, subjunctive purpose. -/
def subArabic : SubordinationProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "VSO"
  , notes := "VSO with consistent head-initial subordination" }

/-- Korean: rigid OV like Japanese, suffixal subordination. -/
def subKorean : SubordinationProfile :=
  { language := "Korean"
  , iso := "kor"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Head-final like Japanese; suffixal subordination" }

/-- Irish: VSO with initial subordinators/complementizers, post-nominal RCs,
    subjunctive purpose. -/
def subIrish : SubordinationProfile :=
  { language := "Irish"
  , iso := "gle"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "VSO"
  , notes := "Celtic VSO; consistently head-initial" }

/-- Swahili: SVO with initial subordinators/complementizers, post-nominal
    RCs, subjunctive purpose. -/
def subSwahili : SubordinationProfile :=
  { language := "Swahili"
  , iso := "swh"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "SVO"
  , notes := "Bantu SVO; consistent head-initial subordination" }

/-- Persian: SOV with initial subordinators/complementizers (disharmonic
    for OV), post-nominal RCs (also disharmonic), infinitive purpose. -/
def subPersian : SubordinationProfile :=
  { language := "Persian"
  , iso := "fas"
  , subordinatorOrder := .initialWord
  , ovAdposition := .ovPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "SOV"
  , notes := "OV but head-initial subordination (disharmonic); Ch 95 OV+Prepositions" }

/-- German: V2 main / SOV embedded; mixed but initial subordinators. -/
def subGerman : SubordinationProfile :=
  { language := "German"
  , iso := "deu"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "V2/SOV"
  , notes := "V2 main clause; initial complementizer despite SOV embedded clauses" }

/-- Russian: SVO with initial subordinators/complementizers, post-nominal
    RCs, infinitive purpose. -/
def subRussian : SubordinationProfile :=
  { language := "Russian"
  , iso := "rus"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "SVO"
  , notes := "SVO with consistent head-initial subordination" }

/-- Quechua: rigid SOV with subordinator suffixes, no comp, pre-nominal
    RCs, nominalized purpose. -/
def subQuechua : SubordinationProfile :=
  { language := "Quechua"
  , iso := "que"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .none
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Consistently head-final; suffixal subordination like Turkish" }

/-- Yoruba: SVO with initial subordinators, post-nominal RCs, serial verb
    purpose (West African areal). -/
def subYoruba : SubordinationProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .serialVerb
  , basicOrder := "SVO"
  , notes := "SVO with serial verb purpose clauses (West African areal)" }

/-- Tagalog: V-initial Austronesian, linker `na` for complementation/RCs. -/
def subTagalog : SubordinationProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "VSO"
  , notes := "V-initial Austronesian; linker 'na' for complementation and RCs" }

/-- Basque: SOV isolate with final subordinator suffixes, no overt
    complementizer, pre-nominal RCs, nominalized purpose. -/
def subBasque : SubordinationProfile :=
  { language := "Basque"
  , iso := "eus"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Language isolate; head-final subordination with suffixal markers" }

/-- Navajo: SOV (Na-Dene) with internally headed RCs. -/
def subNavajo : SubordinationProfile :=
  { language := "Navajo"
  , iso := "nav"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .none
  , rcPosition := .internallyHeaded
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Na-Dene; internally headed RCs attested; heavily suffixal" }

/-- Bambara: SOV (Mande) with canonical internally headed RCs. -/
def subBambara : SubordinationProfile :=
  { language := "Bambara"
  , iso := "bam"
  , subordinatorOrder := .initialWord
  , ovAdposition := .ovPostp
  , compPosition := .initial
  , rcPosition := .internallyHeaded
  , purposeStrategy := .serialVerb
  , basicOrder := "SOV"
  , notes := "Mande language; canonical internally headed RCs" }

/-- Amharic: SOV (Semitic) with final subordinators/complementizers but
    pre-nominal RCs, subjunctive purpose. -/
def subAmharic : SubordinationProfile :=
  { language := "Amharic"
  , iso := "amh"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "SOV"
  , notes := "Semitic SOV; head-final subordination" }

/-- Malagasy: VOS Austronesian, head-initial subordination. -/
def subMalagasy : SubordinationProfile :=
  { language := "Malagasy"
  , iso := "mlg"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "VOS"
  , notes := "VOS Austronesian; head-initial subordination" }

/-- The 20-language sample. -/
def allSubProfiles : List SubordinationProfile :=
  [ subEnglish, subJapanese, subTurkish, subHindiUrdu, subMandarin
  , subArabic, subKorean, subIrish, subSwahili, subPersian
  , subGerman, subRussian, subQuechua, subYoruba, subTagalog
  , subBasque, subNavajo, subBambara, subAmharic, subMalagasy ]

theorem sub_sample_size : allSubProfiles.length = 20 := by native_decide

/-- Count of profiles matching a predicate. -/
def countSubProfiles (pred : SubordinationProfile → Bool) : Nat :=
  (allSubProfiles.filter pred).length

-- ============================================================================
-- §2. Q1: Initial subordinators correlate with VO order
-- ============================================================================

/-- All VO languages in the sample have initial subordinators. -/
theorem vo_implies_initial_subordinator :
    let voLangs := allSubProfiles.filter (·.isVO)
    voLangs.all (·.hasInitialSubordinator) = true := by native_decide

/-- All sample languages with final subordinators are OV. -/
theorem final_sub_implies_ov :
    let finalSubLangs := allSubProfiles.filter (·.hasFinalSubordinator)
    finalSubLangs.all (·.isOV) = true := by native_decide

-- ============================================================================
-- §3. Q2--Q3: Relative clause distribution
-- ============================================================================

/-- Post-nominal RCs are the most common type in the sample. -/
theorem postnominal_rc_majority :
    countSubProfiles (·.hasPostNominalRC) >
    countSubProfiles (·.hasPreNominalRC) := by native_decide

theorem postnominal_rc_count :
    countSubProfiles (·.hasPostNominalRC) = 10 := by native_decide

theorem prenominal_rc_count :
    countSubProfiles (·.hasPreNominalRC) = 7 := by native_decide

/-- Pre-nominal RC languages are overwhelmingly OV (Mandarin is the
    famous head-mixed exception). -/
theorem prenominal_rc_mostly_ov :
    let preNomOV := (allSubProfiles.filter
      (λ p => p.hasPreNominalRC && p.isOV)).length
    let preNomVO := (allSubProfiles.filter
      (λ p => p.hasPreNominalRC && p.isVO)).length
    preNomOV > preNomVO * 5 := by native_decide

-- ============================================================================
-- §4. Q4: Complementizer position mirrors subordinator position
-- ============================================================================

/-- No language in the sample has initial subordinator + final complementizer. -/
theorem no_initial_sub_final_comp :
    let conflicts := allSubProfiles.filter
      (λ p => p.hasInitialSubordinator && p.compPosition == .final)
    conflicts.length = 0 := by native_decide

/-- No language in the sample has final subordinator + initial complementizer. -/
theorem no_final_sub_initial_comp :
    let conflicts := allSubProfiles.filter
      (λ p => p.hasFinalSubordinator && p.compPosition == .initial)
    conflicts.length = 0 := by native_decide

-- ============================================================================
-- §5. Q5: SOV languages overwhelmingly use postpositions
-- ============================================================================

/-- In the sample, OV languages with postpositions outnumber OV languages
    with prepositions by at least 5x. -/
theorem sample_ov_mostly_postpositions :
    let ovPostp := (allSubProfiles.filter
      (λ p => p.ovAdposition == .ovPostp)).length
    let ovPrep := (allSubProfiles.filter
      (λ p => p.ovAdposition == .ovPrep)).length
    ovPostp > ovPrep * 5 := by native_decide

-- ============================================================================
-- §6. Q6: Purpose clause strategy correlates with finiteness
-- ============================================================================

/-- All nominalization-purpose languages in the sample are OV. -/
theorem nominalization_purpose_implies_ov :
    let nomPurp := allSubProfiles.filter
      (λ p => p.purposeStrategy == .nominalization)
    nomPurp.all (·.isOV) = true := by native_decide

/-- Serial verb purpose clauses appear in both VO and OV languages. -/
theorem serial_verb_purpose_mixed :
    let svPurp := allSubProfiles.filter
      (λ p => p.purposeStrategy == .serialVerb)
    (svPurp.any (·.isVO)) && (svPurp.any (·.isOV)) = true := by native_decide

-- ============================================================================
-- §7. Q7: Head-direction consistency across constructions
-- ============================================================================

/-- "Consistently head-initial": initial sub + initial comp + post-nominal
    RC + VO. -/
def isConsistentlyHeadInitial (p : SubordinationProfile) : Bool :=
  p.hasInitialSubordinator && p.compPosition == .initial &&
  p.hasPostNominalRC && p.isVO

/-- "Consistently head-final": final sub + (final comp or none) +
    pre-nominal RC + OV. -/
def isConsistentlyHeadFinal (p : SubordinationProfile) : Bool :=
  p.hasFinalSubordinator &&
  (p.compPosition == .final || p.compPosition == .none) &&
  p.hasPreNominalRC && p.isOV

/-- Most sample languages are consistently head-initial or head-final. -/
theorem consistency_dominant :
    let consistent := countSubProfiles isConsistentlyHeadInitial +
                      countSubProfiles isConsistentlyHeadFinal
    consistent > allSubProfiles.length / 2 := by native_decide

theorem head_initial_count :
    countSubProfiles isConsistentlyHeadInitial = 9 := by native_decide

theorem head_final_count :
    countSubProfiles isConsistentlyHeadFinal = 6 := by native_decide

-- ============================================================================
-- §8. Q8: Disharmonic languages
-- ============================================================================

/-- Persian: OV with prepositions (Ch 95 type), initial complementizer,
    post-nominal RC. -/
theorem persian_disharmonic :
    subPersian.ovAdposition == .ovPrep ∧
    subPersian.compPosition == .initial ∧
    subPersian.rcPosition == .postNominal := by native_decide

theorem hindi_disharmonic :
    subHindiUrdu.isOV ∧ subHindiUrdu.hasInitialSubordinator := by native_decide

theorem mandarin_disharmonic :
    subMandarin.isVO ∧ subMandarin.hasPreNominalRC := by native_decide

-- ============================================================================
-- §9. Q9--Q10: Areal RC patterns
-- ============================================================================

/-- Correlative RCs are an areal feature; only Hindi-Urdu in the sample. -/
theorem correlative_rc_rare :
    (allSubProfiles.filter (·.rcPosition == .correlative)).length = 1 := by
  native_decide

theorem correlative_is_hindi :
    (allSubProfiles.filter (·.rcPosition == .correlative)).all
      (·.language == "Hindi-Urdu") = true := by native_decide

/-- Internally headed RCs are typologically rare; Navajo and Bambara in the
    sample. -/
theorem internal_rc_rare :
    (allSubProfiles.filter (·.rcPosition == .internallyHeaded)).length = 2 := by
  native_decide

-- ============================================================================
-- §10. Q12: Subordinator suffixes restricted to OV languages
-- ============================================================================

/-- All sample languages with subordinator suffixes are OV. Suffixal
    subordination requires the subordinated verb to be identifiable by
    position, which OV order provides. -/
theorem sub_suffix_implies_ov :
    let suffixLangs := allSubProfiles.filter
      (λ p => p.subordinatorOrder == .finalSuffix)
    suffixLangs.all (·.isOV) = true := by native_decide

end Phenomena.Complementation.Studies.Dryer2013
