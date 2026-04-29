import Linglib.Datasets.WALS.Features.F81A
import Linglib.Datasets.WALS.Features.F82A
import Linglib.Datasets.WALS.Features.F83A
import Linglib.Datasets.WALS.Features.F87A
import Linglib.Datasets.WALS.Features.F88A
import Linglib.Datasets.WALS.Features.F90A
import Linglib.Datasets.WALS.Features.F94A
import Linglib.Datasets.WALS.Features.F95A
import Linglib.Datasets.WALS.Features.F96A
import Linglib.Datasets.WALS.Features.F97A
import Linglib.Datasets.WALS.Features.F81B
import Linglib.Datasets.WALS.Features.F90B
import Linglib.Datasets.WALS.Features.F90C
import Linglib.Datasets.WALS.Features.F60A
import Linglib.Datasets.WALS.Features.F61A

/-!
# Dryer & Haspelmath (eds., 2013): WALS aggregate generalizations
@cite{dryer-haspelmath-2013} @cite{dryer-1992}

Aggregate cross-linguistic generalizations derived directly from the WALS
Online corpus (@cite{dryer-haspelmath-2013}). Each theorem here is a
distributional fact about WALS chapter values: a count or comparative-count
predicate over `Datasets.WALS.Features.F{N}A.allData`.

These are not Greenberg-1963 implicational universals (which are conditional,
per-language statements; see `Studies/Greenberg1963.lean`). They are
unconditional aggregate claims about how WALS values distribute, of the form
"value X is more common than value Y in chapter N".

The chapter authorship within WALS Online is per-chapter (typically Dryer for
Ch 81–88, 95–96; Hammarström for Ch 97; etc.); the entire atlas is
@cite{dryer-haspelmath-2013}. @cite{dryer-1992} is the canonical earlier
synthesis of many of these correlations, predating WALS.

## What this file proves

§1. Basic constituent order (Ch 81–83): SOV-most-common, SOV+SVO majority,
    OV-dominant in Ch 83, subject-first vs verb-first dominance, object-
    initial rarity, SV vs VS dominance.

§2. Per-WALS-chapter generalizations (Ch 87, 88, 90, 94, 95, 96, 97, 81B,
    90B, 90C, 60, 61): per-chapter dominant-value claims. Several link to
    Gibson 2025's single-word-exception argument (Ch 87/88/97 all involve
    single-word dependents where head direction is less predictive).
-/

namespace Phenomena.WordOrder.Studies.DryerHaspelmath2013

private abbrev ch81  := Datasets.WALS.F81A.allData
private abbrev ch82  := Datasets.WALS.F82A.allData
private abbrev ch83  := Datasets.WALS.F83A.allData
private abbrev ch87  := Datasets.WALS.F87A.allData
private abbrev ch88  := Datasets.WALS.F88A.allData
private abbrev ch90  := Datasets.WALS.F90A.allData
private abbrev ch94  := Datasets.WALS.F94A.allData
private abbrev ch95  := Datasets.WALS.F95A.allData
private abbrev ch96  := Datasets.WALS.F96A.allData
private abbrev ch97  := Datasets.WALS.F97A.allData
private abbrev ch81B := Datasets.WALS.F81B.allData
private abbrev ch90B := Datasets.WALS.F90B.allData
private abbrev ch90C := Datasets.WALS.F90C.allData
private abbrev ch60  := Datasets.WALS.F60A.allData
private abbrev ch61  := Datasets.WALS.F61A.allData

-- ============================================================================
-- §1. Basic constituent order (Ch 81–83)
-- ============================================================================

set_option maxRecDepth 8192 in
/-- Ch 81: SOV is the most common basic order. -/
theorem sov_most_common :
    (ch81.filter (·.value == .sov)).length >
    (ch81.filter (·.value == .svo)).length := by decide

set_option maxRecDepth 8192 in
/-- Ch 81: SOV + SVO together exceed 75% of all sampled languages. -/
theorem sov_svo_majority_overall :
    let sov := (ch81.filter (·.value == .sov)).length
    let svo := (ch81.filter (·.value == .svo)).length
    (sov + svo) * 4 > ch81.length * 3 := by decide

set_option maxRecDepth 8192 in
/-- Ch 83: OV slightly outnumbers VO. -/
theorem ov_dominant_ch83 :
    (ch83.filter (·.value == .ov)).length >
    (ch83.filter (·.value == .vo)).length := by decide

set_option maxRecDepth 8192 in
/-- Ch 81: subject-first orders (SOV + SVO) far outnumber verb-first orders
    (VSO + VOS). -/
theorem subject_first_dominant :
    let sf := (ch81.filter (·.value == .sov)).length +
              (ch81.filter (·.value == .svo)).length
    let vf := (ch81.filter (·.value == .vso)).length +
              (ch81.filter (·.value == .vos)).length
    sf > vf * 8 := by decide

set_option maxRecDepth 8192 in
/-- Ch 81: object-initial orders (OVS + OSV) are extremely rare — less than
    2% of the sample. -/
theorem object_initial_rare :
    let oi := (ch81.filter (·.value == .ovs)).length +
              (ch81.filter (·.value == .osv)).length
    oi * 100 < ch81.length * 2 := by decide

set_option maxRecDepth 8192 in
/-- Ch 82: SV overwhelmingly dominates VS. SV languages outnumber VS
    languages by more than 5 to 1. -/
theorem sv_dominant :
    (ch82.filter (·.value == .sv)).length >
    (ch82.filter (·.value == .vs)).length * 5 := by decide

-- ============================================================================
-- §2. Per-chapter generalizations
-- ============================================================================

set_option maxRecDepth 8192 in
/-- Ch 87: N-Adj order dominates cross-linguistically (one of Gibson's
    single-word exceptions: adjectives are typically leaves). -/
theorem nounAdj_dominant_ch87 :
    (ch87.filter (·.value == .nounAdjective)).length >
    (ch87.filter (·.value == .adjectiveNoun)).length * 2 := by decide

set_option maxRecDepth 8192 in
/-- Ch 88: Dem-N vs N-Dem is roughly balanced (another single-word exception:
    demonstratives are single words, so head direction is less predictive). -/
theorem demN_roughly_balanced_ch88 :
    let demN := (ch88.filter (·.value == .demonstrativeNoun)).length
    let nDem := (ch88.filter (·.value == .nounDemonstrative)).length
    demN * 10 > nDem * 9 := by decide

set_option maxRecDepth 8192 in
/-- Ch 90: N-RelCl strongly dominates (relative clauses are recursive
    phrases, not single words — head direction matters). -/
theorem nounRelCl_dominant_ch90 :
    (ch90.filter (·.value == .nounRelativeClause)).length >
    (ch90.filter (·.value == .relativeClauseNoun)).length * 4 := by decide

set_option maxRecDepth 8192 in
/-- Ch 94: Initial subordinator words are the most common strategy for
    adverbial subordination. -/
theorem initial_subordinator_dominant_ch94 :
    (ch94.filter (·.value == .initialSubordinatorWord)).length >
    (ch94.filter (·.value == .finalSubordinatorWord)).length * 4 := by decide

set_option maxRecDepth 8192 in
/-- Ch 95: Harmonic pairs (OV+Postp, VO+Prep) vastly outnumber disharmonic
    (OV+Prep, VO+Postp). -/
theorem ch95_harmonic_dominant :
    let harmonic := (ch95.filter (·.value == .ovAndPostpositions)).length +
                    (ch95.filter (·.value == .voAndPrepositions)).length
    let disharmonic := (ch95.filter (·.value == .ovAndPrepositions)).length +
                       (ch95.filter (·.value == .voAndPostpositions)).length
    harmonic > disharmonic * 16 := by decide

set_option maxRecDepth 8192 in
/-- Ch 96: VO+NRel strongly dominates VO+RelN (relative clauses are
    recursive, so head direction matters). OV languages are more mixed due
    to the N-RelCl strategy. -/
theorem ch96_voNRel_dominant :
    (ch96.filter (·.value == .voAndNrel)).length >
    (ch96.filter (·.value == .voAndReln)).length * 80 := by decide

set_option maxRecDepth 8192 in
/-- Ch 97: OV languages split between AdjN and NAdj (weak correlation,
    single-word exception). This contrasts with Ch 95 where OV+Prep is
    nearly absent. -/
theorem ch97_ov_split :
    let ovAdjN := (ch97.filter (·.value == .ovAndAdjn)).length
    let ovNAdj := (ch97.filter (·.value == .ovAndNadj)).length
    ovNAdj > ovAdjN := by decide

set_option maxRecDepth 8192 in
/-- Ch 81B: SOV-or-SVO is the most common dual-order pattern, consistent
    with the general dominance of subject-first orders. -/
theorem ch81B_sovOrSvo_most_common :
    (ch81B.filter (·.value == .sovOrSvo)).length >
    (ch81B.filter (·.value == .vsoOrVos)).length := by decide

set_option maxRecDepth 4096 in
/-- Ch 90B: Dominant-only prenominal (RelN) is the majority among languages
    with this strategy. -/
theorem ch90B_dominant_relN_majority :
    (ch90B.filter (·.value == .relativeClauseNounDominant)).length >
    ch90B.length / 2 := by decide

set_option maxRecDepth 4096 in
/-- Ch 90C: Dominant-only postnominal (NRel) is overwhelmingly the majority
    among languages with this strategy. -/
theorem ch90C_dominant_nRel_majority :
    (ch90C.filter (·.value == .nounRelativeClauseDominant)).length >
    ch90C.length * 9 / 10 := by decide

set_option maxRecDepth 4096 in
/-- Ch 60: "Highly differentiated" between genitives, adjectives, and
    relative clauses is the majority value. -/
theorem ch60_highlyDifferentiated_majority :
    (ch60.filter (·.value == .highlyDifferentiated)).length >
    ch60.length / 2 := by decide

set_option maxRecDepth 4096 in
/-- Ch 61: "Without marking" is the majority strategy for headless adjective
    phrases. -/
theorem ch61_withoutMarking_majority :
    (ch61.filter (·.value == .withoutMarking)).length >
    ch61.length / 2 := by decide

end Phenomena.WordOrder.Studies.DryerHaspelmath2013
