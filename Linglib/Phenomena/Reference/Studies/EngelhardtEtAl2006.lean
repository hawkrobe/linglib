import Linglib.Theories.Pragmatics.GriceanMaxims
import Linglib.Phenomena.Reference.Studies.SedivyEtAl1999
import Linglib.Phenomena.Reference.Studies.DaleReiter1995

/-!
# @cite{engelhardt-etal-2006}
@cite{sedivy-etal-1999} @cite{grice-1975} @cite{dale-reiter-1995}

Do Speakers and Listeners Observe the Gricean Maxim of Quantity?
*Journal of Memory and Language* 54(4), 554–573.

## Core Argument

Three experiments test whether speakers and listeners follow the Gricean
Maxim of Quantity — the requirement that contributions be as informative
as required but not more informative than required.

- **Exp 1** (production, N = 24): Speakers over-describe ~31% of the
  time, using unnecessary modifiers (color adjectives, relative clauses,
  prepositional phrases) when a bare NP suffices.
- **Exp 2** (judgment, N = 72): Listeners rate over-descriptions no
  worse than concise descriptions, but rate under-descriptions
  significantly worse.
- **Exp 3** (eye-tracking, N = 48): Over-descriptions cause implicit
  processing costs — longer first-pass reading times on the head noun
  and more regressions back to the unnecessary modifier.

Conclusion: the language processing system is "only moderately Gricean."
Speakers routinely violate the "not more informative" half of Quantity,
listeners are explicitly tolerant of these violations but implicitly
sensitive to them.

## Connection to Contrastive Inference

The eye-tracking processing cost for unnecessary modifiers is the
complement of @cite{sedivy-etal-1999}'s contrastive inference benefit
from necessary modifiers. Both effects confirm that the comprehension
system is sensitive to modifier presence and its pragmatic licensing.

## Verified Data

Eye-tracking F-statistics and reading times verified against running
text (§4). Judgment t-test significance levels verified against running
text (§3). Production proportions and judgment mean ratings read from
Tables 1–2 (not restated in running text).
-/

namespace EngelhardtEtAl2006

-- ============================================================================
-- § Experiment 1: Production (§2, N = 24)
-- ============================================================================

/-- Over-description and modification rates from Exp 1 (Table 1).
    In 1-referent displays, speakers used modified NPs 31% of the time
    when a bare NP would have been sufficient. -/
structure ProductionRate where
  /-- Proportion of modified NP productions -/
  modified : Float
  /-- Standard error -/
  se : Float
  deriving Repr

/-- 1-referent target: 31% over-description (Table 1). -/
def exp1_target_1ref : ProductionRate := { modified := 0.31, se := 0.05 }

/-- 2-referent target: 90% modification — necessary (Table 1). -/
def exp1_target_2ref : ProductionRate := { modified := 0.90, se := 0.04 }

/-- No-competitor goal: 19% over-description (Table 1). -/
def exp1_goal_noCompetitor : ProductionRate := { modified := 0.19, se := 0.05 }

/-- Competitor goal: 92% modification — necessary (Table 1). -/
def exp1_goal_competitor : ProductionRate := { modified := 0.92, se := 0.03 }

-- ============================================================================
-- § Experiment 2: Judgment (§3, N = 72)
-- ============================================================================

/-- Judgment result: between-subjects t-test comparing two instruction
    types. Rating scale 1–5 (1 = "very bad", 5 = "very good").
    The three participant groups each saw a different instruction version,
    so comparisons use independent-sample t-tests. -/
structure JudgmentResult where
  /-- Mean rating for concise instruction -/
  conciseRating : Float
  /-- Mean rating for alternative instruction (over-described or modified) -/
  altRating : Float
  /-- Degrees of freedom -/
  df : Nat
  /-- t-statistic; `none` when paper reports "< 1" -/
  tStat : Option Float
  /-- Significant at p < .05 -/
  significant : Bool
  deriving Repr

/-- 1-referent target: over-description NOT rated worse than concise.
    Concise 3.93 vs over-described 3.89, t₁(46) < 1 (§3). -/
def exp2_target_1ref : JudgmentResult :=
  { conciseRating := 3.93, altRating := 3.89, df := 46
  , tStat := none, significant := false }

/-- 2-referent target: under-description rated significantly worse.
    Concise (= under-described) 3.31 vs modified 3.88,
    t₁(46) = 3.69, p < .001 (§3). -/
def exp2_target_2ref : JudgmentResult :=
  { conciseRating := 3.31, altRating := 3.88, df := 46
  , tStat := some 3.69, significant := true }

/-- No-competitor goal: over-description NOT rated worse.
    Concise 3.56 vs over-described 3.59, t₁(46) < 1 (§3). -/
def exp2_goal_noCompetitor : JudgmentResult :=
  { conciseRating := 3.56, altRating := 3.59, df := 46
  , tStat := none, significant := false }

/-- Competitor goal: under-description rated significantly worse.
    Concise (= under-described) 3.36 vs modified 3.69,
    t₁(46) = 2.01, p < .05 (§3). -/
def exp2_goal_competitor : JudgmentResult :=
  { conciseRating := 3.36, altRating := 3.69, df := 46
  , tStat := some 2.01, significant := true }

-- ============================================================================
-- § Experiment 3: Eye-Tracking (§4, N = 48)
-- ============================================================================

/-- Reuse ANOVA result structure from @cite{sedivy-etal-1999}. Both
    studies use by-subjects (F₁) and by-items (F₂) ANOVAs on
    eye-tracking data. -/
abbrev AnovaResult := SedivyEtAl1999.AnovaResult

/-- Eye-tracking reading measure with mean values and ANOVA. -/
structure ReadingMeasure where
  /-- Mean for modified (over-described) condition -/
  modified : Float
  /-- Mean for bare (concise) condition -/
  bare : Float
  /-- ANOVA result -/
  anova : AnovaResult
  deriving Repr

/-- Head noun first-pass reading time: modified 531ms vs bare 489ms.
    Listeners spend significantly longer reading the head noun after
    an unnecessary modifier. F₁(1,47) = 9.31, p < .01;
    F₂(1,23) = 7.32, p < .05 (§4, non-matching condition). -/
def exp3_headNoun_firstPass : ReadingMeasure :=
  { modified := 531, bare := 489
  , anova := { F1 := 9.31, df1 := 47, F2 := 7.32, df2 := 23
             , significant := true } }

/-- Post-noun regressions back to adjective: modified 14.6% vs bare 7.3%.
    Listeners regress to re-read the unnecessary modifier significantly
    more often. F₁(1,47) = 17.74, p < .001; F₂(1,23) = 14.15, p < .001
    (§4, non-matching condition). -/
def exp3_postNoun_regressions : ReadingMeasure :=
  { modified := 14.6, bare := 7.3
  , anova := { F1 := 17.74, df1 := 47, F2 := 14.15, df2 := 23
             , significant := true } }

/-- Head noun first-fixation duration: marginal by subjects, significant
    by items. F₁(1,47) = 3.19, p < .08; F₂(1,23) = 5.12, p < .05
    (§4, non-matching condition). -/
def exp3_headNoun_firstFixation : AnovaResult :=
  { F1 := 3.19, df1 := 47, F2 := 5.12, df2 := 23, significant := false }

-- ============================================================================
-- § Bridge: Q1/Q2 Asymmetry
-- ============================================================================

open Pragmatics.GriceanMaxims

/-- Q1 and Q2 violations map to under- and over-description. -/
theorem violation_mapping :
    QuantityViolation.underInformative.submaxim = .Q1 ∧
    QuantityViolation.overInformative.submaxim = .Q2 :=
  ⟨rfl, rfl⟩

/-- The two sub-maxims of Quantity behave asymmetrically in explicit
    judgments: Q1 violations (under-description) are penalized, but
    Q2 violations (over-description) are not. -/
theorem q1_q2_asymmetry :
    -- Q2 violations (over-description): NOT penalized
    ¬exp2_target_1ref.significant ∧
    ¬exp2_goal_noCompetitor.significant ∧
    -- Q1 violations (under-description): IS penalized
    exp2_target_2ref.significant ∧
    exp2_goal_competitor.significant :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- Despite explicit tolerance of Q2 violations, over-descriptions
    incur implicit processing costs: both first-pass reading times
    and regression rates are significantly elevated. -/
theorem q2_implicit_processing_cost :
    exp3_headNoun_firstPass.anova.significant ∧
    exp3_postNoun_regressions.anova.significant :=
  ⟨rfl, rfl⟩

/-- Over-descriptions slow head-noun reading: 531ms > 489ms. -/
theorem over_description_slows_reading :
    exp3_headNoun_firstPass.modified > exp3_headNoun_firstPass.bare := by
  native_decide

/-- Over-descriptions double regression rate: 14.6% vs 7.3%. -/
theorem over_description_doubles_regressions :
    exp3_postNoun_regressions.modified > exp3_postNoun_regressions.bare := by
  native_decide

/-- Speakers are sensitive to discriminability: necessary modification
    is near-ceiling (~90%) while unnecessary modification is ~31%. -/
theorem speakers_distinguish_necessity :
    exp1_target_2ref.modified > exp1_target_1ref.modified ∧
    exp1_goal_competitor.modified > exp1_goal_noCompetitor.modified := by
  constructor <;> native_decide

-- ============================================================================
-- § Bridge: Connection to Contrastive Inference
-- ============================================================================

/-- Both this study and @cite{sedivy-etal-1999} show that adjective
    modifiers affect eye-movement patterns, but in complementary ways:

    - @cite{sedivy-etal-1999}: *necessary* modifiers trigger contrastive
      inferences, speeding target identification (competitor fixation).
    - This study: *unnecessary* modifiers impose a processing cost,
      slowing head-noun reading and increasing regressions.

    Both effects are significant, confirming that the comprehension system
    is sensitive to modifier presence and its pragmatic licensing. -/
theorem complementary_eye_tracking :
    -- Sedivy: necessary modifiers trigger contrastive inference
    SedivyEtAl1999.exp1_competitor_contrast.significant ∧
    -- This study: unnecessary modifiers cause processing cost
    exp3_headNoun_firstPass.anova.significant ∧
    exp3_postNoun_regressions.anova.significant :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § Bridge: Moderately Gricean
-- ============================================================================

/-- The paper's main conclusion: the language processing system is "only
    moderately Gricean." Evidence:

    1. Speakers violate Q2 31% of the time (over-description)
    2. Listeners don't explicitly penalize Q2 violations (tolerant)
    3. But listeners implicitly detect Q2 violations (processing cost)
    4. Listeners DO penalize Q1 violations (under-description)

    Q1 (informativeness) is enforced; Q2 (non-redundancy) operates
    implicitly rather than explicitly. -/
theorem moderately_gricean :
    -- Production: speakers violate Q2 (over-describe)
    exp1_target_1ref.modified > 0.2 ∧
    -- Judgment: Q2 violations tolerated, Q1 violations penalized
    ¬exp2_target_1ref.significant ∧
    exp2_target_2ref.significant ∧
    -- Eye-tracking: Q2 violations implicitly detected
    exp3_headNoun_firstPass.anova.significant ∧
    exp3_postNoun_regressions.anova.significant := by
  refine ⟨?_, by decide, rfl, rfl, rfl⟩; native_decide

-- ============================================================================
-- § Bridge: Support for No-Brevity (Dale & Reiter 1995)
-- ============================================================================

/-- @cite{dale-reiter-1995} argue that Q2 should be interpreted as
    "No Brevity" — speakers use a fixed preference order and include
    any discriminating attribute without optimizing for brevity.
    This study provides direct empirical support:

    1. Speakers over-describe 31% of the time (Q2 violated in production)
    2. Over-descriptions are not penalized in judgment (Q2 tolerated)
    3. Under-descriptions ARE penalized (Q1 enforced)

    This matches the No-Brevity regime: Q1 is enforced, Q2 is not. -/
theorem supports_noBrevity :
    -- Production: speakers over-describe (consistent with No-Brevity)
    exp1_target_1ref.modified > 0.2 ∧
    -- Judgment: over-description not penalized (Q2 not enforced)
    ¬exp2_target_1ref.significant ∧
    -- Judgment: under-description penalized (Q1 enforced)
    exp2_target_2ref.significant ∧
    -- No Brevity is the weakest Q2 interpretation
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 := by
  refine ⟨?_, by decide, rfl, rfl⟩; native_decide

end EngelhardtEtAl2006
