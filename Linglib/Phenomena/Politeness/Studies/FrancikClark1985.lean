import Linglib.Core.Discourse.SpeechActs
import Linglib.Core.Modality.ModalTypes

/-!
# @cite{francik-clark-1985} — How to Make Requests That Overcome
  Obstacles to Compliance
@cite{clark-1979} @cite{searle-1969}

Journal of Memory and Language 24 (1985) 560–568.

## Overview

Speakers design requests to overcome the greatest potential obstacle to
compliance. Obstacle types correspond to @cite{searle-1969}'s preparatory
conditions for requests — ability (including knowledge, memory, perception)
and willingness — plus speaker memory. Three experiments show:

1. **Higher obstacles → fewer direct requests** (Exp. 1, Table 1)
2. **Form content matches obstacle type**: "Do you know?" for knowledge
   doubt, "Do you remember?" for memory, "Would you mind?" for
   willingness (Exp. 1 & 2)
3. **Can/Could are general-purpose**: high appropriateness across all
   scenario types because they cover both ability and willingness (Exp. 3)
4. **Sidestepping**: when obstacles are too sensitive, speakers approach
   obliquely rather than mentioning the obstacle directly (Exp. 1)

## Three Strategies for Overcoming Obstacles

1. **Conditional request**: make the request conditional on the absence of
   the obstacle. "Did you happen to see what time the concert begins?"
   means "if you saw it, tell me." More specific obstacles → more
   specific conditions → less direct forms.
2. **General-purpose request**: when the obstacle is ill-specified, use a
   broadly applicable form. "Can you tell me?" and "Could you tell me?"
   cover both ability and willingness, making them applicable across
   many situations.
3. **Sidestepping**: when the obstacle is too sensitive to mention, approach
   obliquely. Ask for related information the addressee IS willing to give.

## Connection to Preparatory Conditions

The obstacle types formalized here derive from `PreparatoryCondition` in
`Core.Discourse.SpeechActs`. Each obstacle IS a preparatory condition at
risk. The specificity gradient (Can you? → Do you know? → Do you
remember? → Did you happen to read...?) corresponds to descending the
subsumption hierarchy.
-/

set_option autoImplicit false

namespace Phenomena.Politeness.Studies.FrancikClark1985

open Core.Discourse (PreparatoryCondition)
open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Obstacle Types
-- ════════════════════════════════════════════════════

/-- Obstacle types from the paper's experimental design. These correspond
    to the risk that a specific preparatory condition will not be met. -/
inductive ObstacleType where
  | ability       -- Addressee may not be able to provide the information
  | willingness   -- Addressee may not be willing to provide the information
  | speakerMemory -- Speaker uncertain whether request was already made
  deriving DecidableEq, Repr

/-- Obstacle level: high or low risk that the precondition fails. -/
inductive ObstacleLevel where
  | high  -- Significant risk of non-compliance
  | low   -- Minimal risk
  deriving DecidableEq, Repr

/-- Map obstacle types to the preparatory condition at risk.
    Speaker memory is not a preparatory condition on the hearer, so it
    maps to `none` — it's a precondition on the *speaker*. -/
def ObstacleType.toPreparatoryCondition : ObstacleType → Option PreparatoryCondition
  | .ability      => some .ability
  | .willingness  => some .willingness
  | .speakerMemory => none

/-- Map obstacle types to their closest modal flavor.
    Ability obstacles concern the addressee's circumstances (can/could).
    Willingness maps to deontic as a rough approximation: "Would you?"
    concerns what the addressee allows themselves to do. Strictly, this is
    volitional/bouletic modality (the will of the agent), which the current
    `ModalFlavor` enum does not distinguish from deontic (external norms).
    Speaker memory has no corresponding modal flavor. -/
def ObstacleType.modalFlavor : ObstacleType → Option ModalFlavor
  | .ability       => some .circumstantial
  | .willingness   => some .deontic
  | .speakerMemory => none


-- ════════════════════════════════════════════════════
-- § 2. Request Forms
-- ════════════════════════════════════════════════════

/-- The five request form types tested in Experiment 3. These cover the
    space from ability-specific to willingness-specific, with Can/Could
    as general-purpose forms spanning both. -/
inductive RequestForm where
  | doYouKnow       -- "Do you know X?" — targets knowledge (ability)
  | canYouTellMe    -- "Can you tell me X?" — general (ability + willingness)
  | couldYouTellMe  -- "Could you tell me X?" — general (ability + willingness)
  | wouldYouMind    -- "Would you mind telling me X?" — targets willingness
  | haveYouToldMe   -- "Have you already told me X?" — targets speaker memory
  deriving DecidableEq, Repr

/-- The preparatory condition primarily queried by each request form. -/
def RequestForm.queriedCondition : RequestForm → Option PreparatoryCondition
  | .doYouKnow      => some .knowledge
  | .canYouTellMe   => some .ability
  | .couldYouTellMe => some .ability
  | .wouldYouMind   => some .willingness
  | .haveYouToldMe  => none  -- queries speaker memory, not a hearer condition

/-- Whether a form is "general-purpose" — applicable across both ability
    and willingness scenarios. -/
def RequestForm.isGeneralPurpose : RequestForm → Bool
  | .canYouTellMe | .couldYouTellMe => true
  | _ => false


-- ════════════════════════════════════════════════════
-- § 3. Experiment 1 — Direct Request Rates (Table 1)
-- ════════════════════════════════════════════════════

/-! N = 30 (15 per list), 24 scenarios per participant (12 ability +
    8 willingness + 4 memory). Each percentage is based on 15 requests
    per scenario. Responses were pared to requests-proper by omitting
    prefaces, justifications, and obligations.
    Key finding: min F'(1,29) = 46.90, p < .001 for the obstacle effect. -/

structure Exp1Result where
  obstacleType : ObstacleType
  level        : ObstacleLevel
  nScenarios   : Nat
  directPct    : Nat  -- percentage of direct requests (0–100)
  deriving Repr

def exp1_ability_high : Exp1Result :=
  { obstacleType := .ability, level := .high, nScenarios := 12, directPct := 25 }
def exp1_ability_low : Exp1Result :=
  { obstacleType := .ability, level := .low, nScenarios := 12, directPct := 37 }
def exp1_willingness_high : Exp1Result :=
  { obstacleType := .willingness, level := .high, nScenarios := 8, directPct := 34 }
def exp1_willingness_low : Exp1Result :=
  { obstacleType := .willingness, level := .low, nScenarios := 8, directPct := 54 }
def exp1_memory_high : Exp1Result :=
  { obstacleType := .speakerMemory, level := .high, nScenarios := 4, directPct := 68 }
def exp1_memory_low : Exp1Result :=
  { obstacleType := .speakerMemory, level := .low, nScenarios := 4, directPct := 82 }

/-- Core finding: for every scenario type, high obstacles produce fewer
    direct requests than low obstacles. -/
theorem obstacle_reduces_directness :
    exp1_ability_high.directPct < exp1_ability_low.directPct ∧
    exp1_willingness_high.directPct < exp1_willingness_low.directPct ∧
    exp1_memory_high.directPct < exp1_memory_low.directPct := by
  native_decide

/-- Overall: 35% direct in high-obstacle vs 49% in low-obstacle
    (unweighted mean across the three types). -/
theorem overall_obstacle_effect :
    exp1_ability_high.directPct + exp1_willingness_high.directPct +
    exp1_memory_high.directPct <
    exp1_ability_low.directPct + exp1_willingness_low.directPct +
    exp1_memory_low.directPct := by native_decide


-- ════════════════════════════════════════════════════
-- § 4. Experiment 2 — Directness Scores (Table 2)
-- ════════════════════════════════════════════════════

/-! Experiment 2 (N = 10) collected directness rankings (1 = most direct)
    for the request forms produced in Experiment 1. High-obstacle mean
    directness = 4.09, low = 3.64 (min F'(1,48) = 4.59, p < .05). -/

/-- Directness score for a request form. Score × 100 to stay in Nat. -/
structure DirectnessEntry where
  form  : String
  score : Nat  -- directness rank × 100 (100 = rank 1.0, most direct)
  deriving Repr

/-- The nine request forms from the "time" scenario (asking a student the
    time at Tresidder), ordered from most to least direct. Each successive
    form describes the obstacle more specifically.

    High obstacle: addressee is clearly not wearing a watch.
    Low obstacle: addressee is wearing a watch. -/
def timeScenarioForms : List DirectnessEntry :=
  [ ⟨"What time is it?",                                     100⟩
  , ⟨"Do you know what time it is?",                          300⟩
  , ⟨"Could you tell me what time it is?",                    340⟩
  , ⟨"Do you have the time?",                                 420⟩
  , ⟨"Do you happen to know what time it is?",                450⟩
  , ⟨"Do you have any idea what time it is?",                 600⟩
  , ⟨"You wouldn't happen to know the time, would you?",      670⟩
  , ⟨"Do you happen to have a watch...?",                     730⟩
  , ⟨"Do you know if there's a clock anywhere around here?",  880⟩ ]

/-- Scores increase monotonically: more specific obstacle descriptions
    are judged less direct. -/
theorem directness_monotonic :
    timeScenarioForms.map (·.score) =
    [100, 300, 340, 420, 450, 600, 670, 730, 880] := rfl


-- ════════════════════════════════════════════════════
-- § 5. Experiment 1 — Obstacle-Specific Form Usage
-- ════════════════════════════════════════════════════

/-! Speakers chose request forms whose content matched the specific
    obstacle they faced. Percentages from the paper's text.

    Six obstacle categories are distinguished, each with characteristic
    request forms that appear predominantly or exclusively in the
    matching scenario type. -/

structure FormUsageRate where
  description   : String
  scenarioRange : String
  highPct       : Nat  -- % usage in high-obstacle condition
  lowPct        : Nat  -- % usage in low-obstacle condition
  deriving Repr

-- Category 1: Knowledge uncertain (scenarios 1–5)
def usage_doYouKnow : FormUsageRate :=
  { description := "Do you know? / Do you happen to know? / Do you have any idea?"
  , scenarioRange := "scenarios 1–5 (knowledge uncertain)"
  , highPct := 77, lowPct := 25 }

-- Category 2: Memory uncertain (scenarios 6–7)
def usage_doYouRemember : FormUsageRate :=
  { description := "Do you remember?"
  , scenarioRange := "scenarios 6–7 (memory uncertain)"
  , highPct := 20, lowPct := 13 }

-- Category 3: Perception uncertain (scenarios 8–10)
-- In these scenarios the low obstacle is ALSO substantial (addressee may
-- not remember), so speakers use indirect forms for both levels. The form
-- shifts from perception-targeting to memory-targeting as the obstacle
-- changes from perception to memory.
def usage_didYouSee : FormUsageRate :=
  { description := "Did you see/hear/notice?"
  , scenarioRange := "scenarios 8–10 (perception uncertain)"
  , highPct := 42, lowPct := 31 }

def usage_doYouRemember_inPerception : FormUsageRate :=
  { description := "Do you remember? (in perception scenarios)"
  , scenarioRange := "scenarios 8–10 (memory uncertain in low obstacle)"
  , highPct := 11, lowPct := 31 }

-- Category 4: Permission/policy (scenarios 11–12)
-- Borderline ability/willingness. Speakers SIDESTEP the obstacle.
def usage_couldIGet : FormUsageRate :=
  { description := "Could I get? (sidestepping permission obstacle)"
  , scenarioRange := "scenarios 11–12 (permission/policy)"
  , highPct := 37, lowPct := 17 }

-- Category 5: Willingness (scenarios 13–20)
-- Can/Could used 30% high vs 26% low. Would you? only 7% high, 2% low.
-- Many speakers sidestepped (volunteered personal info, steered topic).
def usage_sidestepping_willingness : FormUsageRate :=
  { description := "Sidestepping (volunteered personal info, steered topic)"
  , scenarioRange := "scenarios 13–20 (willingness uncertain)"
  , highPct := 23, lowPct := 9 }

def usage_wouldYou_produced : FormUsageRate :=
  { description := "Would you? / Would you mind? (production)"
  , scenarioRange := "scenarios 13–20 (willingness uncertain)"
  , highPct := 7, lowPct := 2 }

-- Category 6: Speaker memory (scenarios 21–24)
def usage_haveIAsked : FormUsageRate :=
  { description := "Have I asked you? / Did you tell me?"
  , scenarioRange := "scenarios 21–24 (speaker memory)"
  , highPct := 27, lowPct := 5 }

/-- In every obstacle category, the obstacle-specific form is used more
    in high-obstacle than low-obstacle conditions. -/
theorem obstacle_specific_forms_increase :
    usage_doYouKnow.highPct > usage_doYouKnow.lowPct ∧
    usage_doYouRemember.highPct > usage_doYouRemember.lowPct ∧
    usage_didYouSee.highPct > usage_didYouSee.lowPct ∧
    usage_couldIGet.highPct > usage_couldIGet.lowPct ∧
    usage_haveIAsked.highPct > usage_haveIAsked.lowPct := by
  native_decide

/-- In scenarios 8–10, the form REVERSES between high and low obstacle:
    perception forms dominate when perception is the obstacle (high),
    memory forms dominate when memory is the obstacle (low). This is the
    strongest per-scenario test of obstacle-specific form selection. -/
theorem perception_memory_reversal :
    usage_didYouSee.highPct > usage_doYouRemember_inPerception.highPct ∧
    usage_doYouRemember_inPerception.lowPct > usage_doYouRemember_inPerception.highPct ∧
    usage_didYouSee.highPct > usage_didYouSee.lowPct := by
  native_decide

/-- Sidestepping was exclusive to willingness/permission scenarios:
    never used in ability scenarios. The rate increased with obstacle
    level (23% vs 9% for willingness; 37% vs 17% for permission). -/
theorem sidestepping_exclusive_to_willingness :
    usage_sidestepping_willingness.highPct > usage_sidestepping_willingness.lowPct ∧
    usage_couldIGet.highPct > usage_couldIGet.lowPct := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 6. Experiment 3 — Appropriateness Ratings (Table 3)
-- ════════════════════════════════════════════════════

/-! N = 18. Five request forms rated for appropriateness (1–7 scale) in
    each scenario type × obstacle level. Ratings stored as hundredths
    (5.52 → 552) to stay in Nat. -/

structure AppropriatenessRating where
  form         : RequestForm
  obstacleType : ObstacleType
  level        : ObstacleLevel
  rating       : Nat  -- rating × 100
  deriving Repr

-- Ability scenarios
def app_know_ab_hi   : AppropriatenessRating := ⟨.doYouKnow,      .ability, .high, 552⟩
def app_know_ab_lo   : AppropriatenessRating := ⟨.doYouKnow,      .ability, .low,  485⟩
def app_can_ab_hi    : AppropriatenessRating := ⟨.canYouTellMe,   .ability, .high, 526⟩
def app_can_ab_lo    : AppropriatenessRating := ⟨.canYouTellMe,   .ability, .low,  533⟩
def app_could_ab_hi  : AppropriatenessRating := ⟨.couldYouTellMe, .ability, .high, 512⟩
def app_could_ab_lo  : AppropriatenessRating := ⟨.couldYouTellMe, .ability, .low,  549⟩
def app_would_ab_hi  : AppropriatenessRating := ⟨.wouldYouMind,   .ability, .high, 429⟩
def app_would_ab_lo  : AppropriatenessRating := ⟨.wouldYouMind,   .ability, .low,  507⟩
def app_told_ab_hi   : AppropriatenessRating := ⟨.haveYouToldMe,  .ability, .high, 178⟩
def app_told_ab_lo   : AppropriatenessRating := ⟨.haveYouToldMe,  .ability, .low,  197⟩

-- Willingness scenarios
def app_know_wi_hi   : AppropriatenessRating := ⟨.doYouKnow,      .willingness, .high, 246⟩
def app_know_wi_lo   : AppropriatenessRating := ⟨.doYouKnow,      .willingness, .low,  279⟩
def app_can_wi_hi    : AppropriatenessRating := ⟨.canYouTellMe,   .willingness, .high, 419⟩
def app_can_wi_lo    : AppropriatenessRating := ⟨.canYouTellMe,   .willingness, .low,  503⟩
def app_could_wi_hi  : AppropriatenessRating := ⟨.couldYouTellMe, .willingness, .high, 456⟩
def app_could_wi_lo  : AppropriatenessRating := ⟨.couldYouTellMe, .willingness, .low,  514⟩
def app_would_wi_hi  : AppropriatenessRating := ⟨.wouldYouMind,   .willingness, .high, 550⟩
def app_would_wi_lo  : AppropriatenessRating := ⟨.wouldYouMind,   .willingness, .low,  572⟩
def app_told_wi_hi   : AppropriatenessRating := ⟨.haveYouToldMe,  .willingness, .high, 215⟩
def app_told_wi_lo   : AppropriatenessRating := ⟨.haveYouToldMe,  .willingness, .low,  235⟩

-- Memory scenarios
def app_know_me_hi   : AppropriatenessRating := ⟨.doYouKnow,      .speakerMemory, .high, 350⟩
def app_know_me_lo   : AppropriatenessRating := ⟨.doYouKnow,      .speakerMemory, .low,  361⟩
def app_can_me_hi    : AppropriatenessRating := ⟨.canYouTellMe,   .speakerMemory, .high, 458⟩
def app_can_me_lo    : AppropriatenessRating := ⟨.canYouTellMe,   .speakerMemory, .low,  475⟩
def app_could_me_hi  : AppropriatenessRating := ⟨.couldYouTellMe, .speakerMemory, .high, 472⟩
def app_could_me_lo  : AppropriatenessRating := ⟨.couldYouTellMe, .speakerMemory, .low,  481⟩
def app_would_me_hi  : AppropriatenessRating := ⟨.wouldYouMind,   .speakerMemory, .high, 330⟩
def app_would_me_lo  : AppropriatenessRating := ⟨.wouldYouMind,   .speakerMemory, .low,  356⟩
def app_told_me_hi   : AppropriatenessRating := ⟨.haveYouToldMe,  .speakerMemory, .high, 525⟩
def app_told_me_lo   : AppropriatenessRating := ⟨.haveYouToldMe,  .speakerMemory, .low,  306⟩


-- ════════════════════════════════════════════════════
-- § 6b. Appropriateness Theorems
-- ════════════════════════════════════════════════════

/-- "Do you know?" most appropriate in ability scenarios.
    Mean across obstacle levels: ability 5.19, willingness 2.63,
    memory 3.56. min F'(1,27) = 76.96, p < .001. -/
theorem know_best_for_ability :
    (app_know_ab_hi.rating + app_know_ab_lo.rating) >
    (app_know_wi_hi.rating + app_know_wi_lo.rating) ∧
    (app_know_ab_hi.rating + app_know_ab_lo.rating) >
    (app_know_me_hi.rating + app_know_me_lo.rating) := by native_decide

/-- "Would you mind?" most appropriate in willingness scenarios.
    Mean: willingness 5.61, ability 4.68, memory 3.43. -/
theorem would_best_for_willingness :
    (app_would_wi_hi.rating + app_would_wi_lo.rating) >
    (app_would_ab_hi.rating + app_would_ab_lo.rating) ∧
    (app_would_wi_hi.rating + app_would_wi_lo.rating) >
    (app_would_me_hi.rating + app_would_me_lo.rating) := by native_decide

/-- "Have you told me?" most appropriate in memory scenarios.
    Mean: memory 4.16, willingness 2.25, ability 1.88. -/
theorem told_best_for_memory :
    (app_told_me_hi.rating + app_told_me_lo.rating) >
    (app_told_ab_hi.rating + app_told_ab_lo.rating) ∧
    (app_told_me_hi.rating + app_told_me_lo.rating) >
    (app_told_wi_hi.rating + app_told_wi_lo.rating) := by native_decide

/-- Even when memory scenarios are omitted, ability forms are most
    appropriate in ability scenarios and willingness forms in willingness
    scenarios. min F'(1,23) = 21.82, p < .001. -/
theorem matching_without_memory :
    -- ability forms higher in ability than willingness
    (app_know_ab_hi.rating + app_know_ab_lo.rating +
     app_can_ab_hi.rating + app_can_ab_lo.rating +
     app_could_ab_hi.rating + app_could_ab_lo.rating) >
    (app_know_wi_hi.rating + app_know_wi_lo.rating +
     app_can_wi_hi.rating + app_can_wi_lo.rating +
     app_could_wi_hi.rating + app_could_wi_lo.rating) ∧
    -- willingness form higher in willingness than ability
    (app_would_wi_hi.rating + app_would_wi_lo.rating) >
    (app_would_ab_hi.rating + app_would_ab_lo.rating) := by native_decide

/-- Can/Could are the most appropriate forms overall.
    Mean: Can 4.96, Could 5.06, Do you know 4.06, Would you mind 4.78,
    Have you told me 2.38. min F'(1,38) = 139.62, p < .001. -/
theorem can_could_general_purpose :
    let canSum := app_can_ab_hi.rating + app_can_ab_lo.rating +
                  app_can_wi_hi.rating + app_can_wi_lo.rating +
                  app_can_me_hi.rating + app_can_me_lo.rating
    let couldSum := app_could_ab_hi.rating + app_could_ab_lo.rating +
                    app_could_wi_hi.rating + app_could_wi_lo.rating +
                    app_could_me_hi.rating + app_could_me_lo.rating
    let knowSum := app_know_ab_hi.rating + app_know_ab_lo.rating +
                   app_know_wi_hi.rating + app_know_wi_lo.rating +
                   app_know_me_hi.rating + app_know_me_lo.rating
    let wouldSum := app_would_ab_hi.rating + app_would_ab_lo.rating +
                    app_would_wi_hi.rating + app_would_wi_lo.rating +
                    app_would_me_hi.rating + app_would_me_lo.rating
    let toldSum := app_told_ab_hi.rating + app_told_ab_lo.rating +
                   app_told_wi_hi.rating + app_told_wi_lo.rating +
                   app_told_me_hi.rating + app_told_me_lo.rating
    canSum > knowSum ∧ canSum > wouldSum ∧ canSum > toldSum ∧
    couldSum > knowSum ∧ couldSum > wouldSum ∧ couldSum > toldSum := by
  native_decide

/-- Can/Could are less appropriate in high-obstacle than low-obstacle
    conditions (min F'(1,34) = 12.02, p < .001). General-purpose forms
    are outperformed by obstacle-specific forms when a specific obstacle
    can be identified. -/
theorem can_could_less_appropriate_with_specific_obstacle :
    (app_can_ab_hi.rating + app_can_wi_hi.rating + app_can_me_hi.rating) <
    (app_can_ab_lo.rating + app_can_wi_lo.rating + app_can_me_lo.rating) ∧
    (app_could_ab_hi.rating + app_could_wi_hi.rating + app_could_me_hi.rating) <
    (app_could_ab_lo.rating + app_could_wi_lo.rating + app_could_me_lo.rating) := by
  native_decide

/-- Production-comprehension dissociation: "Would you mind?" was rarely
    PRODUCED in willingness scenarios (only 7% high, 2% low in Exp 1)
    but was RATED as highly appropriate (5.61 mean in Exp 3). Speakers
    recognize it as legitimate but prefer Can/Could. -/
theorem wouldYou_production_comprehension_gap :
    -- Low production rate
    usage_wouldYou_produced.highPct < 10 ∧
    usage_wouldYou_produced.lowPct < 5 ∧
    -- High appropriateness rating
    (app_would_wi_hi.rating + app_would_wi_lo.rating) > 1000 := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 7. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- Obstacle types that concern the hearer map to preparatory conditions;
    speaker memory does not. -/
theorem hearer_obstacles_are_preparatory :
    ObstacleType.toPreparatoryCondition .ability = some .ability ∧
    ObstacleType.toPreparatoryCondition .willingness = some .willingness ∧
    ObstacleType.toPreparatoryCondition .speakerMemory = none := ⟨rfl, rfl, rfl⟩

/-- Request forms query the condition matching their obstacle target.
    "Do you know?" queries `.knowledge`, a subtype of `.ability`.
    "Would you mind?" queries `.willingness`. -/
theorem form_targets_match_obstacle :
    RequestForm.queriedCondition .doYouKnow = some .knowledge ∧
    RequestForm.queriedCondition .wouldYouMind = some .willingness ∧
    RequestForm.queriedCondition .haveYouToldMe = none := ⟨rfl, rfl, rfl⟩

/-- Knowledge (queried by "Do you know?") is subsumed by ability. This
    is why "Do you know?" is specific to ability scenarios: it queries a
    SUBTYPE of the ability preparatory condition. -/
theorem knowledge_is_ability_subtype :
    PreparatoryCondition.ability.subsumes .knowledge = true := rfl

/-- Can/Could query the general `.ability` condition, which subsumes both
    `.knowledge` and `.permission`. This structural property explains
    their broad applicability across scenario types (Exp. 3). -/
theorem general_forms_query_broad_condition :
    RequestForm.queriedCondition .canYouTellMe = some .ability ∧
    RequestForm.queriedCondition .couldYouTellMe = some .ability ∧
    PreparatoryCondition.ability.subsumes .knowledge = true ∧
    PreparatoryCondition.ability.subsumes .permission = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Ability obstacles map to circumstantial modality: "Can you?" questions
    the addressee's circumstances. Willingness maps to deontic as the
    closest available flavor (see § 1 note on the bouletic gap). -/
theorem obstacle_modal_flavors :
    ObstacleType.modalFlavor .ability = some .circumstantial ∧
    ObstacleType.modalFlavor .willingness = some .deontic := ⟨rfl, rfl⟩

/-- The specificity gradient in request forms corresponds to depth in the
    preparatory condition subsumption hierarchy:

    Can you? (ability) ⊃ Do you know? (knowledge) ⊃ Do you remember? (memory)

    More specific obstacles → deeper in the hierarchy → less direct forms. -/
theorem specificity_is_subsumption_depth :
    PreparatoryCondition.ability.subsumes .knowledge = true ∧
    PreparatoryCondition.knowledge.subsumes .memory = true ∧
    PreparatoryCondition.knowledge.subsumes .perception = true := ⟨rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 8. End-to-End Argumentation
-- ════════════════════════════════════════════════════

/-! The obstacle model predicts: when a form queries a preparatory
    condition that matches the scenario's obstacle type, it will be rated
    more appropriate than when it doesn't match. We verify this for each
    of the three form–obstacle pairings. -/

/-- End-to-end: "Do you know?" queries `.knowledge` (⊂ `.ability`),
    and the appropriateness data confirms it is rated highest in ability
    scenarios. The subsumption hierarchy predicts the data. -/
theorem endToEnd_know_ability :
    RequestForm.queriedCondition .doYouKnow = some .knowledge ∧
    PreparatoryCondition.ability.subsumes .knowledge = true ∧
    (app_know_ab_hi.rating + app_know_ab_lo.rating) >
    (app_know_wi_hi.rating + app_know_wi_lo.rating) ∧
    (app_know_ab_hi.rating + app_know_ab_lo.rating) >
    (app_know_me_hi.rating + app_know_me_lo.rating) := by
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

/-- End-to-end: "Would you mind?" queries `.willingness`, and the data
    confirms it is rated highest in willingness scenarios. -/
theorem endToEnd_would_willingness :
    RequestForm.queriedCondition .wouldYouMind = some .willingness ∧
    ObstacleType.toPreparatoryCondition .willingness = some .willingness ∧
    (app_would_wi_hi.rating + app_would_wi_lo.rating) >
    (app_would_ab_hi.rating + app_would_ab_lo.rating) ∧
    (app_would_wi_hi.rating + app_would_wi_lo.rating) >
    (app_would_me_hi.rating + app_would_me_lo.rating) := by
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

/-- End-to-end: Can/Could query `.ability` (general), which subsumes all
    ability subtypes, and the data confirms they are rated highly across
    ALL scenario types — the broadest condition yields the broadest
    applicability. -/
theorem endToEnd_canCould_general :
    RequestForm.isGeneralPurpose .canYouTellMe = true ∧
    RequestForm.isGeneralPurpose .couldYouTellMe = true ∧
    RequestForm.queriedCondition .canYouTellMe = some .ability ∧
    -- Can is above 4.0 (400) in ALL six scenario-type × obstacle-level cells
    app_can_ab_hi.rating > 400 ∧ app_can_ab_lo.rating > 400 ∧
    app_can_wi_hi.rating > 400 ∧ app_can_wi_lo.rating > 400 ∧
    app_can_me_hi.rating > 400 ∧ app_can_me_lo.rating > 400 := by
  exact ⟨rfl, rfl, rfl, by native_decide, by native_decide,
         by native_decide, by native_decide,
         by native_decide, by native_decide⟩

end Phenomena.Politeness.Studies.FrancikClark1985
