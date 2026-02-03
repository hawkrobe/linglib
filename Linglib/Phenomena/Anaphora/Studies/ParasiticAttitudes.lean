/-
# Parasitic Attitudes: Karttunen (1973) Puzzle

Theory-neutral empirical data on presupposition projection across attitude sequences,
the key puzzle that motivates Maier (2015)'s parasitic attitude analysis.

## The Core Puzzle

Karttunen (1973) observed an asymmetry in presupposition projection:

  "Bill believed Fred had been beating his wife and he hoped Fred would stop"
  → Does NOT presuppose Fred was beating his wife (to speaker)
  → The presupposition is "filtered" by the belief ascription

But the reverse order doesn't filter:

  "*John hopes Mary will come. He believes Sue will come too."
  → DOES presuppose someone (contextually salient) will come
  → The hope doesn't filter for the belief

## Maier's Analysis (2015)

Non-doxastic attitudes (hope, imagine, dream) are **parasitic** on doxastic
attitudes (believe, know): their presupposition computation uses the belief
state's accessibility relation, not their own.

Key insight: The dependency is asymmetric - belief can filter hope's
presuppositions, but hope cannot filter belief's presuppositions.

## References

- Karttunen (1973). Presuppositions of compound sentences.
- Maier (2015). Parasitic Attitudes.
- Heim (1992). Presupposition Projection and the Semantics of Attitude Verbs.
-/

import Linglib.Core.Presupposition

namespace Phenomena.ParasiticAttitudes.Karttunen1973

open Core.Presupposition

-- ============================================================================
-- PART 1: World Types for the Bill/Fred Scenario
-- ============================================================================

/--
World type for Bill/Fred wife-beating scenario.

Models three possible states:
- Fred was beating and stopped (presupposition satisfied, assertion true)
- Fred was beating and continues (presupposition satisfied, assertion false)
- Fred never beat (presupposition fails)
-/
inductive BeatingWorld where
  | fredWasBeating_fredStopped   -- Fred used to beat, has stopped
  | fredWasBeating_fredContinues -- Fred used to beat, still does
  | fredNeverBeat                 -- Fred never beat his wife
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- PART 2: Empirical Judgment Structure
-- ============================================================================

/--
Empirical judgment about attitude sequence and presupposition projection.

Records:
- The sentence
- Whether the presupposition projects to the speaker
- Whether the presupposition is attributed to the attitude holder
- Whether the sentence is acceptable
-/
structure AttitudeSequenceJudgment where
  /-- The sentence being judged -/
  sentence : String
  /-- Does the presupposition project to the speaker? -/
  presupProjectsToSpeaker : Bool
  /-- Is the presupposition attributed to the attitude holder? -/
  presupProjectsToHolder : Bool
  /-- Is the sentence acceptable? -/
  acceptable : Bool
  deriving Repr

-- ============================================================================
-- PART 3: Core Karttunen Puzzle Data
-- ============================================================================

/--
**Core Puzzle**: Believe-hope sequences FILTER presuppositions.

"Bill believed Fred had been beating his wife and he hoped Fred would stop"

The presupposition of "stop" (that Fred was beating) is filtered by the
preceding belief ascription - it does NOT project to the speaker.

This is the key datum that Maier (2015) explains via parasitic attitudes.
-/
def believeHopeFiltering : AttitudeSequenceJudgment :=
  { sentence := "Bill believed Fred had been beating his wife and he hoped Fred would stop"
  , presupProjectsToSpeaker := false  -- KEY: presup is filtered!
  , presupProjectsToHolder := true    -- Attributed to Bill's belief state
  , acceptable := true }

/--
**Contrast**: Hope-believe does NOT filter.

"*John hopes Mary will come. He believes Sue will come too."

The "too" presupposition (someone salient will come) is NOT filtered by
the preceding hope - it projects to the speaker, causing infelicity if
no one is salient.

This asymmetry shows the dependency is one-directional: believe → hope.
-/
def hopeBelieverNoFiltering : AttitudeSequenceJudgment :=
  { sentence := "*John hopes Mary will come. He believes Sue will come too."
  , presupProjectsToSpeaker := true  -- Presup projects to speaker
  , presupProjectsToHolder := false
  , acceptable := false }            -- Infelicitous without context

/--
**Key asymmetry**: The believe-hope order matters.

Belief can satisfy hope's presuppositions, but hope cannot satisfy
belief's presuppositions. This is the parasitic dependency.
-/
theorem asymmetry_data :
    believeHopeFiltering.presupProjectsToSpeaker = false ∧
    hopeBelieverNoFiltering.presupProjectsToSpeaker = true := by
  constructor <;> rfl

-- ============================================================================
-- PART 4: Extended Data (Maier Section 5.4)
-- ============================================================================

/--
Believe-imagine also filters (imagination is parasitic on belief).

"John believed there was a monster and imagined it was chasing him"
→ No presupposition to speaker about monster existence
-/
def believeImagineFiltering : AttitudeSequenceJudgment :=
  { sentence := "John believed there was a monster and imagined it was chasing him"
  , presupProjectsToSpeaker := false
  , presupProjectsToHolder := true
  , acceptable := true }

/--
Believe-dream also filters (dreams are parasitic on beliefs).

"John believed the king existed and dreamed the king was bald"
→ No presupposition to speaker about king existence
-/
def believeDreamFiltering : AttitudeSequenceJudgment :=
  { sentence := "John believed the king existed and dreamed the king was bald"
  , presupProjectsToSpeaker := false
  , presupProjectsToHolder := true
  , acceptable := true }

/--
Imagine-believe does NOT filter (belief is not parasitic on imagination).

"?John imagined there was a monster. He believed it was dangerous."
→ Awkward: "it" presupposes established referent not from imagination
-/
def imagineBelieverNoFiltering : AttitudeSequenceJudgment :=
  { sentence := "?John imagined there was a monster. He believed it was dangerous."
  , presupProjectsToSpeaker := true
  , presupProjectsToHolder := false
  , acceptable := false }

-- ============================================================================
-- PART 5: World Model for Semantic Analysis
-- ============================================================================

/--
"Fred stopped beating his wife" as a presuppositional proposition.

Presupposition: Fred was beating his wife
Assertion: Fred no longer beats his wife
-/
def fredStopped : PrProp BeatingWorld :=
  { presup := fun w => match w with
      | .fredWasBeating_fredStopped => true
      | .fredWasBeating_fredContinues => true
      | .fredNeverBeat => false  -- Presupposition fails
  , assertion := fun w => match w with
      | .fredWasBeating_fredStopped => true
      | .fredWasBeating_fredContinues => false
      | .fredNeverBeat => false }

/--
"Fred was beating his wife" (the antecedent belief).

No presupposition, just an assertion.
-/
def fredWasBeating : PrProp BeatingWorld :=
  { presup := fun _ => true  -- No presupposition
  , assertion := fun w => match w with
      | .fredWasBeating_fredStopped => true
      | .fredWasBeating_fredContinues => true
      | .fredNeverBeat => false }

/--
The key semantic observation: the assertion of "Fred was beating" entails
the presupposition of "Fred stopped beating".

This is what enables filtering in believe-hope sequences.
-/
theorem assertion_entails_presup :
    ∀ w, fredWasBeating.assertion w = true → fredStopped.presup w = true := by
  intro w h
  cases w <;> simp_all [fredWasBeating, fredStopped]

-- ============================================================================
-- PART 6: Parasitic Attitude Classification
-- ============================================================================

/--
Classification of attitudes by their parasitic status.

- Doxastic: belief, knowledge - these are the "host" attitudes
- Parasitic: hope, fear, imagine, dream - depend on doxastic attitudes
-/
inductive AttitudeType where
  | doxastic    -- Belief, knowledge
  | parasitic   -- Hope, fear, imagine, dream
  deriving DecidableEq, Repr

/--
Common attitude verbs and their classification.
-/
def classifyAttitude : String → AttitudeType
  | "believe" => .doxastic
  | "know"    => .doxastic
  | "think"   => .doxastic
  | "hope"    => .parasitic
  | "fear"    => .parasitic
  | "imagine" => .parasitic
  | "dream"   => .parasitic
  | "wish"    => .parasitic
  | "expect"  => .parasitic
  | _         => .doxastic  -- Default to doxastic

/--
Filtering can only occur when a doxastic attitude precedes a parasitic one.

This captures Maier's key insight about the asymmetric dependency.
-/
def canFilter (first second : AttitudeType) : Bool :=
  first == .doxastic && second == .parasitic

theorem doxastic_then_parasitic_can_filter :
    canFilter .doxastic .parasitic = true := rfl

theorem parasitic_then_doxastic_cannot_filter :
    canFilter .parasitic .doxastic = false := rfl

-- ============================================================================
-- PART 7: Summary Data
-- ============================================================================

/--
All empirical judgments collected in this module.
-/
def allJudgments : List AttitudeSequenceJudgment :=
  [ believeHopeFiltering
  , hopeBelieverNoFiltering
  , believeImagineFiltering
  , believeDreamFiltering
  , imagineBelieverNoFiltering ]

/--
The filtering cases are exactly those where doxastic precedes parasitic.
-/
def filteringCases : List AttitudeSequenceJudgment :=
  [ believeHopeFiltering
  , believeImagineFiltering
  , believeDreamFiltering ]

/--
The non-filtering cases are those where parasitic precedes doxastic.
-/
def nonFilteringCases : List AttitudeSequenceJudgment :=
  [ hopeBelieverNoFiltering
  , imagineBelieverNoFiltering ]

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### World Types
- `BeatingWorld`: Models Fred's wife-beating scenario

### Empirical Judgments
- `AttitudeSequenceJudgment`: Structure for recording projection patterns
- `believeHopeFiltering`: Core Karttunen puzzle (believe→hope filters)
- `hopeBelieverNoFiltering`: Contrast (hope→believe doesn't filter)
- Extended cases: imagine, dream

### Semantic Analysis
- `fredStopped`, `fredWasBeating`: PrProp representations
- `assertion_entails_presup`: Why filtering works

### Attitude Classification
- `AttitudeType`: Doxastic vs parasitic
- `canFilter`: Predicts filtering based on order

### Key Results
- `asymmetry_data`: The believe→hope vs hope→believe asymmetry
- `doxastic_then_parasitic_can_filter`: Filtering condition

## Connection to Theory

This data motivates the theoretical analysis in:
`Theories/Montague/Verb/Attitude/Parasitic.lean`

The key insight: parasitic attitudes (hope, fear, imagine) compute their
presuppositions using the doxastic accessibility relation, not their own
preferential accessibility relation.
-/

end Phenomena.ParasiticAttitudes.Karttunen1973
