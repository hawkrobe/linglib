/-
# Thomas (2026): Argument-Building Additives

Empirical data from Thomas (2026) "A probabilistic, question-based approach
to additivity" on the **argument-building** use of additive particles.

## The Phenomenon

Thomas identifies a novel use of "too" where the antecedent and prejacent
are NOT focus alternatives but jointly build an argument toward a conclusion:

"Sue cooks, and she has a lot of free time, too."
- ANT = "Sue cooks"
- π = "Sue has a lot of free time"
- Neither is a focus alternative of the other
- Both contribute toward: "Sue should host the dinner party"

This challenges traditional analyses (Rooth 1992, Kripke 2009) that require
the antecedent to be a focus alternative of the prejacent.

## Thomas's Analysis

Thomas proposes a **question-based** account:
- Both ANT and π must answer a common Resolved Question (RQ)
- The RQ is typically an implicit "big question" being addressed
- "too" signals that π provides additional evidence toward the same goal

## Key Properties

1. **Non-alternative antecedents**: ANT and π need not be focus alternatives
2. **Cumulative evidence**: Both contribute to answering a common RQ
3. **Implicit conclusion**: The RQ is often an evaluative/decision question

## References

- Thomas (2026). A probabilistic, question-based approach to additivity.
-/

import Linglib.Phenomena.AdditiveParticles.Data

namespace Phenomena.AdditiveParticles.Studies.Thomas2026

open Phenomena.AdditiveParticles

-- ============================================================================
-- Argument-Building Examples
-- ============================================================================

/-- The flagship argument-building example from Thomas (2026). -/
def sueCooksFreetime : AdditiveParticleDatum :=
  { sentence := "Sue cooks, and she has a lot of free time, too."
  , antecedent := "Sue cooks"
  , prejacent := "Sue has a lot of free time"
  , particle := "too"
  , resolvedQuestion := some "Who should host the dinner party?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "Key example: ANT and π jointly evidence 'Sue should host'"
  , source := "Thomas (2026)"
  }

/-- Another argument-building example: hiring decision. -/
def brilliantHardworking : AdditiveParticleDatum :=
  { sentence := "He's brilliant, and he's hard-working, too."
  , antecedent := "He's brilliant"
  , prejacent := "He's hard-working"
  , particle := "too"
  , resolvedQuestion := some "Should we hire him?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "Both properties evidence positive hiring decision"
  , source := "Thomas (2026)"
  }

/-- Argument-building: qualities supporting a conclusion. -/
def kindGenerous : AdditiveParticleDatum :=
  { sentence := "She's kind, and she's generous, too."
  , antecedent := "She's kind"
  , prejacent := "She's generous"
  , particle := "too"
  , resolvedQuestion := some "Is she a good person?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "Cumulative positive evidence"
  , source := "Thomas (2026)"
  }

/-- Argument-building with negative conclusion. -/
def lateUnprepared : AdditiveParticleDatum :=
  { sentence := "He was late, and he was unprepared, too."
  , antecedent := "He was late"
  , prejacent := "He was unprepared"
  , particle := "too"
  , resolvedQuestion := some "Did the presentation go well?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "Both properties evidence negative outcome"
  , source := "Thomas (2026)"
  }

/-- Argument-building: recommendation. -/
def quietAffordable : AdditiveParticleDatum :=
  { sentence := "The neighborhood is quiet, and it's affordable, too."
  , antecedent := "The neighborhood is quiet"
  , prejacent := "It's affordable"
  , particle := "too"
  , resolvedQuestion := some "Should we move there?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "Cumulative factors supporting a decision"
  , source := "Thomas (2026)"
  }

/-- Argument-building examples from Thomas (2026). -/
def argumentBuildingExamples : List AdditiveParticleDatum :=
  [ sueCooksFreetime
  , brilliantHardworking
  , kindGenerous
  , lateUnprepared
  , quietAffordable
  ]

-- ============================================================================
-- Infelicitous Argument-Building Cases
-- ============================================================================

/-- Prejacent trivially entails conclusion - fails additivity. -/
def trivialPrejacent : AdditiveParticleDatum :=
  { sentence := "#John is a bachelor, and he's unmarried, too."
  , antecedent := "John is a bachelor"
  , prejacent := "John is unmarried"
  , particle := "too"
  , resolvedQuestion := some "What is John's status?"
  , felicity := .odd
  , useType := .argumentBuilding
  , notes := "π entails the same content as ANT - no additional evidence"
  , source := "Thomas (2026)"
  }

/-- Infelicitous argument-building examples. -/
def infelicitousExamples : List AdditiveParticleDatum :=
  [ trivialPrejacent
  ]

-- ============================================================================
-- Collected Data
-- ============================================================================

/-- All Thomas (2026) examples. -/
def allExamples : List AdditiveParticleDatum :=
  argumentBuildingExamples ++ infelicitousExamples

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data
- `argumentBuildingExamples`: 5 felicitous argument-building uses of "too"
- `infelicitousExamples`: Cases where argument-building fails

### Key Insight

The argument-building use shows that "too" does NOT require focus alternatives:
- "Sue cooks" and "Sue has free time" are not alternatives
- But both answer "Who should host?" → felicitous use of "too"

This motivates Thomas's question-based analysis over Rooth's focus-based one.

### Theoretical Connections

- Contrasts with Rooth (1992): Focus alternatives not required
- Contrasts with Kripke (2009): Anaphoric analysis insufficient
- Supports question-based pragmatics (Roberts 1996, Beaver & Clark 2008)
-/

end Phenomena.AdditiveParticles.Studies.Thomas2026
