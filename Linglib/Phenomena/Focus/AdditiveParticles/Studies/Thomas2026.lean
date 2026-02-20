/-
# Thomas (2026): Argument-Building Additives

Empirical data from Thomas (2026) on argument-building uses of additive particles where antecedent and prejacent jointly support a conclusion rather than being focus alternatives.

## Main definitions

- `sueCooksFreetime`: Flagship example of argument-building "too"
- `argumentBuildingExamples`: Collected argument-building data

## References

- Thomas (2026). A probabilistic, question-based approach to additivity.
-/

import Linglib.Phenomena.Focus.AdditiveParticles.Data

namespace Phenomena.Focus.AdditiveParticles.Studies.Thomas2026

open Phenomena.Focus.AdditiveParticles

/-- Flagship argument-building example from Thomas (2026). -/
def sueCooksFreetime : AdditiveParticleDatum :=
  { sentence := "Sue cooks, and she has a lot of free time, too."
  , antecedent := "Sue cooks"
  , prejacent := "Sue has a lot of free time"
  , particle := "too"
  , resolvedQuestion := some "Who should host the dinner party?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := ""
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
  , notes := ""
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

-- Infelicitous Argument-Building Cases

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

-- Collected Data

/-- All Thomas (2026) examples. -/
def allExamples : List AdditiveParticleDatum :=
  argumentBuildingExamples ++ infelicitousExamples

end Phenomena.Focus.AdditiveParticles.Studies.Thomas2026
