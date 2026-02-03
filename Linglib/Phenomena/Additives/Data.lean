import Linglib.Phenomena.EmpiricalData

/-!
# Additive Particle Data (Thomas 2026)

Empirical data on additive particles (too, also, either) and their felicity
conditions, following Thomas (2026) "A probabilistic, question-based approach
to additivity".

## Overview

This file contains theory-neutral empirical data on:
1. Classic additive examples (standard presuppositional use)
2. Argument-building examples (Thomas's key contribution)
3. Infelicitous cases (missing antecedent, failed conditions)
4. Polarity-sensitive uses (either in negative contexts)
5. Cross-linguistic patterns

## The Argument-Building Phenomenon

Thomas (2026) identifies a novel use of "too" where the antecedent and
prejacent aren't focus alternatives but jointly build an argument:

"Sue cooks, and she has a lot of free time, too."
- ANT = "Sue cooks"
- π = "Sue has a lot of free time"
- Neither is a focus alternative of the other
- Both contribute toward: "Sue should host the dinner party"

This challenges traditional analyses requiring focus alternatives.

## Sources

- Thomas (2026). A probabilistic, question-based approach to additivity.
- Kripke (2009). Presupposition and Anaphora.
- Heim (1992). Presupposition Projection and the Semantics of Attitude Verbs.
- Beaver & Clark (2008). Sense and Sensitivity.
-/

namespace Phenomena.AdditiveParticles

-- ============================================================================
-- Basic Data Structures
-- ============================================================================

/-- Felicity judgment for an additive particle example. -/
inductive FelicityJudgment where
  | ok       -- Fully acceptable
  | marginal -- Somewhat degraded
  | odd      -- Clearly infelicitous
  deriving DecidableEq, Repr, BEq

/-- Type of additive particle use. -/
inductive UseType where
  | standard        -- ANT and π are focus alternatives
  | argumentBuilding -- ANT and π jointly support conclusion
  | scalar          -- π is scalar alternative
  | contrastive     -- Contrastive focus
  deriving DecidableEq, Repr, BEq

/-- An empirical data point for additive particles. -/
structure AdditiveParticleDatum where
  /-- The example sentence -/
  sentence : String
  /-- The antecedent (if present) -/
  antecedent : String
  /-- The prejacent (scope of additive particle) -/
  prejacent : String
  /-- The additive particle -/
  particle : String
  /-- The resolved question (if identifiable) -/
  resolvedQuestion : Option String
  /-- Felicity judgment -/
  felicity : FelicityJudgment
  /-- Type of use -/
  useType : UseType
  /-- Additional notes -/
  notes : String := ""
  /-- Source reference -/
  source : String := "Thomas (2026)"
  deriving Repr

-- ============================================================================
-- Classic Standard Examples
-- ============================================================================

/-- Classic "too" with focus alternatives. -/
def johnCameMaryToo : AdditiveParticleDatum :=
  { sentence := "John came to the party. Mary came, too."
  , antecedent := "John came to the party"
  , prejacent := "Mary came"
  , particle := "too"
  , resolvedQuestion := some "Who came to the party?"
  , felicity := .ok
  , useType := .standard
  , notes := "Classic case: John and Mary are focus alternatives"
  }

/-- "Also" in medial position. -/
def maryAlsoCame : AdditiveParticleDatum :=
  { sentence := "John came to the party. Mary also came."
  , antecedent := "John came to the party"
  , prejacent := "Mary came"
  , particle := "also"
  , resolvedQuestion := some "Who came to the party?"
  , felicity := .ok
  , useType := .standard
  , notes := "'Also' is medial; 'too' is final"
  }

/-- Same subject, different properties. -/
def johnSingsJohnDancesToo : AdditiveParticleDatum :=
  { sentence := "John sings. He dances, too."
  , antecedent := "John sings"
  , prejacent := "John dances"
  , particle := "too"
  , resolvedQuestion := some "What does John do?"
  , felicity := .ok
  , useType := .standard
  , notes := "Same entity, different properties as alternatives"
  }

/-- Classic examples from the literature. -/
def classicExamples : List AdditiveParticleDatum :=
  [ johnCameMaryToo
  , maryAlsoCame
  , johnSingsJohnDancesToo
  ]

-- ============================================================================
-- Argument-Building Examples (Thomas 2026)
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
-- Infelicitous Cases
-- ============================================================================

/-- Missing antecedent - classic infelicity. -/
def missingAntecedent : AdditiveParticleDatum :=
  { sentence := "#Mary came to the party, too."
  , antecedent := ""
  , prejacent := "Mary came to the party"
  , particle := "too"
  , resolvedQuestion := none
  , felicity := .odd
  , useType := .standard
  , notes := "No antecedent established - presupposition failure"
  }

/-- Antecedent doesn't answer RQ. -/
def irrelevantAntecedent : AdditiveParticleDatum :=
  { sentence := "#The weather is nice. Mary came to the party, too."
  , antecedent := "The weather is nice"
  , prejacent := "Mary came to the party"
  , particle := "too"
  , resolvedQuestion := some "Who came to the party?"
  , felicity := .odd
  , useType := .standard
  , notes := "ANT doesn't answer RQ - fails antecedent condition"
  }

/-- Prejacent trivially entails conclusion. -/
def trivialPrejacent : AdditiveParticleDatum :=
  { sentence := "#John is a bachelor, and he's unmarried, too."
  , antecedent := "John is a bachelor"
  , prejacent := "John is unmarried"
  , particle := "too"
  , resolvedQuestion := some "What is John's status?"
  , felicity := .odd
  , useType := .argumentBuilding
  , notes := "π entails the same content as ANT - no additional evidence"
  }

/-- Out-of-the-blue "too" with clear context mismatch. -/
def contextMismatch : AdditiveParticleDatum :=
  { sentence := "#[Out of the blue] I like coffee, too."
  , antecedent := ""
  , prejacent := "I like coffee"
  , particle := "too"
  , resolvedQuestion := none
  , felicity := .odd
  , useType := .standard
  , notes := "No prior discourse context for ANT"
  }

/-- Infelicitous examples. -/
def infelicitousExamples : List AdditiveParticleDatum :=
  [ missingAntecedent
  , irrelevantAntecedent
  , trivialPrejacent
  , contextMismatch
  ]

-- ============================================================================
-- Polarity-Sensitive: "Either"
-- ============================================================================

/-- "Either" in negative context - felicitous. -/
def eitherNegative : AdditiveParticleDatum :=
  { sentence := "John didn't come. Mary didn't come either."
  , antecedent := "John didn't come"
  , prejacent := "Mary didn't come"
  , particle := "either"
  , resolvedQuestion := some "Who didn't come?"
  , felicity := .ok
  , useType := .standard
  , notes := "'Either' requires negative polarity context"
  }

/-- "Either" in positive context - infelicitous. -/
def eitherPositive : AdditiveParticleDatum :=
  { sentence := "#John came. Mary came either."
  , antecedent := "John came"
  , prejacent := "Mary came"
  , particle := "either"
  , resolvedQuestion := some "Who came?"
  , felicity := .odd
  , useType := .standard
  , notes := "'Either' is ungrammatical in positive contexts"
  }

/-- "Either" with negation scope. -/
def eitherWontCome : AdditiveParticleDatum :=
  { sentence := "John won't be there. I won't be there either."
  , antecedent := "John won't be there"
  , prejacent := "I won't be there"
  , particle := "either"
  , resolvedQuestion := some "Who won't be there?"
  , felicity := .ok
  , useType := .standard
  , notes := "Future negative licenses 'either'"
  }

/-- Either examples. -/
def eitherExamples : List AdditiveParticleDatum :=
  [ eitherNegative
  , eitherPositive
  , eitherWontCome
  ]

-- ============================================================================
-- Scalar/Emphatic Uses
-- ============================================================================

/-- Scalar "too" - emphatic reading. -/
def tooExpensive : AdditiveParticleDatum :=
  { sentence := "This is too expensive."
  , antecedent := ""
  , prejacent := "This is expensive (beyond threshold)"
  , particle := "too"
  , resolvedQuestion := none
  , felicity := .ok
  , useType := .scalar
  , notes := "Scalar/degree 'too' - different from additive 'too'"
  }

/-- Scalar examples (different "too"). -/
def scalarExamples : List AdditiveParticleDatum :=
  [ tooExpensive
  ]

-- ============================================================================
-- Cross-Linguistic Notes
-- ============================================================================

/-- A structure for cross-linguistic comparison data. -/
structure CrossLinguisticDatum where
  language : String
  additiveParticle : String
  gloss : String
  notes : String
  deriving Repr

/-- German "auch". -/
def germanAuch : CrossLinguisticDatum :=
  { language := "German"
  , additiveParticle := "auch"
  , gloss := "also, too"
  , notes := "Similar distribution to English 'too'/'also'"
  }

/-- Japanese "mo". -/
def japaneseMo : CrossLinguisticDatum :=
  { language := "Japanese"
  , additiveParticle := "も (mo)"
  , gloss := "also, too"
  , notes := "Particle attached to NP; broader range of uses"
  }

/-- Dutch "ook". -/
def dutchOok : CrossLinguisticDatum :=
  { language := "Dutch"
  , additiveParticle := "ook"
  , gloss := "also, too"
  , notes := "Similar to German 'auch'"
  }

/-- French "aussi". -/
def frenchAussi : CrossLinguisticDatum :=
  { language := "French"
  , additiveParticle := "aussi"
  , gloss := "also, too"
  , notes := "Typically sentence-medial or final"
  }

def crossLinguisticData : List CrossLinguisticDatum :=
  [ germanAuch
  , japaneseMo
  , dutchOok
  , frenchAussi
  ]

-- ============================================================================
-- Summary Statistics
-- ============================================================================

/-- All additive particle examples. -/
def allExamples : List AdditiveParticleDatum :=
  classicExamples ++ argumentBuildingExamples ++ infelicitousExamples ++
  eitherExamples ++ scalarExamples

/-- Count felicitous examples. -/
def felicitousCount : Nat :=
  allExamples.filter (fun d => d.felicity == .ok) |>.length

/-- Count infelicitous examples. -/
def infelicitousCount : Nat :=
  allExamples.filter (fun d => d.felicity == .odd) |>.length

/-- Count argument-building examples. -/
def argumentBuildingCount : Nat :=
  allExamples.filter (fun d => d.useType == .argumentBuilding) |>.length

/-- Total example count. -/
def totalCount : Nat := allExamples.length

end Phenomena.AdditiveParticles
