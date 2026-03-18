import Linglib.Core.Empirical

/-!
# Additive Particle Data
@cite{heim-1992} @cite{kripke-2009} @cite{rooth-1992}

Empirical data on additive particles (too, also, either) and their felicity conditions.

## Main definitions

- `AdditiveParticleDatum`: Data point for additive particle use
- `FelicityJudgment`: Acceptability ratings (ok/marginal/odd)
- `UseType`: Standard, argument-building, scalar, contrastive uses

-/

namespace Phenomena.Focus.AdditiveParticles

-- Basic Data Structures

/-- Felicity judgment for additive particle examples. -/
inductive FelicityJudgment where
  | ok
  | marginal
  | odd
  deriving DecidableEq, Repr, BEq

/-- Type of additive particle use.

Binary classification following @cite{thomas-2026}: standard (focus-alternative)
vs argument-building. Degree-"too" ("too expensive") is a distinct lexeme,
not an additive particle use. -/
inductive UseType where
  | standard        -- ANT and π are focus alternatives
  | argumentBuilding -- ANT and π jointly support a conclusion
  deriving DecidableEq, Repr, BEq

/-- Empirical data point for additive particles. -/
structure AdditiveParticleDatum where
  sentence : String
  antecedent : String
  prejacent : String
  particle : String
  resolvedQuestion : Option String
  felicity : FelicityJudgment
  useType : UseType
  notes : String := ""
  source : String := "Thomas (2026)"
  deriving Repr

/-- Classic "too" with focus alternatives. -/
def johnCameMaryToo : AdditiveParticleDatum :=
  { sentence := "John came to the party. Mary came, too."
  , antecedent := "John came to the party"
  , prejacent := "Mary came"
  , particle := "too"
  , resolvedQuestion := some "Who came to the party?"
  , felicity := .ok
  , useType := .standard
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
  }

def classicExamples : List AdditiveParticleDatum :=
  [ johnCameMaryToo
  , maryAlsoCame
  , johnSingsJohnDancesToo
  ]

def missingAntecedent : AdditiveParticleDatum :=
  { sentence := "#Mary came to the party, too."
  , antecedent := ""
  , prejacent := "Mary came to the party"
  , particle := "too"
  , resolvedQuestion := none
  , felicity := .odd
  , useType := .standard
  , notes := ""
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
  , contextMismatch
  ]

-- Polarity-Sensitive: "Either"

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

-- Cross-Linguistic Notes

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

-- @cite{rooth-1992} Examples: Focus and "Too"

/-!
## Rooth's Focus-Based Analysis

@cite{rooth-1992} §2.2 analyzes "too" via the Focus Interpretation Principle (FIP):
- The antecedent must be a **focus alternative** of the prejacent
- "Mary read Lear, and she read Macbeth too"
- Focus: MACBETH
- ⟦Macbeth⟧f = {Lear, Macbeth, Hamlet,...}
- Antecedent "Lear" ∈ ⟦Macbeth⟧f ✓

See `Theories/Semantics/Focus/Interpretation.lean` for formalization.
-/

/-- Rooth's classic "too" example -/
def roothTooLear : AdditiveParticleDatum :=
  { sentence := "Mary read Lear, and she read Macbeth too"
  , antecedent := "Mary read Lear"
  , prejacent := "Mary read Macbeth"
  , particle := "too"
  , resolvedQuestion := some "What did Mary read?"
  , felicity := .ok
  , useType := .standard
  , notes := "Antecedent 'Lear' must be in focus alternatives of 'Macbeth'"
  , source := "Rooth (1992) §2.2"
  }

/-- Rooth's example with verb focus -/
def roothTooSing : AdditiveParticleDatum :=
  { sentence := "John sang, and he danced too"
  , antecedent := "John sang"
  , prejacent := "John danced"
  , particle := "too"
  , resolvedQuestion := some "What did John do?"
  , felicity := .ok
  , useType := .standard
  , notes := "Verb-level focus: singing and dancing are activity alternatives"
  , source := "Rooth (1992)"
  }

/-- Parallel subject focus -/
def roothTooMary : AdditiveParticleDatum :=
  { sentence := "John came to the party, and Mary came too"
  , antecedent := "John came to the party"
  , prejacent := "Mary came to the party"
  , particle := "too"
  , resolvedQuestion := some "Who came to the party?"
  , felicity := .ok
  , useType := .standard
  , notes := "Subject focus: John and Mary are individual alternatives"
  , source := "Rooth (1992)"
  }

def roothExamples : List AdditiveParticleDatum :=
  [ roothTooLear
  , roothTooSing
  , roothTooMary
  ]

-- Summary Statistics

/-- All additive particle examples in this file.
    Note: Argument-building examples are in Studies/Thomas2026.lean
    Note: Ahn's "either" analysis is in Studies/Ahn2015.lean -/
def allExamples : List AdditiveParticleDatum :=
  classicExamples ++ infelicitousExamples ++
  eitherExamples ++ roothExamples

/-- Count felicitous examples. -/
def felicitousCount : Nat :=
  allExamples.filter (λ d => d.felicity == .ok) |>.length

/-- Count infelicitous examples. -/
def infelicitousCount : Nat :=
  allExamples.filter (λ d => d.felicity == .odd) |>.length

/-- Total example count. -/
def totalCount : Nat := allExamples.length

end Phenomena.Focus.AdditiveParticles
