import Linglib.Core.Empirical

/-!
# Additive Particle Data

Empirical data on additive particles (too, also, either) and their felicity conditions.

## Main definitions

- `AdditiveParticleDatum`: Data point for additive particle use
- `FelicityJudgment`: Acceptability ratings (ok/marginal/odd)
- `UseType`: Standard, argument-building, scalar, contrastive uses

## References

- Rooth (1992). A Theory of Focus Interpretation.
- Ahn (2015). The Semantics of Additive Either.
- Kripke (2009). Presupposition and Anaphora.
- Heim (1992). Presupposition Projection and the Semantics of Attitude Verbs.
-/

namespace Phenomena.Focus.AdditiveParticles

-- Basic Data Structures

/-- Felicity judgment for additive particle examples. -/
inductive FelicityJudgment where
  | ok
  | marginal
  | odd
  deriving DecidableEq, Repr, BEq

/-- Type of additive particle use. -/
inductive UseType where
  | standard
  | argumentBuilding
  | scalar
  | contrastive
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

-- Scalar/Emphatic Uses

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

-- Rooth (1992) Examples: Focus and "Too"

/-!
## Rooth's Focus-Based Analysis

Rooth (1992) §2.2 analyzes "too" via the Focus Interpretation Principle (FIP):
- The antecedent must be a **focus alternative** of the prejacent
- "Mary read Lear, and she read Macbeth too"
- Focus: MACBETH
- ⟦Macbeth⟧f = {Lear, Macbeth, Hamlet, ...}
- Antecedent "Lear" ∈ ⟦Macbeth⟧f ✓

See `Theories/Montague/Sentence/FocusInterpretation.lean` for formalization.
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

-- Ahn (2015) Examples: "Either" Analysis

/-!
## Ahn's Analysis of "Either"

Ahn (2015) analyzes "either" as the negative polarity counterpart of "too":
- "too" presupposes conjunction: q ∧ p (antecedent q is true, prejacent p is true)
- "either" presupposes disjunction: ¬q ∨ ¬p (at least one is false)

### Three Key Properties (Ahn 2015)

1. **Antecedent Requirement**: Both require a salient antecedent
2. **Focus Sensitivity**: Both associate with focus
3. **Distinctness**: Antecedent and prejacent must be distinct propositions

### Polarity Restriction

- "too" is a PPI: requires positive context
- "either" is an NPI: requires negative context
-/

/-- Ahn's semantic characterization of "too" vs "either" -/
structure AdditiveSemanticsDatum where
  /-- The particle -/
  particle : String
  /-- Semantic contribution -/
  semantics : String
  /-- Polarity restriction -/
  polarity : String
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

def ahnTooSemantics : AdditiveSemanticsDatum :=
  { particle := "too"
  , semantics := "q ∧ p (conjunction: antecedent q true, prejacent p true)"
  , polarity := "PPI (positive polarity item)"
  , notes := "Presupposes both antecedent and prejacent are true"
  , source := "Ahn (2015)"
  }

def ahnEitherSemantics : AdditiveSemanticsDatum :=
  { particle := "either"
  , semantics := "¬q ∨ ¬p (disjunction: at least one false)"
  , polarity := "NPI (negative polarity item)"
  , notes := "Presupposes at least one of antecedent/prejacent is false"
  , source := "Ahn (2015)"
  }

/-- Ahn's three properties of additive particles -/
structure AhnPropertyDatum where
  /-- Property name -/
  property : String
  /-- Particle this applies to -/
  particle : String
  /-- Example sentence -/
  exampleSentence : String
  /-- Explanation -/
  explanation : String
  /-- Source -/
  source : String := "Ahn (2015)"
  deriving Repr

/-- Antecedent requirement for "too" -/
def ahnAntecedentToo : AhnPropertyDatum :=
  { property := "antecedent_requirement"
  , particle := "too"
  , exampleSentence := "#Mary came to the party too. (out of the blue)"
  , explanation := "Requires salient antecedent proposition in discourse"
  }

/-- Antecedent requirement for "either" -/
def ahnAntecedentEither : AhnPropertyDatum :=
  { property := "antecedent_requirement"
  , particle := "either"
  , exampleSentence := "#Mary didn't come to the party either. (out of the blue)"
  , explanation := "Requires salient antecedent proposition in discourse"
  }

/-- Focus sensitivity for "too" -/
def ahnFocusToo : AhnPropertyDatum :=
  { property := "focus_sensitivity"
  , particle := "too"
  , exampleSentence := "John read Lear. Mary read MACBETH too."
  , explanation := "Focus on 'Macbeth' determines alternatives (other plays)"
  }

/-- Focus sensitivity for "either" -/
def ahnFocusEither : AhnPropertyDatum :=
  { property := "focus_sensitivity"
  , particle := "either"
  , exampleSentence := "John didn't read Lear. Mary didn't read MACBETH either."
  , explanation := "Focus determines what's being denied as an alternative"
  }

/-- Distinctness for "too" -/
def ahnDistinctToo : AhnPropertyDatum :=
  { property := "distinctness"
  , particle := "too"
  , exampleSentence := "#John came, and John came too."
  , explanation := "Antecedent and prejacent must be distinct"
  }

/-- Distinctness for "either" -/
def ahnDistinctEither : AhnPropertyDatum :=
  { property := "distinctness"
  , particle := "either"
  , exampleSentence := "#John didn't come, and John didn't come either."
  , explanation := "Antecedent and prejacent must be distinct"
  }

def ahnPropertyData : List AhnPropertyDatum :=
  [ ahnAntecedentToo, ahnAntecedentEither
  , ahnFocusToo, ahnFocusEither
  , ahnDistinctToo, ahnDistinctEither
  ]

/-- Ahn's "either" examples as AdditiveParticleDatum -/
def ahnEitherBasic : AdditiveParticleDatum :=
  { sentence := "John didn't come. Mary didn't come either."
  , antecedent := "John didn't come"
  , prejacent := "Mary didn't come"
  , particle := "either"
  , resolvedQuestion := some "Who didn't come?"
  , felicity := .ok
  , useType := .standard
  , notes := "Basic 'either' with parallel negation"
  , source := "Ahn (2015)"
  }

def ahnEitherVerb : AdditiveParticleDatum :=
  { sentence := "John doesn't sing. He doesn't dance either."
  , antecedent := "John doesn't sing"
  , prejacent := "John doesn't dance"
  , particle := "either"
  , resolvedQuestion := some "What doesn't John do?"
  , felicity := .ok
  , useType := .standard
  , notes := "Verb focus with 'either'"
  , source := "Ahn (2015)"
  }

def ahnExamples : List AdditiveParticleDatum :=
  [ ahnEitherBasic
  , ahnEitherVerb
  ]

-- Summary Statistics

/-- All additive particle examples in this file.
    Note: Argument-building examples are in Studies/Thomas2026.lean -/
def allExamples : List AdditiveParticleDatum :=
  classicExamples ++ infelicitousExamples ++
  eitherExamples ++ scalarExamples ++ roothExamples ++ ahnExamples

/-- Count felicitous examples. -/
def felicitousCount : Nat :=
  allExamples.filter (λ d => d.felicity == .ok) |>.length

/-- Count infelicitous examples. -/
def infelicitousCount : Nat :=
  allExamples.filter (λ d => d.felicity == .odd) |>.length

/-- Total example count. -/
def totalCount : Nat := allExamples.length

end Phenomena.Focus.AdditiveParticles
