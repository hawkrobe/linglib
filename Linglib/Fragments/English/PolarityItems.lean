/-
# English Polarity-Sensitive Items

Theory-neutral lexical entries for polarity-sensitive items:
- Negative Polarity Items (NPIs): any, ever, yet, at all, lift a finger
- Free Choice Items (FCIs): any (FC use), whatever, whichever
- Positive Polarity Items (PPIs): some, already, somewhat

## Properties Captured

1. Licensing contexts: where the item can appear
2. Strength: weak (DE) vs strong (anti-additive) NPIs
3. Base quantificational force: underlying semantic type
4. Scalar direction: strengthening vs attenuating (Israel 1996)

## Theoretical Analyses (in Theories/)

- `Phenomena/Polarity/Studies/AlonsoOvalleMoghiseh2025.lean`: EFCI exhaustification analysis
- `Phenomena/NPIs/Data.lean`: Empirical distribution data

-/

import Linglib.Core.Lexical.PolarityItem

namespace Fragments.English.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- The Polarity Item Lexicon
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Weak NPIs
-- ----------------------------------------------------------------------------

/-- "any" - the prototypical NPI/FCI -/
def any : PolarityItemEntry :=
  { form := "any"
  , polarityType := .npi_fci
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody, .conditional_ant, .question
      , .modal_possibility, .modal_necessity, .imperative, .generic ]
  , scalarDirection := .strengthening  -- domain widening → stronger assertion
  , notes := "Dual NPI/FCI; obligatory domain alternatives yield universal-like FC"
  }

/-- "ever" - temporal NPI -/
def ever : PolarityItemEntry :=
  { form := "ever"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts :=
      [ .negation, .nobody, .conditional_ant, .question
      , .superlative, .comparative ]
  , scalarDirection := .strengthening  -- temporal endpoint → stronger assertion
  , notes := "Temporal NPI; also in superlatives ('best ever')"
  }

/-- "yet" - temporal NPI (different from "ever") -/
def yet : PolarityItemEntry :=
  { form := "yet"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation, .question]
  , notes := "Restricted distribution; requires relevance to 'now'"
  }

/-- "anymore" - temporal NPI -/
def anymore : PolarityItemEntry :=
  { form := "anymore"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , notes := "Very restricted; mainly with negation"
  }

/-- "at all" - degree NPI -/
def atAll : PolarityItemEntry :=
  { form := "at all"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts :=
      [.negation, .nobody, .conditional_ant, .question]
  , scalarDirection := .attenuating  -- weakens: "not at all" = not even minimally
  , notes := "Degree emphasis; 'Did you sleep at all?'"
  }

/-- "in the least" - degree NPI -/
def inTheLeast : PolarityItemEntry :=
  { form := "in the least"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts := [.negation, .question]
  , notes := "Formal register"
  }

/-- "a single" - emphatic existential NPI -/
def aSingle : PolarityItemEntry :=
  { form := "a single"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .without_clause]
  , notes := "'I didn't see a single person'"
  }

/-- "whatsoever" - emphatic NPI (post-nominal) -/
def whatsoever : PolarityItemEntry :=
  { form := "whatsoever"
  , polarityType := .npiWeak
  , baseForce := .manner
  , licensingContexts := [.negation, .nobody]
  , notes := "Post-nominal: 'no reason whatsoever'"
  }

-- ----------------------------------------------------------------------------
-- Strong NPIs (require anti-additive)
-- ----------------------------------------------------------------------------

/-- "lift a finger" - idiomatic strong NPI -/
def liftAFinger : PolarityItemEntry :=
  { form := "lift a finger"
  , polarityType := .npiStrong
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .without_clause]
  , scalarDirection := .nonScalar
  , morphology := .idiomatic
  , notes := "Idiomatic; requires anti-additive (*few people lifted a finger)"
  }

/-- "budge an inch" - idiomatic strong NPI -/
def budgeAnInch : PolarityItemEntry :=
  { form := "budge an inch"
  , polarityType := .npiStrong
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .without_clause]
  , scalarDirection := .nonScalar
  , morphology := .idiomatic
  , notes := "Idiomatic strong NPI"
  }

/-- "in years" - temporal strong NPI -/
def inYears : PolarityItemEntry :=
  { form := "in years"
  , polarityType := .npiStrong
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody]
  , notes := "'I haven't seen him in years' (*Few people have seen him in years)"
  }

/-- "until" - temporal strong NPI (in some analyses) -/
def until_ : PolarityItemEntry :=
  { form := "until"
  , polarityType := .npiStrong
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , notes := "Durative 'until' is NPI: 'didn't leave until 5'"
  }

-- ----------------------------------------------------------------------------
-- Free Choice Items
-- ----------------------------------------------------------------------------

/-- "whatever" - free relative FCI -/
def whatever : PolarityItemEntry :=
  { form := "whatever"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic, .free_relative]
  , notes := "Free relative; 'Read whatever you want'"
  }

/-- "whoever" - free relative FCI -/
def whoever : PolarityItemEntry :=
  { form := "whoever"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic, .free_relative]
  , notes := "Free relative; 'Invite whoever you like'"
  }

/-- "whichever" - free relative FCI -/
def whichever : PolarityItemEntry :=
  { form := "whichever"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic, .free_relative]
  , notes := "Free relative with restriction; 'whichever book you prefer'"
  }

-- ----------------------------------------------------------------------------
-- Positive Polarity Items (blocked in DE)
-- ----------------------------------------------------------------------------

/-- "some" (stressed) - PPI reading -/
def some_ppi : PolarityItemEntry :=
  { form := "some (stressed)"
  , polarityType := .ppi
  , baseForce := .existential
  , licensingContexts := []  -- Empty = requires positive
  , notes := "Stressed 'some' is PPI: '*I didn't see SOME students'"
  }

/-- "already" - temporal PPI -/
def already : PolarityItemEntry :=
  { form := "already"
  , polarityType := .ppi
  , baseForce := .temporal
  , licensingContexts := []
  , notes := "PPI: '*I didn't already finish' (on temporal reading)"
  }

/-- "somewhat" - degree PPI -/
def somewhat : PolarityItemEntry :=
  { form := "somewhat"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , notes := "PPI: '*I'm not somewhat tired'"
  }

/-- "rather" - degree PPI -/
def rather : PolarityItemEntry :=
  { form := "rather"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , notes := "PPI (in degree sense): '*I don't rather like it'"
  }

-- ============================================================================
-- Lexicon Access
-- ============================================================================

/-- All weak NPIs -/
def weakNPIs : List PolarityItemEntry :=
  [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever]

/-- All strong NPIs -/
def strongNPIs : List PolarityItemEntry :=
  [liftAFinger, budgeAnInch, inYears, until_]

/-- All NPIs (weak + strong) -/
def allNPIs : List PolarityItemEntry := weakNPIs ++ strongNPIs

/-- All FCIs -/
def allFCIs : List PolarityItemEntry :=
  [any, whatever, whoever, whichever]

/-- All PPIs -/
def allPPIs : List PolarityItemEntry :=
  [some_ppi, already, somewhat, rather]

/-- All polarity items -/
def allPolarityItems : List PolarityItemEntry :=
  weakNPIs ++ strongNPIs ++ [whatever, whoever, whichever] ++ allPPIs

/-- Lookup by form -/
def lookup (form : String) : Option PolarityItemEntry :=
  allPolarityItems.find? λ p => p.form == form

-- ============================================================================
-- Verification
-- ============================================================================

-- "any" is both NPI and FCI
#guard any.isNPI
#guard any.isFCI

-- "ever" is NPI but not FCI
#guard ever.isNPI
#guard !ever.isFCI

-- "whatever" is FCI but not (plain) NPI
#guard whatever.isFCI
#guard whatever.polarityType == .fci

-- PPIs have empty licensing contexts
#guard already.licensingContexts.isEmpty

-- Scalar direction tags
#guard ever.scalarDirection == .strengthening
#guard any.scalarDirection == .strengthening
#guard atAll.scalarDirection == .attenuating
#guard liftAFinger.scalarDirection == .nonScalar

-- ============================================================================
-- Summary
-- ============================================================================

end Fragments.English.PolarityItems
