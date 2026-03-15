/-
# English Polarity-Sensitive Items

Theory-neutral lexical entries for polarity-sensitive items:
- Negative Polarity Items (NPIs): any, ever, yet, at all, lift a finger
- Inverted NPIs: wild horses, all the tea in China, in a million years
- Free Choice Items (FCIs): any (FC use), whatever, whichever
- Positive Polarity Items (PPIs): some, already, somewhat
- Inverted PPIs: at the drop of a hat, in a jiffy, for a pittance

## Properties Captured

1. Licensing contexts: where the item can appear
2. Strength: weak (DE) vs strong (anti-additive) NPIs
3. Base quantificational force: underlying semantic type
4. Scalar direction: strengthening vs attenuating (@cite{israel-1996})
5. Scalar value: high vs low on the relevant scale (@cite{israel-2001})
6. Canonicity: canonical vs inverted (@cite{israel-2001} §3)
7. Likelihood effect: facilitating vs impeding (@cite{israel-2001} §4)

## Theoretical Analyses

- `Phenomena/Polarity/Studies/Israel2001.lean`: Scalar Model, inverted items
- `Phenomena/Polarity/Studies/AlonsoOvalleMoghiseh2025.lean`: EFCI exhaustification analysis

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
  , scalarValue := .low               -- existential = low on quantifier scale
  , canonicity := .canonical           -- low NPI = canonical
  , likelihoodEffect := .impeding      -- theme/patient role in typical use
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
  , scalarValue := .low               -- minimal temporal extent
  , canonicity := .canonical
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
  , scalarValue := .low              -- minimal degree
  , canonicity := .canonical
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
  , scalarValue := .low           -- minimal effort (a finger, not a hand)
  , canonicity := .canonical      -- low-value NPI = canonical
  , likelihoodEffect := .impeding -- patient/increment: more effort → less likely
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
  , scalarValue := .low           -- minimal distance (an inch)
  , canonicity := .canonical      -- low-value NPI = canonical
  , likelihoodEffect := .impeding -- increment: more distance → less likely
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
  , scalarDirection := .attenuating  -- weaker than "many"/"all"
  , scalarValue := .low              -- low on quantifier scale
  , canonicity := .canonical         -- low-value attenuating PPI = canonical
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
  , scalarDirection := .attenuating  -- weaker than "very"
  , scalarValue := .low              -- low degree
  , canonicity := .canonical         -- low-value attenuating PPI = canonical
  , notes := "PPI: '*I'm not somewhat tired'"
  }

/-- "rather" - degree PPI -/
def rather : PolarityItemEntry :=
  { form := "rather"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .attenuating  -- weaker than "very"
  , scalarValue := .low              -- low-to-mid degree
  , canonicity := .canonical         -- low-value attenuating PPI = canonical
  , notes := "PPI (in degree sense): '*I don't rather like it'"
  }

-- ----------------------------------------------------------------------------
-- Inverted NPIs (@cite{israel-2001} §3: maximizer NPIs)
-- ----------------------------------------------------------------------------

/-- "wild horses" - inverted emphatic NPI (high scalar value, stimulus role)
    "Wild horses couldn't keep me away." -/
def wildHorses : PolarityItemEntry :=
  { form := "wild horses"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal force
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- stimulus: more powerful → more likely to move
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3: maximizer NPI; stimulus/agent role"
  }

/-- "all the tea in China" - inverted emphatic NPI (high value, reward role)
    "I wouldn't do it for all the tea in China." -/
def allTheTeaInChina : PolarityItemEntry :=
  { form := "all the tea in China"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal reward
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- reward: bigger reward → more likely to act
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3: maximizer NPI; reward role"
  }

/-- "a ten-foot pole" - inverted emphatic NPI (high value, instrument role)
    "I wouldn't touch it with a ten-foot pole." -/
def aTenFootPole : PolarityItemEntry :=
  { form := "a ten-foot pole"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal distance instrument
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- instrument: bigger → easier to reach
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3: maximizer NPI; instrument role"
  }

/-- "in a million years" - inverted emphatic NPI (high temporal value)
    "I wouldn't marry that woman in a million years." -/
def inAMillionYears : PolarityItemEntry :=
  { form := "in a million years"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal time span
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- duration: more time → more likely (punctual event)
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3–4: inverted temporal NPI; bounded interval for punctual event"
  }

-- ----------------------------------------------------------------------------
-- Inverted PPIs (@cite{israel-2001} §3: minimizer PPIs)
-- ----------------------------------------------------------------------------

/-- "at the drop of a hat" - inverted emphatic PPI (low value, stimulus role)
    "He's scared of his own shadow / at the drop of a hat." -/
def atTheDropOfAHat : PolarityItemEntry :=
  { form := "at the drop of a hat"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: minimal stimulus → maximal reaction
  , scalarValue := .low               -- minimal provocation
  , canonicity := .inverted            -- low-value PPI = inverted
  , likelihoodEffect := .facilitating  -- stimulus: any stimulus triggers event
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3: minimizer PPI; stimulus role"
  }

/-- "in a jiffy" - inverted emphatic PPI (low temporal value)
    "We'll be back in a jiffy." -/
def inAJiffy : PolarityItemEntry :=
  { form := "in a jiffy"
  , polarityType := .ppi
  , baseForce := .temporal
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: tiny interval → impressive speed
  , scalarValue := .low               -- minimal time
  , canonicity := .inverted            -- low-value PPI = inverted
  , likelihoodEffect := .facilitating  -- bounded interval: short → event very likely
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3–4: inverted temporal PPI"
  }

/-- "for a pittance" - inverted emphatic PPI (low monetary value, reward role)
    "He got Madonna to play for peanuts." -/
def forAPittance : PolarityItemEntry :=
  { form := "for a pittance"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: tiny cost → impressive deal
  , scalarValue := .low               -- minimal monetary value
  , canonicity := .inverted            -- low-value PPI = inverted
  , likelihoodEffect := .facilitating  -- reward/price: small cost → exchange more likely
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3–4: inverted pecuniary PPI; reward role"
  }

/-- "for a song" - inverted emphatic PPI (low monetary value, reward role)
    "He bought that painting for a song." -/
def forASong : PolarityItemEntry :=
  { form := "for a song"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening
  , scalarValue := .low
  , canonicity := .inverted
  , likelihoodEffect := .facilitating
  , morphology := .idiomatic
  , notes := "@cite{israel-2001} §3: inverted pecuniary PPI; reward role"
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

/-- Inverted (maximizer) NPIs (@cite{israel-2001} §3) -/
def invertedNPIs : List PolarityItemEntry :=
  [wildHorses, allTheTeaInChina, aTenFootPole, inAMillionYears]

/-- All NPIs (weak + strong + inverted) -/
def allNPIs : List PolarityItemEntry := weakNPIs ++ strongNPIs ++ invertedNPIs

/-- All FCIs -/
def allFCIs : List PolarityItemEntry :=
  [any, whatever, whoever, whichever]

/-- Canonical PPIs -/
def canonicalPPIs : List PolarityItemEntry :=
  [some_ppi, already, somewhat, rather]

/-- Inverted (minimizer) PPIs (@cite{israel-2001} §3) -/
def invertedPPIs : List PolarityItemEntry :=
  [atTheDropOfAHat, inAJiffy, forAPittance, forASong]

/-- All PPIs -/
def allPPIs : List PolarityItemEntry :=
  canonicalPPIs ++ invertedPPIs

/-- All polarity items -/
def allPolarityItems : List PolarityItemEntry :=
  weakNPIs ++ strongNPIs ++ invertedNPIs ++
  [whatever, whoever, whichever] ++ allPPIs

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

-- Scalar value: canonical NPIs are low, inverted NPIs are high
#guard liftAFinger.scalarValue == .low
#guard budgeAnInch.scalarValue == .low
#guard wildHorses.scalarValue == .high
#guard allTheTeaInChina.scalarValue == .high

-- Canonicity: canonical vs inverted (@cite{israel-2001})
#guard liftAFinger.canonicity == .canonical
#guard budgeAnInch.canonicity == .canonical
#guard wildHorses.canonicity == .inverted
#guard allTheTeaInChina.canonicity == .inverted
#guard atTheDropOfAHat.canonicity == .inverted
#guard forAPittance.canonicity == .inverted

-- Likelihood effect: impeding = canonical, facilitating = inverted
#guard liftAFinger.likelihoodEffect == .impeding
#guard wildHorses.likelihoodEffect == .facilitating
#guard allTheTeaInChina.likelihoodEffect == .facilitating
#guard atTheDropOfAHat.likelihoodEffect == .facilitating

-- All classified items have consistent canonicity predictions
#guard allPolarityItems.all (·.canonicityConsistent)

-- ============================================================================
-- Summary
-- ============================================================================

end Fragments.English.PolarityItems
