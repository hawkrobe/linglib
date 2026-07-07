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
4. Scalar direction: strengthening vs attenuating ([israel-1996])
5. Scalar value: high vs low on the relevant scale ([israel-2001])
6. Canonicity: canonical vs inverted ([israel-2001] §3)
7. Likelihood effect: facilitating vs impeding ([israel-2001] §4)

## Theoretical Analyses

- `Studies/Israel2001.lean`: Scalar Model, inverted items
- `Studies/AlonsoOvalleMoghiseh2025.lean`: EFCI exhaustification analysis

-/

import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Polarity.Israel

namespace English.PolarityItems

open Semantics.Polarity

/-! ### The Polarity Item Lexicon -/

-- ----------------------------------------------------------------------------
-- Weak NPIs
-- ----------------------------------------------------------------------------

/-- "any" - the prototypical NPI/FCI -/
def any : Item :=
  { form := "any"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody, .conditionalAntecedent, .question
      , .modalPossibility, .modalNecessity, .imperative, .generic
      , .onlyFocus, .adversative ]
  , scalarDirection := .strengthening  -- domain widening → stronger assertion
  , scalarValue := .low               -- existential = low on quantifier scale
  , canonicity := .canonical           -- low NPI = canonical
  , likelihoodEffect := .impeding      -- theme/patient role in typical use
  , alternativeType := .domain         -- D-MIN domain alternatives (Chierchia 2006)
  }

/-- "ever" - temporal NPI -/
def ever : Item :=
  { form := "ever"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts :=
      [ .negation, .nobody, .conditionalAntecedent, .question
      , .superlative, .comparativeS, .onlyFocus, .adversative ]
  , scalarDirection := .strengthening  -- temporal endpoint → stronger assertion
  , scalarValue := .low               -- minimal temporal extent
  , canonicity := .canonical
  , alternativeType := .domain         -- D-MAX domain alternatives (Chierchia 2006)
  }

/-- "yet" - temporal NPI (different from "ever") -/
def yet : Item :=
  { form := "yet"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation, .question]
  }

/-- "anymore" - temporal NPI -/
def anymore : Item :=
  { form := "anymore"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  }

/-- "at all" - degree NPI -/
def atAll : Item :=
  { form := "at all"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts :=
      [.negation, .nobody, .conditionalAntecedent, .question]
  , scalarDirection := .strengthening -- emphatic: "not at all" = complete negation (Figure 1)
  , scalarValue := .low              -- minimal degree
  , canonicity := .canonical
  }

/-- "in the least" - degree NPI -/
def inTheLeast : Item :=
  { form := "in the least"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation, .question]
  }

/-- "a single" - emphatic existential NPI -/
def aSingle : Item :=
  { form := "a single"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  }

/-- "whatsoever" - emphatic NPI (post-nominal) -/
def whatsoever : Item :=
  { form := "whatsoever"
  , licensor := some .weak
  , baseForce := .manner
  , licensingContexts := [.negation, .nobody]
  }

-- ----------------------------------------------------------------------------
-- Strong NPIs (require anti-additive)
-- ----------------------------------------------------------------------------

/-- "lift a finger" - idiomatic strong NPI -/
def liftAFinger : Item :=
  { form := "lift a finger"
  , licensor := some .antiAdditive
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening  -- emphatic minimizer (§1, Figure 1)
  , scalarValue := .low           -- minimal effort (a finger, not a hand)
  , canonicity := .canonical      -- low-value NPI = canonical
  , likelihoodEffect := .impeding -- patient/increment: more effort → less likely
  , morphology := .idiomatic
  }

/-- "budge an inch" - idiomatic strong NPI -/
def budgeAnInch : Item :=
  { form := "budge an inch"
  , licensor := some .antiAdditive
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening  -- emphatic minimizer (§1, Figure 1)
  , scalarValue := .low           -- minimal distance (an inch)
  , canonicity := .canonical      -- low-value NPI = canonical
  , likelihoodEffect := .impeding -- increment: more distance → less likely
  , morphology := .idiomatic
  }

/-- "in years" - temporal strong NPI -/
def inYears : Item :=
  { form := "in years"
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody]
  }

/-- "until" - temporal strong NPI (in some analyses) -/
def until_ : Item :=
  { form := "until"
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation]
  }

/-- "either" — additive strong NPI ([rullmann-2003], [gajewski-2011]).

    Per [gajewski-2011] (exs. 39c, 40c, 41c, p. 120):
    *Only John likes pancakes, either / *If Bill likes pancakes, either / *Mary
    is sorry that she likes pancakes, either — strong NPI ungrammatical under
    Strawson-DE / Strawson-AA operators despite vF1999 having shown those
    contexts to be Strawson-DE. -/
def either_npi : Item :=
  { form := "either"
  , licensor := some .antiAdditive
  , baseForce := .additive
  , licensingContexts := [.negation, .nobody]
  }

-- ----------------------------------------------------------------------------
-- Free Choice Items
-- ----------------------------------------------------------------------------

/-- "whatever" - free relative FCI -/
def whatever : Item :=
  { form := "whatever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative]
  }

/-- "whoever" - free relative FCI -/
def whoever : Item :=
  { form := "whoever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative]
  }

/-- "whichever" - free relative FCI -/
def whichever : Item :=
  { form := "whichever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative]
  }

-- ----------------------------------------------------------------------------
-- Positive Polarity Items (blocked in DE)
-- ----------------------------------------------------------------------------

/-- "some" (stressed) - PPI reading -/
def some_ppi : Item :=
  { form := "some (stressed)"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := []  -- Empty = requires positive
  , scalarDirection := .attenuating  -- weaker than "many"/"all"
  , scalarValue := .low              -- low on quantifier scale
  , canonicity := .canonical         -- low-value attenuating PPI = canonical
  }

/-- "already" - temporal PPI -/
def already : Item :=
  { form := "already"
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := []
  }

/-- "somewhat" - degree PPI -/
def somewhat : Item :=
  { form := "somewhat"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .attenuating  -- weaker than "very"
  , scalarValue := .low              -- low degree
  , canonicity := .canonical         -- low-value attenuating PPI = canonical
  }

/-- "rather" - degree PPI -/
def rather : Item :=
  { form := "rather"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .attenuating  -- weaker than "very"
  , scalarValue := .low              -- low-to-mid degree
  , canonicity := .canonical         -- low-value attenuating PPI = canonical
  }

-- ----------------------------------------------------------------------------
-- Canonical Emphatic PPIs (Figure 1: high value, emphatic)
-- ----------------------------------------------------------------------------

/-- "tons of" - canonical emphatic PPI (high value)
    "She has tons of friends." -/
def tonsOf : Item :=
  { form := "tons of"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: maximal quantity
  , scalarValue := .high               -- high on quantity scale
  , canonicity := .canonical           -- high-value emphatic PPI = canonical
  }

/-- "utterly" - canonical emphatic PPI (high degree)
    "I was utterly depressed." -/
def utterly : Item :=
  { form := "utterly"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: maximal degree
  , scalarValue := .high               -- high on degree scale
  , canonicity := .canonical           -- high-value emphatic PPI = canonical
  }

-- ----------------------------------------------------------------------------
-- Inverted NPIs (§3: maximizer NPIs)
-- ----------------------------------------------------------------------------

/-- "wild horses" - inverted emphatic NPI (high scalar value, stimulus role)
    "Wild horses couldn't keep me away." -/
def wildHorses : Item :=
  { form := "wild horses"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal force
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- stimulus: more powerful → more likely to move
  , morphology := .idiomatic
  }

/-- "all the tea in China" - inverted emphatic NPI (high value, reward role)
    "I wouldn't do it for all the tea in China." -/
def allTheTeaInChina : Item :=
  { form := "all the tea in China"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal reward
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- reward: bigger reward → more likely to act
  , morphology := .idiomatic
  }

/-- "a ten-foot pole" - inverted emphatic NPI (high value, instrument role)
    "I wouldn't touch it with a ten-foot pole." -/
def aTenFootPole : Item :=
  { form := "a ten-foot pole"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal distance instrument
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- instrument: bigger → easier to reach
  , morphology := .idiomatic
  }

/-- "in a million years" - inverted emphatic NPI (high temporal value)
    "I wouldn't marry that woman in a million years." -/
def inAMillionYears : Item :=
  { form := "in a million years"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , scalarValue := .high              -- maximal time span
  , canonicity := .inverted           -- high-value NPI = inverted
  , likelihoodEffect := .facilitating -- duration: more time → more likely (punctual event)
  , morphology := .idiomatic
  }

-- ----------------------------------------------------------------------------
-- Inverted PPIs (§3: minimizer PPIs)
-- ----------------------------------------------------------------------------

/-- "at the drop of a hat" - inverted emphatic PPI (low value, stimulus role)
    "He's scared of his own shadow / at the drop of a hat." -/
def atTheDropOfAHat : Item :=
  { form := "at the drop of a hat"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: minimal stimulus → maximal reaction
  , scalarValue := .low               -- minimal provocation
  , canonicity := .inverted            -- low-value PPI = inverted
  , likelihoodEffect := .facilitating  -- stimulus: any stimulus triggers event
  , morphology := .idiomatic
  }

/-- "in a jiffy" - inverted emphatic PPI (low temporal value)
    "We'll be back in a jiffy." -/
def inAJiffy : Item :=
  { form := "in a jiffy"
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: tiny interval → impressive speed
  , scalarValue := .low               -- minimal time
  , canonicity := .inverted            -- low-value PPI = inverted
  , likelihoodEffect := .facilitating  -- bounded interval: short → event very likely
  , morphology := .idiomatic
  }

/-- "for a pittance" - inverted emphatic PPI (low monetary value, reward role)
    "He got Madonna to play for peanuts." -/
def forAPittance : Item :=
  { form := "for a pittance"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening  -- emphatic: tiny cost → impressive deal
  , scalarValue := .low               -- minimal monetary value
  , canonicity := .inverted            -- low-value PPI = inverted
  , likelihoodEffect := .facilitating  -- reward/price: small cost → exchange more likely
  , morphology := .idiomatic
  }

/-- "for a song" - inverted emphatic PPI (low monetary value, reward role)
    "He bought that painting for a song." -/
def forASong : Item :=
  { form := "for a song"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := .strengthening
  , scalarValue := .low
  , canonicity := .inverted
  , likelihoodEffect := .facilitating
  , morphology := .idiomatic
  }

/-! ### Lexicon Access -/

/-- All weak NPIs -/
def weakNPIs : List Item :=
  [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever]

/-- All strong NPIs -/
def strongNPIs : List Item :=
  [liftAFinger, budgeAnInch, inYears, until_]

/-- Inverted (maximizer) NPIs (§3) -/
def invertedNPIs : List Item :=
  [wildHorses, allTheTeaInChina, aTenFootPole, inAMillionYears]

/-- All NPIs (weak + strong + inverted) -/
def allNPIs : List Item := weakNPIs ++ strongNPIs ++ invertedNPIs

/-- All FCIs -/
def allFCIs : List Item :=
  [any, whatever, whoever, whichever]

/-- Canonical PPIs -/
def canonicalPPIs : List Item :=
  [some_ppi, already, somewhat, rather, tonsOf, utterly]

/-- Inverted (minimizer) PPIs (§3) -/
def invertedPPIs : List Item :=
  [atTheDropOfAHat, inAJiffy, forAPittance, forASong]

/-- All PPIs -/
def allPPIs : List Item :=
  canonicalPPIs ++ invertedPPIs

/-- All polarity items -/
def allPolarityItems : List Item :=
  weakNPIs ++ strongNPIs ++ invertedNPIs ++
  [whatever, whoever, whichever] ++ allPPIs

/-- Lookup by form -/
def lookup (form : String) : Option Item :=
  allPolarityItems.find? λ p => p.form == form

/-! ### Verification -/

-- "any" is both NPI and FCI
example : any.isNPI := by decide
example : any.isFCI := by decide

-- "ever" is NPI but not FCI
example : ever.isNPI := by decide
example : ¬ ever.isFCI := by decide

-- "whatever" is FCI but not (plain) NPI
example : whatever.isFCI := by decide

-- PPIs have empty licensing contexts
#guard already.licensingContexts.isEmpty

-- Scalar direction tags
#guard ever.scalarDirection == .strengthening
#guard any.scalarDirection == .strengthening
#guard atAll.scalarDirection == .strengthening
#guard liftAFinger.scalarDirection == .strengthening

-- Scalar value: canonical NPIs are low, inverted NPIs are high
#guard liftAFinger.scalarValue == .low
#guard budgeAnInch.scalarValue == .low
#guard wildHorses.scalarValue == .high
#guard allTheTeaInChina.scalarValue == .high

-- Canonicity: canonical vs inverted ()
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

-- Canonical emphatic PPIs: high value, strengthening (Figure 1)
#guard tonsOf.scalarValue == .high
#guard tonsOf.scalarDirection == .strengthening
#guard tonsOf.canonicity == .canonical
#guard utterly.scalarValue == .high
#guard utterly.scalarDirection == .strengthening
#guard utterly.canonicity == .canonical

-- All classified items have consistent canonicity predictions
example : ∀ p ∈ allPolarityItems, p.canonicityConsistent := by decide

/-- Every attested context of every entry is predicted licensed. -/
theorem english_licensing_sound :
    ∀ e ∈ allPolarityItems, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

/-! ### Summary -/

end English.PolarityItems
