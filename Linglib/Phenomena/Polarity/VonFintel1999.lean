/-
# Von Fintel (1999) — Empirical Data

Theory-neutral empirical observations from:

  von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context
  Dependency. Journal of Semantics 16(2), 97–148.

Four "recalcitrant" NPI-licensing contexts that are not classically DE:
1. `only` (§2)
2. Adversative attitude verbs: sorry, surprised, regret (§3)
3. Superlatives (§4.2)
4. Conditional antecedents / temporal `since` (§4.1, §2.3)

The key empirical pattern: these contexts license NPIs despite not being
classically downward entailing. Von Fintel's Strawson-DE explains why,
but the data here is pre-theoretical.
-/

namespace Phenomena.Polarity.VonFintel1999

-- ============================================================================
-- Datum Structure
-- ============================================================================

/--
A single empirical observation about NPI licensing in a Strawson-DE context.
-/
structure StrawsonDEDatum where
  /-- Example sentence -/
  sentence : String
  /-- The NPI or polarity item in question -/
  npiItem : String
  /-- The licensing context type -/
  context : String
  /-- Is the sentence grammatical? -/
  grammatical : Bool
  /-- Is the context classically (not Strawson-) DE? -/
  isClassicallyDE : Bool
  /-- Von Fintel (1999) example number -/
  exampleNum : String := ""
  /-- Additional notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Section 1: "Only" Examples (§2)
-- ============================================================================

/-- Ex 10: "Only" licenses weak NPIs -/
def onlyEverAny : StrawsonDEDatum :=
  { sentence := "Only John ever goes to that restaurant"
  , npiItem := "ever"
  , context := "only"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "10"
  , notes := "Weak NPI 'ever' licensed in focus of 'only'" }

/-- Ex 11: "Only" is not classically DE -/
def onlyNotDE : StrawsonDEDatum :=
  { sentence := "Only John ate vegetables ⊬ Only John ate kale"
  , npiItem := ""
  , context := "only"
  , grammatical := true  -- sentence is fine; inference fails
  , isClassicallyDE := false
  , exampleNum := "11"
  , notes := "The DE inference fails: presupposition of conclusion not guaranteed" }

/-- Ex 18: "Only" is Strawson-DE — inference goes through with presup satisfied -/
def onlyStrawsonDE : StrawsonDEDatum :=
  { sentence := "Only John ate vegetables ⊨_S Only John ate kale (given John ate kale)"
  , npiItem := ""
  , context := "only"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "18"
  , notes := "With presupposition satisfied, the DE inference holds" }

-- ============================================================================
-- Section 2: Adversative Attitude Verbs (§3)
-- ============================================================================

/-- Ex 28a: "Sorry" licenses "any" -/
def sorryAny : StrawsonDEDatum :=
  { sentence := "Sandy is sorry that Robin bought any car"
  , npiItem := "any"
  , context := "adversative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "28a"
  , notes := "Factive adversative; complement position licenses NPI" }

/-- Ex 28b: "Surprised" licenses "ever" -/
def surprisedEver : StrawsonDEDatum :=
  { sentence := "Sandy is amazed that Robin ever ate kale"
  , npiItem := "ever"
  , context := "adversative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "28b"
  , notes := "Factive adversative; complement position licenses NPI" }

/-- Ex 31: "Glad" does NOT reliably license NPIs (non-adversative factive) -/
def gladNotLicense : StrawsonDEDatum :=
  { sentence := "?Sandy is glad that Robin bought any car"
  , npiItem := "any"
  , context := "glad"
  , grammatical := false
  , isClassicallyDE := false
  , exampleNum := "31"
  , notes := "'Glad' is factive but not adversative; NPI licensing degraded" }

/-- Adversative attitude verbs are not classically DE -/
def sorryNotDE : StrawsonDEDatum :=
  { sentence := "Sandy is sorry that Robin ate vegetables ⊬ Sandy is sorry that Robin ate kale"
  , npiItem := ""
  , context := "adversative"
  , grammatical := true
  , isClassicallyDE := false
  , notes := "The DE inference fails without presupposition guarantee" }

-- ============================================================================
-- Section 3: Superlative Examples (§4.2)
-- ============================================================================

/-- Ex 75: Superlative licenses "ever" -/
def superlativeEver : StrawsonDEDatum :=
  { sentence := "Emma is the tallest girl who ever won"
  , npiItem := "ever"
  , context := "superlative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "75"
  , notes := "Restriction of superlative licenses weak NPI" }

/-- Ex 76: Superlative is not classically DE -/
def superlativeNotDE : StrawsonDEDatum :=
  { sentence := "tallest girl in her class ⊬ tallest girl to learn the alphabet"
  , npiItem := ""
  , context := "superlative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "76"
  , notes := "The DE inference fails: narrowing domain may change ranking" }

/-- Ex 77: Superlative is Strawson-DE -/
def superlativeStrawsonDE : StrawsonDEDatum :=
  { sentence := "tallest girl in class ⊨_S tallest girl to learn alphabet (given she did)"
  , npiItem := ""
  , context := "superlative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "77"
  , notes := "With presupposition satisfied, the DE inference holds" }

-- ============================================================================
-- Section 4: Temporal "Since" (§2.3)
-- ============================================================================

/-- Ex 20: "Since" licenses NPIs -/
def sinceNPI : StrawsonDEDatum :=
  { sentence := "It's been five years since I've seen any deer"
  , npiItem := "any"
  , context := "since"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "20"
  , notes := "Temporal 'since' licenses weak NPIs (Iatridou)" }

/-- "Since" is not classically DE -/
def sinceNotDE : StrawsonDEDatum :=
  { sentence := "It's been 5 years since I saw a deer ⊬ 5 years since I saw a fawn"
  , npiItem := ""
  , context := "since"
  , grammatical := true
  , isClassicallyDE := false
  , notes := "The DE inference fails: I may have seen deer but not fawns" }

/-- "Since" is Strawson-DE -/
def sinceStrawsonDE : StrawsonDEDatum :=
  { sentence := "5 years since I saw a deer ⊨_S 5 years since I saw a fawn (given I saw a fawn)"
  , npiItem := ""
  , context := "since"
  , grammatical := true
  , isClassicallyDE := false
  , notes := "With presupposition satisfied, the DE inference holds" }

-- ============================================================================
-- Collected Data
-- ============================================================================

/-- All examples where Strawson-DE contexts license NPIs -/
def npiLicensingExamples : List StrawsonDEDatum :=
  [onlyEverAny, sorryAny, surprisedEver, superlativeEver, sinceNPI]

/-- All examples where Strawson-DE contexts fail classical DE -/
def notClassicallyDEExamples : List StrawsonDEDatum :=
  [onlyNotDE, sorryNotDE, superlativeNotDE, sinceNotDE]

-- ============================================================================
-- Empirical Generalizations
-- ============================================================================

-- All Strawson-DE contexts license NPIs
#guard npiLicensingExamples.all (·.grammatical)

-- None of the Strawson-DE contexts are classically DE
#guard npiLicensingExamples.all (! ·.isClassicallyDE)
#guard notClassicallyDEExamples.all (! ·.isClassicallyDE)

-- "Glad" (non-adversative) does NOT license NPIs
#guard !gladNotLicense.grammatical

-- Pattern: NPI licensed ∧ ¬classically DE
-- This is the empirical puzzle that Strawson-DE resolves
#guard npiLicensingExamples.all (λ d => d.grammatical && !d.isClassicallyDE)

end Phenomena.Polarity.VonFintel1999
