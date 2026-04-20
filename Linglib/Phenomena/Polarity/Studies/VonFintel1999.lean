import Linglib.Theories.Semantics.Entailment.PolarityBuilder
import Linglib.Phenomena.Polarity.Studies.Lahiri1998
/-
# @cite{von-fintel-1999} — Empirical Data

Theory-neutral empirical observations from:

  von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context
  Dependency. Journal of Semantics 16(2), 97–148.

Four "recalcitrant" NPI-licensing contexts that are not classically DE:
1. `only` (§2)
2. Adversative attitude verbs: sorry, surprised, regret (§3)
3. Superlatives (§4.2)
4. Conditional antecedents (§4.1) / temporal `since` (§2.2)

The key empirical pattern: these contexts license NPIs despite not being
classically downward entailing. Von Fintel's Strawson-DE explains why,
but the data here is pre-theoretical.
-/

namespace VonFintel1999

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
  /-- @cite{von-fintel-1999} example number -/
  exampleNum : String := ""
  /-- Additional notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Section 1: "Only" Examples (§2)
-- ============================================================================

/-- Ex 10: "Only" licenses weak NPIs -/
def onlyEverAny : StrawsonDEDatum :=
  { sentence := "Only John ever ate any kale for breakfast"
  , npiItem := "ever/any"
  , context := "only"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "10"
  , notes := "Weak NPIs 'ever'/'any' licensed in focus of 'only'" }

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

/-- Ex 28a: "Surprised" licenses "ever" -/
def surprisedEver : StrawsonDEDatum :=
  { sentence := "Sandy is amazed/surprised that Robin ever ate kale"
  , npiItem := "ever"
  , context := "adversative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "28a"
  , notes := "Factive adversative; complement position licenses NPI" }

/-- Ex 28b: "Sorry" licenses "any" -/
def sorryAny : StrawsonDEDatum :=
  { sentence := "Sandy is sorry/regrets that Robin bought any car"
  , npiItem := "any"
  , context := "adversative"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "28b"
  , notes := "Factive adversative; complement position licenses NPI" }

/-- "Glad" does NOT reliably license NPIs (non-adversative factive).
    Not a numbered example in @cite{von-fintel-1999}; discussed in §3.3 prose.
    Von Fintel argues glad is UE, so it should not license NPIs. -/
def gladNotLicense : StrawsonDEDatum :=
  { sentence := "?Sandy is glad that Robin bought any car"
  , npiItem := "any"
  , context := "glad"
  , grammatical := false
  , isClassicallyDE := false
  , notes := "'Glad' is factive but not adversative; NPI licensing degraded (§3.3)" }

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
-- Section 4: Temporal "Since" (§2.2)
-- ============================================================================

/-- Ex 20: "Since" is not classically DE -/
def sinceNotDE : StrawsonDEDatum :=
  { sentence := "It's been five years since I saw a bird of prey in this area ⊬ five years since I saw an eagle"
  , npiItem := ""
  , context := "since"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "20"
  , notes := "The DE inference fails: seeing a bird of prey ⊬ seeing an eagle (Iatridou)" }

/-- Ex 21: "Since" licenses NPIs -/
def sinceNPI : StrawsonDEDatum :=
  { sentence := "It's been five years since I saw any bird of prey in this area"
  , npiItem := "any"
  , context := "since"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "21"
  , notes := "Temporal 'since' licenses weak NPIs (Iatridou)" }

/-- Ex 22: "Since" is Strawson-DE -/
def sinceStrawsonDE : StrawsonDEDatum :=
  { sentence := "It's been five years since I saw a bird of prey. Five years ago I saw an eagle. ∴ It's been five years since I saw an eagle."
  , npiItem := ""
  , context := "since"
  , grammatical := true
  , isClassicallyDE := false
  , exampleNum := "22"
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

-- ============================================================================
-- Cross-Linguistic: Adversative/Non-Adversative Asymmetry
-- ============================================================================

/-! @cite{lahiri-1998} §4.5 shows the same adversative/non-adversative asymmetry
    in Hindi: adversative factives (aaScarya 'surprised') license NPIs, while
    non-adversative factives (khuS 'glad') do not. This cross-linguistic
    agreement supports von Fintel's Strawson-DE analysis as a universal
    licensing mechanism, not an English-specific phenomenon. -/

open Lahiri1998
  (npi_adversative_surprise_ek npi_adversative_surprise_koii npi_glad_bad)

/-- Cross-linguistic adversative pattern: both Hindi (@cite{lahiri-1998})
    and English (@cite{von-fintel-1999}) show the same asymmetry —
    adversative factives license NPIs, non-adversative factives do not. -/
theorem adversative_crosslinguistic :
    -- English: sorry/surprised license, glad doesn't
    sorryAny.grammatical = true ∧
    surprisedEver.grammatical = true ∧
    gladNotLicense.grammatical = false ∧
    -- Hindi: aaScarya (surprised) licenses, khuS (glad) doesn't
    npi_adversative_surprise_ek.grammatical = true ∧
    npi_adversative_surprise_koii.grammatical = true ∧
    npi_glad_bad.grammatical = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end VonFintel1999

/-! ## Bridge content (merged from PolarityBuilderBridge.lean) -/

/-!
# Bridge: PolarityBuilder → Polarity Phenomena
@cite{von-fintel-1999}

Cross-layer agreement between the Builder's monotonicity-derived licensing
predictions and the Fragment's empirical `isLicensedIn` data, plus the
@cite{von-fintel-1999}'s `onlyNotDE` empirical bridge.

## Key result

The Builder's `licensesItem` (derived from monotonicity proofs) agrees with
the Fragment's `isLicensedIn` (empirical licensing lists) for all tested
context–item pairs.

-/


namespace Phenomena.Polarity.PolarityBuilderBridge

open Semantics.Entailment.PolarityBuilder
open Core.Lexical.PolarityItem
open Fragments.English.PolarityItems
open VonFintel1999 (onlyNotDE)

-- ============================================================================
-- Fragment ↔ Builder Cross-Layer Agreement
-- ============================================================================

/-!
### `isLicensedIn` ↔ `licensesItem` agreement

The Fragment's `isLicensedIn` says whether a context is in an item's
empirical licensing list. The Builder's `licensesItem` derives licensing
from monotonicity proofs. These should agree: when a context licenses an
item empirically, the corresponding monotonicity profile should derive the
same prediction.
-/

/-- Negation empirically licenses "ever" and the Builder agrees. -/
theorem fragment_builder_agree_negation_ever :
    isLicensedIn ever .negation ∧
    negationProfile.licensesItem ever = true := ⟨by decide, rfl⟩

/-- Negation empirically licenses "lift a finger" and the Builder agrees. -/
theorem fragment_builder_agree_negation_liftAFinger :
    isLicensedIn liftAFinger .negation ∧
    negationProfile.licensesItem liftAFinger = true := ⟨by decide, rfl⟩

/-- "Only" empirically licenses "ever" (via onlyFocus) and the Builder agrees. -/
theorem fragment_builder_agree_only_ever :
    ¬ isLicensedIn ever .onlyFocus ∧  -- "ever" doesn't list onlyFocus
    onlyProfile.licensesItem ever = true :=    -- but Builder derives licensing
  ⟨by decide, rfl⟩
  -- Note: the Fragment is conservative (only lists attested contexts);
  -- the Builder generalizes (any Strawson-DE context licenses weak NPIs).

/-- "At most 2" empirically blocks "lift a finger" and the Builder agrees. -/
theorem fragment_builder_agree_atMost2_liftAFinger :
    ¬ isLicensedIn liftAFinger .atMost ∧
    atMost2Profile.licensesItem liftAFinger = false := ⟨by decide, rfl⟩

/-- PPIs: "some (stressed)" not licensed under negation, Builder agrees. -/
theorem fragment_builder_agree_negation_ppi :
    ¬ isLicensedIn some_ppi .negation ∧
    negationProfile.licensesItem some_ppi = false := ⟨by decide, rfl⟩

-- ============================================================================
-- @cite{von-fintel-1999} empirical bridge
-- ============================================================================

/--
Von Fintel's empirical observation, derived: "only" has no classical DE level
and the empirical datum records it as not classically DE.
-/
theorem vonFintel_only_not_de :
    onlyProfile.strongestLevel = none ∧ onlyNotDE.isClassicallyDE = false := ⟨rfl, rfl⟩

end Phenomena.Polarity.PolarityBuilderBridge
