import Linglib.Phenomena.Constructions.Studies.FillmoreKayOConnor1988

/-!
# Resultative Construction — Empirical Data

Theory-neutral grammaticality judgments and aspectual contrasts for
English resultative constructions, drawn from Goldberg & Jackendoff (2004)
"The English Resultative as a Family of Constructions" (Language 80(3):532–568).

## Phenomena covered

1. **Causative property resultatives**: "hammer the metal flat"
2. **Causative path resultatives**: "kick the ball into the field"
3. **Noncausative property resultatives**: "the river froze solid"
4. **Noncausative path resultatives**: "the ball rolled into the field"
5. **Fake reflexive resultatives**: "She laughed herself silly"
6. **Aspectual contrasts**: telic vs atelic frame tests
7. **Unacceptable resultatives**: semantic coherence violations

## Reference

Goldberg, A. E. & Jackendoff, R. (2004). The English Resultative as a
Family of Constructions. Language, 80(3), 532–568.
-/

namespace Phenomena.Constructions.Resultatives

open Phenomena.Constructions.Studies.FillmoreKayOConnor1988

/-! ## Datum structure -/

/-- What type of resultative is exemplified. -/
inductive ResultativeType where
  | causativeProperty
  | causativePath
  | noncausativeProperty
  | noncausativePath
  | fakeReflexive
  deriving Repr, DecidableEq, BEq

/-- A single resultative example with judgment data. -/
structure ResultativeDatum where
  /-- Example identifier -/
  exId : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Judgment
  /-- Which resultative subtype -/
  resType : ResultativeType
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! ## 1. Causative property resultatives (§2, Table 1) -/

def hammer_flat : ResultativeDatum :=
  { exId := "1a"
  , sentence := "She hammered the metal flat"
  , judgment := .grammatical
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become flat" }

def wipe_clean : ResultativeDatum :=
  { exId := "1b"
  , sentence := "He wiped the table clean"
  , judgment := .grammatical
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become clean" }

def paint_red : ResultativeDatum :=
  { exId := "1c"
  , sentence := "They painted the house red"
  , judgment := .grammatical
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become red" }

/-! ## 2. Causative path resultatives (§2, Table 1) -/

def kick_into_field : ResultativeDatum :=
  { exId := "2a"
  , sentence := "She kicked the ball into the field"
  , judgment := .grammatical
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to go to goal" }

def push_off_table : ResultativeDatum :=
  { exId := "2b"
  , sentence := "He pushed the glass off the table"
  , judgment := .grammatical
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to move from source" }

/-! ## 3. Noncausative property resultatives (§2, Table 1) -/

def freeze_solid : ResultativeDatum :=
  { exId := "3a"
  , sentence := "The river froze solid"
  , judgment := .grammatical
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: theme becomes result state" }

def swing_shut : ResultativeDatum :=
  { exId := "3b"
  , sentence := "The gate swung shut"
  , judgment := .grammatical
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: unaccusative verb + result state" }

/-! ## 4. Noncausative path resultatives (§2, Table 1) -/

def roll_into_field : ResultativeDatum :=
  { exId := "4a"
  , sentence := "The ball rolled into the field"
  , judgment := .grammatical
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves along path" }

def slide_off_table : ResultativeDatum :=
  { exId := "4b"
  , sentence := "The book slid off the table"
  , judgment := .grammatical
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves from source" }

/-! ## 5. Fake reflexive resultatives (§5) -/

def laugh_silly : ResultativeDatum :=
  { exId := "5a"
  , sentence := "She laughed herself silly"
  , judgment := .grammatical
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: intransitive verb + reflexive + result" }

def drink_sick : ResultativeDatum :=
  { exId := "5b"
  , sentence := "He drank himself sick"
  , judgment := .grammatical
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: verb lacks patient; construction adds it" }

def run_ragged : ResultativeDatum :=
  { exId := "5c"
  , sentence := "She ran herself ragged"
  , judgment := .grammatical
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: unergative verb + reflexive + result" }

/-! ## 6. Aspectual contrasts (§4, Principle 27)

Resultatives are telic: they accept *in*-adverbials and reject *for*-adverbials.
Bare activity verbs are atelic: they accept *for* and reject *in*. -/

/-- An aspectual contrast pair. -/
structure AspectualContrast where
  /-- Sentence with temporal adverbial -/
  sentence : String
  /-- Judgment -/
  judgment : Judgment
  /-- Which adverbial type -/
  adverbialType : String
  /-- Description -/
  description : String
  deriving Repr, BEq

def hammer_flat_in : AspectualContrast :=
  { sentence := "She hammered the metal flat in an hour"
  , judgment := .grammatical
  , adverbialType := "in-adverbial"
  , description := "resultative is telic: in-adverbial OK" }

def hammer_flat_for : AspectualContrast :=
  { sentence := "*She hammered the metal flat for an hour"
  , judgment := .ungrammatical
  , adverbialType := "for-adverbial"
  , description := "resultative is telic: for-adverbial bad" }

def hammer_bare_for : AspectualContrast :=
  { sentence := "She hammered the metal for an hour"
  , judgment := .grammatical
  , adverbialType := "for-adverbial"
  , description := "bare activity is atelic: for-adverbial OK" }

def hammer_bare_in : AspectualContrast :=
  { sentence := "??She hammered the metal in an hour"
  , judgment := .marginal
  , adverbialType := "in-adverbial"
  , description := "bare activity is atelic: in-adverbial degraded" }

/-! ## 7. Unacceptable resultatives (§6, semantic coherence violations) -/

def eat_full : ResultativeDatum :=
  { exId := "7a"
  , sentence := "*She ate the food full"
  , judgment := .ungrammatical
  , resType := .causativeProperty
  , phenomenon := "semantic incoherence: patient of eat ≠ entity that becomes full" }

def sleep_flat : ResultativeDatum :=
  { exId := "7b"
  , sentence := "*She slept the bed flat"
  , judgment := .ungrammatical
  , resType := .causativeProperty
  , phenomenon := "semantic incoherence: sleep cannot cause flatness" }

/-! ## All data -/

def allExamples : List ResultativeDatum :=
  [ hammer_flat, wipe_clean, paint_red
  , kick_into_field, push_off_table
  , freeze_solid, swing_shut
  , roll_into_field, slide_off_table
  , laugh_silly, drink_sick, run_ragged
  , eat_full, sleep_flat ]

def aspectualContrasts : List AspectualContrast :=
  [ hammer_flat_in, hammer_flat_for, hammer_bare_for, hammer_bare_in ]

/-! ## Verification theorems -/

/-- All four resultative types are attested in the data. -/
theorem has_all_resultative_types :
    (allExamples.any (·.resType == .causativeProperty)) = true ∧
    (allExamples.any (·.resType == .causativePath)) = true ∧
    (allExamples.any (·.resType == .noncausativeProperty)) = true ∧
    (allExamples.any (·.resType == .noncausativePath)) = true ∧
    (allExamples.any (·.resType == .fakeReflexive)) = true := by
  constructor; native_decide
  constructor; native_decide
  constructor; native_decide
  constructor; native_decide
  native_decide

/-- Both grammatical and ungrammatical examples are represented. -/
theorem has_both_judgments :
    (allExamples.any (·.judgment == .grammatical)) = true ∧
    (allExamples.any (·.judgment == .ungrammatical)) = true := by
  constructor; native_decide
  native_decide

/-- The aspectual contrast data includes both in- and for-adverbials. -/
theorem aspectual_both_adverbials :
    (aspectualContrasts.any (·.adverbialType == "in-adverbial")) = true ∧
    (aspectualContrasts.any (·.adverbialType == "for-adverbial")) = true := by
  constructor; native_decide
  native_decide

/-- Telic resultatives accept in-adverbials and reject for-adverbials. -/
theorem telic_adverbial_pattern :
    hammer_flat_in.judgment == .grammatical ∧
    hammer_flat_for.judgment == .ungrammatical := by
  constructor <;> native_decide

/-- Atelic bare activities accept for-adverbials. -/
theorem atelic_adverbial_pattern :
    hammer_bare_for.judgment == .grammatical := by
  native_decide

end Phenomena.Constructions.Resultatives
