import Linglib.Theories.Syntax.ConstructionGrammar.Resultatives
import Linglib.Features.Acceptability

/-!
# @cite{goldberg-jackendoff-2004}: The English Resultative as a Family of Constructions
@cite{goldberg-jackendoff-2004}

Paper data and per-datum verifications for @cite{goldberg-jackendoff-2004}.
The construction-theoretic primitives (`ResultativeSubconstruction`,
`SubeventDesc`, the fusion machinery, the universal-quantifier theorems)
live in `Theories/Syntax/ConstructionGrammar/Resultatives.lean`, which
this file imports.

## Key claims

1. The English resultative is not one construction but a **family of four subconstructions**
   organized along two dimensions: causative/noncausative × property/path RP
2. Every resultative has a **dual subevent structure**: a verbal subevent (from the verb)
   and a constructional subevent (CAUSE + BECOME/GO from the construction)
3. The verbal and constructional subevents are linked by typed semantic relations:
   MEANS, RESULT, INSTANCE, or CO-OCCURRENCE
4. **Full Argument Realization (FAR)**: all obligatory arguments of both verb and
   construction must be syntactically realized; shared arguments fuse
5. **Semantic Coherence**: verb role rV and construction role rC may fuse only if
   rV is construable as an instance of rC
6. **Aspectual constraint**: resultatives are telic iff the RP denotes a bounded path/property
7. **Temporal constraint**: the constructional subevent cannot temporally precede
   the verbal subevent

## File contents

This file holds:

- The paper's eight resultative *entries* (`hammerFlat`, `kickIntoField`, …)
  and the `allEntries` list — concrete data points the paper discusses.
- Per-datum verification theorems demonstrating the paper's data is
  consistent with the construction theory.
- A separate empirical-data layer (`ResultativeType`, `ResultativeDatum`,
  `allExamples`, `aspectualContrasts`) holding theory-neutral grammaticality
  judgments and aspectual contrasts drawn from §§2–8 of the paper.
-/

namespace Phenomena.Constructions.Resultatives.Studies.GoldbergJackendoff2004

open ConstructionGrammar
open ConstructionGrammar.Resultatives
open Core.Verbs
open Semantics.Tense.Aspect.LexicalAspect

/-! ## Empirical data: resultative entries -/

def hammerFlat : ResultativeEntry :=
  { verb := "hammer", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "She hammered the metal"
  , levinClass := .hit }               -- Levin §18.1

def kickIntoField : ResultativeEntry :=
  { verb := "kick", subconstruction := .causativePath
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "She kicked the ball"
  , levinClass := .hit }               -- Levin §18.1

def freezeSolid : ResultativeEntry :=
  { verb := "freeze", subconstruction := .noncausativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .achievement
  , levinClass := .otherCoS }          -- Levin §45.4

def rollIntoField : ResultativeEntry :=
  { verb := "roll", subconstruction := .noncausativePath
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , levinClass := .mannerOfMotion }    -- Levin §51.3

def drinkSick : ResultativeEntry :=
  { verb := "drink", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .unselected  -- cf. *"They drank the pub"
  , levinClass := .eat }                 -- Levin §39.1

def laughSilly : ResultativeEntry :=
  { verb := "laugh", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .fakeReflexive  -- cf. *"She laughed him silly"
  , levinClass := .performance }             -- Levin §26.7

def swingShut : ResultativeEntry :=
  { verb := "swing", subconstruction := .noncausativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , levinClass := .mannerOfMotion }    -- Levin §51.3

def wipeClean : ResultativeEntry :=
  { verb := "wipe", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "He wiped the table"
  , levinClass := .wipe }              -- Levin §10.4

/-- All resultative entries. -/
def allEntries : List ResultativeEntry :=
  [ hammerFlat, kickIntoField, freezeSolid, rollIntoField
  , drinkSick, laughSilly, swingShut, wipeClean ]

/-! ## Per-datum verification theorems -/

-- Subconstruction classification
theorem hammerFlat_is_causativeProperty :
    hammerFlat.subconstruction = .causativeProperty := rfl

theorem kickIntoField_is_causativePath :
    kickIntoField.subconstruction = .causativePath := rfl

theorem freezeSolid_is_noncausativeProperty :
    freezeSolid.subconstruction = .noncausativeProperty := rfl

theorem rollIntoField_is_noncausativePath :
    rollIntoField.subconstruction = .noncausativePath := rfl

-- Subevent relations: all core entries default to MEANS
theorem hammerFlat_means : hammerFlat.subeventRelation = .means := rfl
theorem freezeSolid_means : freezeSolid.subeventRelation = .means := rfl
theorem drinkSick_means : drinkSick.subeventRelation = .means := rfl

/-- All four core subconstructions use MEANS (§3, summary 97a–d).
    RESULT is reserved for sound-emission and disappearance subconstructions. -/
theorem all_core_entries_use_means :
    allEntries.all (·.subeventRelation == .means) = true := by
  native_decide

-- Derived subevent structure: CAUSE follows from subconstruction

/-- Causative entries have CAUSE in their derived constructional subevent. -/
theorem causative_entries_have_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- Noncausative entries lack CAUSE in their derived constructional subevent. -/
theorem noncausative_entries_no_cause :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => !e.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- All derived constructional subevents have BECOME. -/
theorem all_constructional_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  native_decide

-- Object selection: intransitive entries have no object selection

/-- Noncausative (intransitive) entries have no object selection. -/
theorem noncausative_no_object_selection :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => e.objectSelection == none) = true := by
  native_decide

/-- All causative entries specify an object selection mode. -/
theorem causative_have_object_selection :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (λ e => e.objectSelection.isSome) = true := by
  native_decide

-- Aspectual predictions

/-- All entries with bounded RP are telic. -/
theorem bounded_entries_telic :
    (allEntries.filter (·.rpBoundedness == .bounded)).all
      (λ e => (resultativeAspect e.rpBoundedness).telicity == .telic) = true := by
  native_decide

/-! ### Theorems migrated from `Theories.Semantics.Causation.Resultatives`

These theorems quantify over `allEntries` (paper-specific data) and
therefore belong with the paper, not in the Theory layer. -/

/-- All causative entries in the data have CAUSE. -/
theorem causative_resultative_has_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- MEANS-relation causative entries all have CAUSE. -/
theorem causative_means_have_cause :
    (allEntries.filter (λ e =>
      e.subconstruction.isCausative && e.subeventRelation == .means
    )).all (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- Activity verbs in the data with bounded RPs become accomplishments. -/
theorem activity_entries_become_accomplishments :
    (allEntries.filter (λ e =>
      e.bareVerbClass == .activity && e.rpBoundedness == .bounded
    )).all (λ e =>
      resultativeVendlerClass e.rpBoundedness == .accomplishment
    ) = true := by
  native_decide

/-- All resultative entries have BECOME. -/
theorem all_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  native_decide

/-! ## Per-entry verb class participation

The construction-verb interaction across the four canonical Levin classes
that @cite{goldberg-jackendoff-2004} discuss: manner verbs (hit = hammer/kick),
change-of-state verbs (otherCoS = freeze), motion verbs (mannerOfMotion =
roll/swing), and removing verbs (wipe). -/

/-- All entries acquire CoS from the construction, regardless of verb class. -/
theorem all_entries_fused_cos :
    allEntries.all (λ e => e.fusedMC.changeOfState) = true := by
  native_decide

/-- All entries participate in the resultative alternation (none are instrument-spec). -/
theorem all_entries_resultative_alternation :
    allEntries.all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .resultative) = true := by
  native_decide

/-- Causative entries all acquire the causative alternation. -/
theorem causative_entries_causative_alternation :
    (allEntries.filter (·.subconstruction.isCausative)).all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .causativeInchoative) = true := by
  native_decide

/-- Noncausative entries do NOT acquire the causative alternation
    (unless the verb already has causation — freeze/otherCoS does). -/
theorem noncausative_entries_no_new_causation :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .causativeInchoative
      = e.verbMC.predictedAlternation .causativeInchoative) = true := by
  native_decide

/-- Hammer (hit-class): no CoS or causation alone → both added by causative construction. -/
theorem hammer_gains_cos_causation :
    hammerFlat.verbMC.changeOfState = false ∧
    hammerFlat.verbMC.causation = false ∧
    hammerFlat.fusedMC.changeOfState = true ∧
    hammerFlat.fusedMC.causation = true := by
  constructor; native_decide
  constructor; native_decide
  constructor <;> native_decide

/-- Freeze (otherCoS): already has CoS + causation → construction doesn't change profile. -/
theorem freeze_already_has_cos :
    freezeSolid.verbMC.changeOfState = true ∧
    freezeSolid.verbMC.causation = true ∧
    freezeSolid.fusedMC = freezeSolid.verbMC := by
  constructor; native_decide
  constructor <;> native_decide

/-- Roll (manner-of-motion): gains CoS from construction; no causation (noncausative). -/
theorem roll_gains_cos_only :
    rollIntoField.verbMC.changeOfState = false ∧
    rollIntoField.fusedMC.changeOfState = true ∧
    rollIntoField.fusedMC.causation = false := by
  constructor; native_decide
  constructor <;> native_decide

/-- Laugh (performance): pure manner verb — construction adds CoS + causation. -/
theorem laugh_gains_cos_causation :
    laughSilly.verbMC.changeOfState = false ∧
    laughSilly.verbMC.causation = false ∧
    laughSilly.fusedMC.changeOfState = true ∧
    laughSilly.fusedMC.causation = true := by
  constructor; native_decide
  constructor; native_decide
  constructor <;> native_decide

/-- Wipe (wipe-class): already has full profile — construction is redundant. -/
theorem wipe_already_has_everything :
    wipeClean.verbMC.changeOfState = true ∧
    wipeClean.verbMC.causation = true ∧
    wipeClean.fusedMC = wipeClean.verbMC := by
  constructor; native_decide
  constructor <;> native_decide

/-! ## Empirical data: grammaticality judgments

Theory-neutral grammaticality judgments and aspectual contrasts drawn
from §§2–8 of the paper. These provide the shared data layer that
other studies (Dendikken, Tay, Levin) connect to their own analyses. -/

open Features (Acceptability)

/-- What type of resultative is exemplified.

Extends the paper's 2×2 matrix (§2) with fake reflexives (§5) and
anticausative property resultatives (@cite{levin-2026}). -/
inductive ResultativeType where
  | causativeProperty
  | causativePath
  | noncausativeProperty
  | noncausativePath
  | fakeReflexive
  /-- Anticausative: verb doesn't alternate alone; construction licenses it
      (@cite{levin-2026}). Distinct from `noncausativeProperty` (e.g., *freeze
      solid*) where the verb independently shows the causative alternation. -/
  | anticausativeProperty
  deriving Repr, DecidableEq

/-- A single resultative example with judgment data. -/
structure ResultativeDatum where
  /-- Example identifier -/
  exId : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Acceptability
  /-- Which resultative subtype -/
  resType : ResultativeType
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! ### Causative property resultatives (§2, ex. 5a, 7a) -/

def hammer_flat : ResultativeDatum :=
  { exId := "1a"
  , sentence := "She hammered the metal flat"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become flat" }

def wipe_clean : ResultativeDatum :=
  { exId := "1b"
  , sentence := "He wiped the table clean"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become clean" }

def paint_red : ResultativeDatum :=
  { exId := "1c"
  , sentence := "They painted the house red"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become red" }

/-! ### Causative path resultatives (§2, ex. 5b) -/

def kick_into_field : ResultativeDatum :=
  { exId := "2a"
  , sentence := "She kicked the ball into the field"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to go to goal" }

def push_off_table : ResultativeDatum :=
  { exId := "2b"
  , sentence := "He pushed the glass off the table"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to move from source" }

/-! ### Noncausative property resultatives (§2, ex. 6a) -/

def freeze_solid : ResultativeDatum :=
  { exId := "3a"
  , sentence := "The river froze solid"
  , judgment := .ok
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: theme becomes result state" }

def swing_shut : ResultativeDatum :=
  { exId := "3b"
  , sentence := "The gate swung shut"
  , judgment := .ok
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: unaccusative verb + result state" }

/-! ### Noncausative path resultatives (§2, ex. 6b) -/

def roll_into_field : ResultativeDatum :=
  { exId := "4a"
  , sentence := "The ball rolled into the field"
  , judgment := .ok
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves along path" }

def slide_off_table : ResultativeDatum :=
  { exId := "4b"
  , sentence := "The book slid off the table"
  , judgment := .ok
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves from source" }

/-! ### Fake reflexive resultatives (§5, ex. 9) -/

def laugh_silly : ResultativeDatum :=
  { exId := "5a"
  , sentence := "She laughed herself silly"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: intransitive verb + reflexive + result" }

def drink_sick : ResultativeDatum :=
  { exId := "5b"
  , sentence := "He drank himself sick"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: verb lacks patient; construction adds it" }

def run_ragged : ResultativeDatum :=
  { exId := "5c"
  , sentence := "She ran herself ragged"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: unergative verb + reflexive + result" }

/-! ### Aspectual contrasts (§4, Principle 27) -/

/-- An aspectual contrast pair. -/
structure AspectualContrast where
  /-- Sentence with temporal adverbial -/
  sentence : String
  /-- Acceptability -/
  judgment : Acceptability
  /-- Which adverbial type -/
  adverbialType : String
  /-- Description -/
  description : String
  deriving Repr, BEq

def hammer_flat_in : AspectualContrast :=
  { sentence := "She hammered the metal flat in an hour"
  , judgment := .ok
  , adverbialType := "in-adverbial"
  , description := "resultative is telic: in-adverbial OK" }

def hammer_flat_for : AspectualContrast :=
  { sentence := "*She hammered the metal flat for an hour"
  , judgment := .unacceptable
  , adverbialType := "for-adverbial"
  , description := "resultative is telic: for-adverbial bad" }

def hammer_bare_for : AspectualContrast :=
  { sentence := "She hammered the metal for an hour"
  , judgment := .ok
  , adverbialType := "for-adverbial"
  , description := "bare activity is atelic: for-adverbial OK" }

def hammer_bare_in : AspectualContrast :=
  { sentence := "??She hammered the metal in an hour"
  , judgment := .marginal
  , adverbialType := "in-adverbial"
  , description := "bare activity is atelic: in-adverbial degraded" }

/-! ### Unacceptable resultatives (§6, semantic coherence violations) -/

def eat_full : ResultativeDatum :=
  { exId := "7a"
  , sentence := "*She ate the food full"
  , judgment := .unacceptable
  , resType := .causativeProperty
  , phenomenon := "semantic incoherence: patient of eat ≠ entity that becomes full" }

def sleep_flat : ResultativeDatum :=
  { exId := "7b"
  , sentence := "*She slept the bed flat"
  , judgment := .unacceptable
  , resType := .causativeProperty
  , phenomenon := "semantic incoherence: sleep cannot cause flatness" }

/-! ### Aggregate data -/

def allExamples : List ResultativeDatum :=
  [ hammer_flat, wipe_clean, paint_red
  , kick_into_field, push_off_table
  , freeze_solid, swing_shut
  , roll_into_field, slide_off_table
  , laugh_silly, drink_sick, run_ragged
  , eat_full, sleep_flat ]

def aspectualContrasts : List AspectualContrast :=
  [ hammer_flat_in, hammer_flat_for, hammer_bare_for, hammer_bare_in ]

/-! ### Empirical verification -/

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
    (allExamples.any (·.judgment == .ok)) = true ∧
    (allExamples.any (·.judgment == .unacceptable)) = true := by
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
    hammer_flat_in.judgment == .ok ∧
    hammer_flat_for.judgment == .unacceptable := by
  constructor <;> native_decide

/-- Atelic bare activities accept for-adverbials. -/
theorem atelic_adverbial_pattern :
    hammer_bare_for.judgment == .ok := by
  native_decide

end Phenomena.Constructions.Resultatives.Studies.GoldbergJackendoff2004
