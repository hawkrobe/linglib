import Linglib.Syntax.ConstructionGrammar.Resultatives
import Linglib.Features.Acceptability

/-!
# [goldberg-jackendoff-2004]: The English Resultative as a Family of Constructions
[goldberg-jackendoff-2004]

Paper data and per-datum verifications for [goldberg-jackendoff-2004].
The construction-theoretic primitives (`ResultativeSubconstruction`,
`SubeventDesc`, the fusion machinery, the universal-quantifier theorems)
live in `Syntax/ConstructionGrammar/Resultatives.lean`, which
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

- The paper's eight resultative *entries* (`hammerFlat`, `pushOffSofa`, …)
  and the `allEntries` list — concrete data points the paper discusses.
- Per-datum verification theorems demonstrating the paper's data is
  consistent with the construction theory.
- A separate empirical-data layer (`ResultativeType`, `ResultativeDatum`,
  `allExamples`, `aspectualContrasts`) holding theory-neutral grammaticality
  judgments and aspectual contrasts drawn from the paper's examples
  (5–9, 23–24, 45, 97).
-/

namespace GoldbergJackendoff2004

open ConstructionGrammar
open ConstructionGrammar.Resultatives
open ArgumentStructure
open Features

/-! ## Empirical data: resultative entries -/

def hammerFlat : ResultativeEntry :=
  { verb := "hammer", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "She hammered the metal"
  , levinClass := .hit }               -- Levin §18.1

def pushOffSofa : ResultativeEntry :=
  { verb := "push", subconstruction := .causativePath
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "Bill pushed Harry" (ex. 24b)
  , levinClass := .pushPull }          -- Levin §12

def freezeSolid : ResultativeEntry :=
  { verb := "freeze", subconstruction := .noncausativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .achievement
  , levinClass := .otherCoS }          -- Levin §45.4

def rollDownHill : ResultativeEntry :=
  { verb := "roll", subconstruction := .noncausativePath
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , levinClass := .mannerOfMotion }    -- Levin §51.3; ex. 97c

def drinkDry : ResultativeEntry :=
  { verb := "drink", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .unselected  -- cf. *"They drank the pub" (ex. 8a)
  , levinClass := .eat }                 -- Levin §39.1

def yellHoarse : ResultativeEntry :=
  { verb := "yell", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .fakeReflexive  -- cf. *"We yelled Harry hoarse" (ex. 9a)
  , levinClass := .mannerOfSpeaking }        -- Levin §37.3

def bleedToDeath : ResultativeEntry :=
  { verb := "bleed", subconstruction := .noncausativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , levinClass := .substanceEmission } -- Levin §43.4; ex. 45c

def wipeClean : ResultativeEntry :=
  { verb := "wipe", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "He wiped the table"
  , levinClass := .wipe }              -- Levin §10.4

/-- All resultative entries. -/
def allEntries : List ResultativeEntry :=
  [ hammerFlat, pushOffSofa, freezeSolid, rollDownHill
  , drinkDry, yellHoarse, bleedToDeath, wipeClean ]

/-! ## Per-datum verification theorems -/

-- Subconstruction classification
theorem hammerFlat_is_causativeProperty :
    hammerFlat.subconstruction = .causativeProperty := rfl

theorem pushOffSofa_is_causativePath :
    pushOffSofa.subconstruction = .causativePath := rfl

theorem freezeSolid_is_noncausativeProperty :
    freezeSolid.subconstruction = .noncausativeProperty := rfl

theorem rollDownHill_is_noncausativePath :
    rollDownHill.subconstruction = .noncausativePath := rfl

-- Subevent relations: all core entries default to MEANS
theorem hammerFlat_means : hammerFlat.subeventRelation = .means := rfl
theorem freezeSolid_means : freezeSolid.subeventRelation = .means := rfl
theorem drinkDry_means : drinkDry.subeventRelation = .means := rfl

/-- All four core subconstructions use MEANS (§3, summary 97a–d).
    RESULT is reserved for sound-emission and disappearance subconstructions. -/
theorem all_core_entries_use_means :
    allEntries.all (·.subeventRelation == .means) = true := by
  decide

-- Derived subevent structure: CAUSE follows from subconstruction

/-- Causative entries have CAUSE in their derived constructional subevent. -/
theorem causative_entries_have_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  decide

/-- Noncausative entries lack CAUSE in their derived constructional subevent. -/
theorem noncausative_entries_no_cause :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => !e.dualSubevent.constructional.hasCause) = true := by
  decide

/-- All derived constructional subevents have BECOME. -/
theorem all_constructional_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  decide

-- Object selection: intransitive entries have no object selection

/-- Noncausative (intransitive) entries have no object selection. -/
theorem noncausative_no_object_selection :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => e.objectSelection == none) = true := by
  decide

/-- All causative entries specify an object selection mode. -/
theorem causative_have_object_selection :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (λ e => e.objectSelection.isSome) = true := by
  decide

-- Aspectual predictions

/-- All entries with bounded RP are telic. -/
theorem bounded_entries_telic :
    (allEntries.filter (·.rpBoundedness == .bounded)).all
      (λ e => (resultativeAspect e.rpBoundedness).telicity == .telic) = true := by
  decide

/-! ### Theorems migrated from `Causation.Resultatives`

These theorems quantify over `allEntries` (paper-specific data) and
therefore belong with the paper, not in the Theory layer. -/

/-- All causative entries in the data have CAUSE. -/
theorem causative_resultative_has_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  decide

/-- MEANS-relation causative entries all have CAUSE. -/
theorem causative_means_have_cause :
    (allEntries.filter (λ e =>
      e.subconstruction.isCausative && e.subeventRelation == .means
    )).all (·.dualSubevent.constructional.hasCause) = true := by
  decide

/-- Activity verbs in the data with bounded RPs become accomplishments. -/
theorem activity_entries_become_accomplishments :
    (allEntries.filter (λ e =>
      e.bareVerbClass == .activity && e.rpBoundedness == .bounded
    )).all (λ e =>
      resultativeVendlerClass e.rpBoundedness == .accomplishment
    ) = true := by
  decide

/-- All resultative entries have BECOME. -/
theorem all_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  decide

/-! ## Per-entry verb class participation

The construction-verb interaction across the Levin classes of the
paper's example verbs: contact/force verbs (hammer, push),
change-of-state verbs (freeze), motion verbs (roll), speech and
emission verbs (yell, bleed), and surface-contact verbs (wipe). -/

/-- All entries acquire CoS from the construction, regardless of verb class. -/
theorem all_entries_fused_cos :
    allEntries.all (λ e => e.fusedMC.changeOfState) = true := by
  decide

/-- All entries participate in the resultative alternation (none are instrument-spec). -/
theorem all_entries_resultative_alternation :
    allEntries.all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .resultative) = true := by
  decide

/-- Causative entries all acquire the causative alternation. -/
theorem causative_entries_causative_alternation :
    (allEntries.filter (·.subconstruction.isCausative)).all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .causativeInchoative) = true := by
  decide

/-- Noncausative entries do NOT acquire the causative alternation
    (unless the verb already has causation — freeze/otherCoS does). -/
theorem noncausative_entries_no_new_causation :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .causativeInchoative
      = e.verbMC.predictedAlternation .causativeInchoative) = true := by
  decide

/-- Hammer (hit-class): no CoS or causation alone → both added by causative construction. -/
theorem hammer_gains_cos_causation :
    hammerFlat.verbMC.changeOfState = false ∧
    hammerFlat.verbMC.causation = false ∧
    hammerFlat.fusedMC.changeOfState = true ∧
    hammerFlat.fusedMC.causation = true := by
  constructor; decide
  constructor; decide
  constructor <;> decide

/-- Freeze (otherCoS): already has CoS + causation → construction doesn't change profile. -/
theorem freeze_already_has_cos :
    freezeSolid.verbMC.changeOfState = true ∧
    freezeSolid.verbMC.causation = true ∧
    freezeSolid.fusedMC = freezeSolid.verbMC := by
  constructor; decide
  constructor <;> decide

/-- Roll (manner-of-motion): gains CoS from construction; no causation (noncausative). -/
theorem roll_gains_cos_only :
    rollDownHill.verbMC.changeOfState = false ∧
    rollDownHill.fusedMC.changeOfState = true ∧
    rollDownHill.fusedMC.causation = false := by
  constructor; decide
  constructor <;> decide

/-- Yell (manner of speaking): pure manner verb — construction adds CoS + causation. -/
theorem yell_gains_cos_causation :
    yellHoarse.verbMC.changeOfState = false ∧
    yellHoarse.verbMC.causation = false ∧
    yellHoarse.fusedMC.changeOfState = true ∧
    yellHoarse.fusedMC.causation = true := by
  constructor; decide
  constructor; decide
  constructor <;> decide

/-- Wipe (wipe-class): already has full profile — construction is redundant. -/
theorem wipe_already_has_everything :
    wipeClean.verbMC.changeOfState = true ∧
    wipeClean.verbMC.causation = true ∧
    wipeClean.fusedMC = wipeClean.verbMC := by
  constructor; decide
  constructor <;> decide

/-! ## Empirical data: grammaticality judgments

Theory-neutral grammaticality judgments and aspectual contrasts drawn
from §§2–8 of the paper. These provide the shared data layer that
other studies (Dendikken, Tay, Levin) connect to their own analyses. -/

open Features (Acceptability)

/-- What type of resultative is exemplified.

Extends the paper's 2×2 matrix (§2) with fake reflexives (§5) and
anticausative property resultatives ([levin-2026]). -/
inductive ResultativeType where
  | causativeProperty
  | causativePath
  | noncausativeProperty
  | noncausativePath
  | fakeReflexive
  /-- Anticausative: verb doesn't alternate alone; construction licenses it
      ([levin-2026]). Distinct from `noncausativeProperty` (e.g., *freeze
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

/-! ### Causative property resultatives (exx. 5a, 7a, 8a; §6.2) -/

def hammer_flat : ResultativeDatum :=
  { exId := "5a"
  , sentence := "Herman hammered the metal flat"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become flat" }

def water_flat : ResultativeDatum :=
  { exId := "7a"
  , sentence := "The gardener watered the flowers flat"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "selected transitive: verb independently takes the object" }

def drink_dry : ResultativeDatum :=
  { exId := "8a"
  , sentence := "They drank the pub dry"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "unselected transitive: object licensed only by the construction" }

def wipe_clean : ResultativeDatum :=
  { exId := "§6.2"
  , sentence := "She wiped the table clean"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "semantic coherence: wiped surface construable as patient" }

/-! ### Causative path resultatives (exx. 5b, 7b, 8b) -/

def laugh_off_stage : ResultativeDatum :=
  { exId := "5b"
  , sentence := "The critics laughed the play off the stage"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to go along path" }

def break_into_pieces : ResultativeDatum :=
  { exId := "7b"
  , sentence := "Bill broke the bathtub into pieces"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "selected transitive with path RP" }

def talk_into_stupor : ResultativeDatum :=
  { exId := "8b"
  , sentence := "The professor talked us into a stupor"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "unselected transitive with path RP" }

/-! ### Noncausative property resultatives (exx. 6a, 45c) -/

def freeze_solid : ResultativeDatum :=
  { exId := "6a"
  , sentence := "The pond froze solid"
  , judgment := .ok
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: theme becomes result state" }

def bleed_to_death : ResultativeDatum :=
  { exId := "45c"
  , sentence := "The tiger bled to death"
  , judgment := .ok
  , resType := .noncausativeProperty
  , phenomenon := "noncausal property resultative: patient subject, coherent roles" }

/-! ### Noncausative path resultatives (exx. 6b, 97c) -/

def roll_out_of_room : ResultativeDatum :=
  { exId := "6b"
  , sentence := "Bill rolled out of the room"
  , judgment := .ok
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves along path" }

def rumble_into_station : ResultativeDatum :=
  { exId := "97c"
  , sentence := "The truck rumbled into the station"
  , judgment := .ok
  , resType := .noncausativePath
  , phenomenon := "sound-emission path resultative: sound RESULTS from motion" }

/-! ### Fake reflexive resultatives (§2, ex. 9a) -/

def yell_hoarse : ResultativeDatum :=
  { exId := "9a"
  , sentence := "We yelled ourselves hoarse"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: intransitive verb + reflexive + result" }

def yell_ourselves : ResultativeDatum :=
  { exId := "9a-unsel"
  , sentence := "*We yelled ourselves"
  , judgment := .unacceptable
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive object is unselected: bad without the RP" }

def yell_harry_hoarse : ResultativeDatum :=
  { exId := "9a-alt"
  , sentence := "*We yelled Harry hoarse"
  , judgment := .unacceptable
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive does not alternate with other NPs" }

/-! ### Aspectual contrasts (§4.1, exx. 23–24) -/

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

def hammer_ever_flatter : AspectualContrast :=
  { sentence := "For hours, Bill hammered the metal ever flatter"
  , judgment := .ok
  , adverbialType := "for-adverbial"
  , description := "ex. 23b: non-end-bounded AP RP → atelic, for-adverbial OK" }

def float_into_cave_for : AspectualContrast :=
  { sentence := "*Bill floated into the cave for hours"
  , judgment := .unacceptable
  , adverbialType := "for-adverbial"
  , description := "ex. 24a: end-bounded PP RP → telic, for-adverbial bad (nonrepetitive)" }

def float_down_river_for : AspectualContrast :=
  { sentence := "Bill floated down the river for hours"
  , judgment := .ok
  , adverbialType := "for-adverbial"
  , description := "ex. 24c: non-end-bounded PP RP → atelic, for-adverbial OK" }

def push_off_sofa_for : AspectualContrast :=
  { sentence := "*Bill pushed Harry off the sofa for hours"
  , judgment := .unacceptable
  , adverbialType := "for-adverbial"
  , description := "ex. 24b: end-bounded PP RP → telic, for-adverbial bad (nonrepetitive)" }

def push_along_trail_for : AspectualContrast :=
  { sentence := "Bill pushed Harry along the trail for hours"
  , judgment := .ok
  , adverbialType := "for-adverbial"
  , description := "ex. 24d: non-end-bounded PP RP → atelic, for-adverbial OK" }

/-! ### Semantic coherence violations (§6.2, ex. 45) -/

def yell_hoarse_bare : ResultativeDatum :=
  { exId := "45a"
  , sentence := "*She yelled hoarse"
  , judgment := .unacceptable
  , resType := .noncausativeProperty
  , phenomenon := "semantic incoherence: agent subject of yell ≠ patient of BECOME" }

def cry_to_sleep : ResultativeDatum :=
  { exId := "45b"
  , sentence := "*Ted cried to sleep"
  , judgment := .unacceptable
  , resType := .noncausativeProperty
  , phenomenon := "semantic incoherence: agent subject of cry ≠ patient of BECOME" }

/-! ### Aggregate data -/

def allExamples : List ResultativeDatum :=
  [ hammer_flat, water_flat, drink_dry, wipe_clean
  , laugh_off_stage, break_into_pieces, talk_into_stupor
  , freeze_solid, bleed_to_death
  , roll_out_of_room, rumble_into_station
  , yell_hoarse, yell_ourselves, yell_harry_hoarse
  , yell_hoarse_bare, cry_to_sleep ]

def aspectualContrasts : List AspectualContrast :=
  [ hammer_ever_flatter, float_into_cave_for, float_down_river_for
  , push_off_sofa_for, push_along_trail_for ]

/-! ### Empirical verification -/

/-- All four resultative types are attested in the data. -/
theorem has_all_resultative_types :
    (allExamples.any (·.resType == .causativeProperty)) = true ∧
    (allExamples.any (·.resType == .causativePath)) = true ∧
    (allExamples.any (·.resType == .noncausativeProperty)) = true ∧
    (allExamples.any (·.resType == .noncausativePath)) = true ∧
    (allExamples.any (·.resType == .fakeReflexive)) = true := by
  constructor; decide
  constructor; decide
  constructor; decide
  constructor; decide
  decide

/-- Both grammatical and ungrammatical examples are represented. -/
theorem has_both_judgments :
    (allExamples.any (·.judgment == .ok)) = true ∧
    (allExamples.any (·.judgment == .unacceptable)) = true := by
  constructor; decide
  decide

/-- The for-adverbial data attests both telic (bad) and atelic (good)
resultatives — boundedness of the RP, not resultativehood, decides
telicity. -/
theorem aspectual_both_outcomes :
    (aspectualContrasts.any (·.judgment == .ok)) = true ∧
    (aspectualContrasts.any (·.judgment == .unacceptable)) = true := by
  constructor; decide
  decide

/-- End-bounded path RPs are telic (for-adverbial bad); the non-end-bounded
counterpart with the same verb is atelic (ex. 24a vs. 24c). -/
theorem telic_adverbial_pattern :
    float_into_cave_for.judgment == .unacceptable ∧
    float_down_river_for.judgment == .ok := by
  constructor <;> decide

/-- Non-end-bounded AP RPs create atelic property resultatives (ex. 23b). -/
theorem atelic_adverbial_pattern :
    hammer_ever_flatter.judgment == .ok := by
  decide

end GoldbergJackendoff2004
