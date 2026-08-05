import Linglib.Syntax.ConstructionGrammar.Resultatives
import Linglib.Data.Examples.GoldbergJackendoff2004

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
- Derived-prediction theorems: the theory's fusion and aspect machinery,
  applied to each entry's independent classification, reproduces the
  paper's claims about CAUSE/BECOME profiles, telicity, and alternations.
- A typed empirical-data layer (`ResultativeType`, `ResultativeDatum`,
  `allExamples`, `aspectualContrasts`) projected from the paper's
  generated example rows (`Data.Examples.GoldbergJackendoff2004`:
  exx. 5–9, 23–24, 45, 97c, §6.2) — the shared data other studies
  (Dendikken, Tay, Levin) connect to their own analyses.
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

/-! ## Derived predictions

Each theorem runs the theory's machinery (`dualSubevent`, `fusedMC`,
`resultativeAspect`) on the entries' independent classifications and
checks the derived profile against the paper's claim. Encoding
invariants of the data itself are anonymous `example`s. -/

-- All core entries use the default MEANS relation (§3, summary 97a–d);
-- RESULT is reserved for sound-emission and disappearance cases.
example : allEntries.all (·.subeventRelation == .means) = true := by decide

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

-- Encoding invariants: causative (transitive) entries carry an object
-- selection mode; noncausative (intransitive) entries carry none.
example :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (λ e => e.objectSelection.isSome) = true := by decide
example :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => e.objectSelection == none) = true := by decide

-- Aspectual predictions

/-- All entries with bounded RP are telic. -/
theorem bounded_entries_telic :
    (allEntries.filter (·.rpBoundedness == .bounded)).all
      (λ e => (resultativeAspect e.rpBoundedness).telicity == .telic) = true := by
  decide

/-- Activity verbs in the data with bounded RPs become accomplishments. -/
theorem activity_entries_become_accomplishments :
    (allEntries.filter (λ e =>
      e.bareVerbClass == .activity && e.rpBoundedness == .bounded
    )).all (λ e =>
      resultativeVendlerClass e.rpBoundedness == .accomplishment
    ) = true := by
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

The stimuli live as generated rows in
`Data.Examples.GoldbergJackendoff2004` (from the per-paper JSON); this
layer projects each row into a typed datum carrying the study's
classification. Other studies (Dendikken, Tay, Levin) connect to this
shared data through the datum layer or the rows directly. -/

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
  /-- Example identifier (the paper's own example label) -/
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

/-- Project a generated example row into a typed datum. Sentence, label,
and judgment come from the row; the `ResultativeType` classification and
phenomenon gloss are the study's reading (mirrored in the row's
`paperFeatures`). -/
def ResultativeDatum.ofExample (ex : Data.Examples.LinguisticExample)
    (resType : ResultativeType) (phenomenon : String) : ResultativeDatum :=
  { exId := ex.source.paperLabel
  , sentence := ex.primaryText
  , judgment := ex.judgment
  , resType := resType
  , phenomenon := phenomenon }

/-! ### Causative property resultatives (exx. 5a, 7a, 8a; §6.2) -/

def hammer_flat : ResultativeDatum :=
  .ofExample Examples.gj2004_5a .causativeProperty
    "causative + property RP: agent causes patient to become flat"

def water_flat : ResultativeDatum :=
  .ofExample Examples.gj2004_7a .causativeProperty
    "selected transitive: verb independently takes the object"

def drink_dry : ResultativeDatum :=
  .ofExample Examples.gj2004_8a .causativeProperty
    "unselected transitive: object licensed only by the construction"

def wipe_clean : ResultativeDatum :=
  .ofExample Examples.gj2004_wipe .causativeProperty
    "semantic coherence: wiped surface construable as patient"

/-! ### Causative path resultatives (exx. 5b, 7b, 8b) -/

def laugh_off_stage : ResultativeDatum :=
  .ofExample Examples.gj2004_5b .causativePath
    "causative + path RP: agent causes theme to go along path"

def break_into_pieces : ResultativeDatum :=
  .ofExample Examples.gj2004_7b .causativePath
    "selected transitive with path RP"

def talk_into_stupor : ResultativeDatum :=
  .ofExample Examples.gj2004_8b .causativePath
    "unselected transitive with path RP"

/-! ### Noncausative property resultatives (exx. 6a, 45c) -/

def freeze_solid : ResultativeDatum :=
  .ofExample Examples.gj2004_6a .noncausativeProperty
    "noncausative + property RP: theme becomes result state"

def bleed_to_death : ResultativeDatum :=
  .ofExample Examples.gj2004_45c .noncausativeProperty
    "noncausal property resultative: patient subject, coherent roles"

/-! ### Noncausative path resultatives (exx. 6b, 97c) -/

def roll_out_of_room : ResultativeDatum :=
  .ofExample Examples.gj2004_6b .noncausativePath
    "noncausative + path RP: theme moves along path"

def rumble_into_station : ResultativeDatum :=
  .ofExample Examples.gj2004_97c .noncausativePath
    "sound-emission path resultative: sound RESULTS from motion"

/-! ### Fake reflexive resultatives (§2, ex. 9a)

The starred diagnostics — `*We yelled ourselves` (unselected without
the RP) and `*We yelled Harry hoarse` (no alternation with other NPs) —
live as the row's `alternatives`. -/

def yell_hoarse : ResultativeDatum :=
  .ofExample Examples.gj2004_9a .fakeReflexive
    "fake reflexive: intransitive verb + reflexive + result"

/-! ### Aspectual contrasts (§4.1, exx. 23–24) -/

/-- An aspectual contrast pair. -/
structure AspectualContrast where
  /-- Sentence with temporal adverbial -/
  sentence : String
  /-- Acceptability -/
  judgment : Judgment
  /-- Which adverbial type -/
  adverbialType : String
  /-- Description -/
  description : String
  deriving Repr, BEq

/-- Project a generated example row into an aspectual contrast. -/
def AspectualContrast.ofExample (ex : Data.Examples.LinguisticExample)
    (description : String) : AspectualContrast :=
  { sentence := ex.primaryText
  , judgment := ex.judgment
  , adverbialType := "for-adverbial"
  , description := description }

def heat_hotter : AspectualContrast :=
  .ofExample Examples.gj2004_23a
    "ex. 23a: non-end-bounded AP RP → atelic, for-adverbial OK"

def hammer_ever_flatter : AspectualContrast :=
  .ofExample Examples.gj2004_23b
    "ex. 23b: non-end-bounded AP RP → atelic, for-adverbial OK"

def weave_longer : AspectualContrast :=
  .ofExample Examples.gj2004_23c
    "ex. 23c: non-end-bounded AP RP → atelic, for-adverbial OK"

def float_into_cave_for : AspectualContrast :=
  .ofExample Examples.gj2004_24a
    "ex. 24a: end-bounded PP RP → telic, for-adverbial bad (nonrepetitive)"

def push_off_sofa_for : AspectualContrast :=
  .ofExample Examples.gj2004_24b
    "ex. 24b: end-bounded PP RP → telic, for-adverbial bad (nonrepetitive)"

def float_down_river_for : AspectualContrast :=
  .ofExample Examples.gj2004_24c
    "ex. 24c: non-end-bounded PP RP → atelic, for-adverbial OK"

def push_along_trail_for : AspectualContrast :=
  .ofExample Examples.gj2004_24d
    "ex. 24d: non-end-bounded PP RP → atelic, for-adverbial OK"

/-! ### Semantic coherence violations (§6.2, ex. 45) -/

def yell_hoarse_bare : ResultativeDatum :=
  .ofExample Examples.gj2004_45a .noncausativeProperty
    "semantic incoherence: agent subject of yell ≠ patient of BECOME"

def cry_to_sleep : ResultativeDatum :=
  .ofExample Examples.gj2004_45b .noncausativeProperty
    "semantic incoherence: agent subject of cry ≠ patient of BECOME"

/-! ### Aggregate data -/

def allExamples : List ResultativeDatum :=
  [ hammer_flat, water_flat, drink_dry, wipe_clean
  , laugh_off_stage, break_into_pieces, talk_into_stupor
  , freeze_solid, bleed_to_death
  , roll_out_of_room, rumble_into_station
  , yell_hoarse
  , yell_hoarse_bare, cry_to_sleep ]

def aspectualContrasts : List AspectualContrast :=
  [ heat_hotter, hammer_ever_flatter, weave_longer
  , float_into_cave_for, push_off_sofa_for
  , float_down_river_for, push_along_trail_for ]

end GoldbergJackendoff2004
