import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Semantics.ArgumentStructure.MeaningComponents

/-!
# Diathesis Alternations
[levin-1993]

Twenty-five curated diathesis alternations from [levin-1993] Part One,
the prediction map from `MeaningComponents`, the per-class participation
profile, and structural theorems characterising how alternation
participation interacts with `MeaningComponents.fuse`.

## Provenance

Moved from `Core/Lexical/DiathesisAlternation.lean` in the cleanup that
dissolved `Core/Lexical/`. Sibling of `LevinClass.lean`, `MeaningComponents.lean`,
`LevinTheory.lean`, `LevinClassProfiles.lean` — all paper-anchored on
[levin-1993] and not theory-neutral substrate.

## Selection caveat

The 25 alternations chosen here are **the formaliser's selection** of
"diagnostically active" alternations from Levin's ~79 in Part One.
Levin's monograph lists many narrower alternations as data/prose; the
selection here covers what's needed to discriminate the major verb
classes per Levin's Introduction. This is NOT Levin's own claim about
which alternations are diagnostically active — verify the curation
against the empirical needs of any downstream consumer.

UNVERIFIED: Per-alternation section numbers (e.g., `§1.1.2.1`, `§2.1`,
`§7.4`) cited from memory throughout. Verify against published
[levin-1993] before treating as authoritative.

## Sections

- §1a `AlternationFamily` — 6 chapter-anchored families
- §1b `DiathesisAlternation` — 25 alternation types + family classifier
- §2 `MeaningComponents.predictedAlternation` — feature-derived predictions
- §3 Structural theorems on `fuse` × `predictedAlternation`
- §4 `LevinClass.participatesIn` — full participation profile (component-derived + class-specific overrides)
- §5 Canonical diagnostic theorems (*break*/*cut*/*hit*/*touch* + cross-class predictions)
-/

namespace ArgumentStructure

-- ════════════════════════════════════════════════════
-- § 1a. Alternation Families
-- ════════════════════════════════════════════════════

/-- Classification of diathesis alternations by the chapter of
    [levin-1993] Part One where they are primarily discussed.

    Organizational grouping for the curated 25-alternation enum;
    the remaining ~50 narrow alternations from Part One are documented
    as data/prose, not as enum constructors.

    UNVERIFIED: Chapter assignments cited from memory. -/
inductive AlternationFamily where
  /-- Ch 1: Transitivity alternations — changes in the number of arguments
      (causative/inchoative, induced action, middle, conative, object drop). -/
  | transitivity
  /-- Ch 2: Alternations involving arguments within the VP — rearrangement
      of internal arguments (dative, benefactive, locative, swarm, etc.). -/
  | vpInternal
  /-- Ch 3: Oblique subject alternations — non-agent subjects
      (instrument subject). -/
  | obliqueSubject
  /-- Ch 5: Passive — verbal and prepositional passives. -/
  | passive
  /-- Ch 6: Alternations involving postverbal subjects — there-insertion,
      locative inversion (unaccusative diagnostics). -/
  | postverbalSubject
  /-- Ch 7: Other constructions — way construction, cognate object,
      resultative, directional phrase. -/
  | otherConstructions
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 1b. Diathesis Alternation Diagnostics
-- ════════════════════════════════════════════════════

/-- Curated diathesis alternations from [levin-1993] Part One.

    The first four (causativeInchoative / inducedAction / middle / conative)
    are the canonical diagnostics from the Introduction; others are from
    specific chapters. Each is classified by `AlternationFamily`.

    UNVERIFIED: Per-constructor section numbers cited from memory. -/
inductive DiathesisAlternation where
  -- Transitivity alternations (Ch 1)
  /-- *she broke the vase* / *the vase broke*. Diagnoses causation + CoS. -/
  | causativeInchoative
  /-- *The scientist ran the rats through the maze* ([levin-1993] §1.1.2.2).
      Causative use of intransitive manner-of-motion verbs. -/
  | inducedAction
  /-- *the bread cuts easily*. Diagnoses change of state. -/
  | middle
  /-- *I cut at the bread*. Diagnoses contact + motion. -/
  | conative
  /-- *heat radiates from the sun* / *the sun radiates heat*.
      Substance emission verbs. -/
  | substanceSource
  /-- *Mike ate the cake* / *Mike ate*. Activity verbs (eat, read, cook, ...).
      The intransitive has an unexpressed but understood indefinite object. -/
  | unspecifiedObject
  /-- *Bill waved his hand* / *Bill waved*. Body-part verbs
      where the object names the moved body part. -/
  | understoodBodyPartObject
  /-- *Bill washed himself* / *Bill washed*. Grooming/body-care verbs
      where the reflexive object can be dropped. -/
  | understoodReflexiveObject
  /-- *Anne met Cathy* / *Anne and Cathy met*. Social interaction verbs.
      Intransitive paraphrasable as transitive with *each other*. -/
  | understoodReciprocalObject
  -- VP-internal alternations (Ch 2)
  /-- *give NP NP* / *give NP to NP*. Give/send class. -/
  | dative
  /-- *Martha carved a toy for the baby* / *Martha carved the baby a toy*.
      Verbs of obtaining and creation. -/
  | benefactive
  /-- *spray paint on wall* / *spray wall with paint*. Spray/load class. -/
  | locative
  /-- *I hit him on the arm* / *I hit his arm*. Diagnoses contact. -/
  | bodyPartPossessorAscension
  /-- *Bees swarmed in the garden* / *The garden swarmed with bees*.
      Intransitive locative alternation for verbs of spatial configuration. -/
  | swarm
  /-- *Martha carved a toy out of wood* / *Martha carved the wood into a toy*.
      Build/creation verbs. -/
  | materialProduct
  /-- *the witch turned the prince into a frog*.
      Complete change of entity type. Turn/convert verbs. -/
  | totalTransformation
  -- Oblique subject alternations (Ch 3)
  /-- *David broke the window with a hammer* / *the hammer broke the window*.
      Intermediary instruments can become subjects with externally caused verbs. -/
  | instrumentSubject
  -- Passive (Ch 5)
  /-- *the window was broken (by the boy)*.
      Fundamental voice alternation for transitive verbs. -/
  | verbalPassive
  /-- *the bed was slept in*. Passive of intransitive + PP,
      diagnostic for unergative verbs. -/
  | prepositionalPassive
  -- Postverbal subject alternations (Ch 6)
  /-- *a problem developed* / *there developed a problem*.
      Unaccusative diagnostic: existence/appearance verbs. -/
  | thereInsertion
  /-- *an old woman lives in the woods* / *in the woods lives an old woman*.
      Unaccusative diagnostic: existence/spatial configuration verbs. -/
  | locativeInversion
  -- Other constructions (Ch 7)
  /-- *Paul laughed a cheerful laugh* ([levin-1993] §40.2). Unergative
      diagnostic: some agentive intransitives take cognate objects. -/
  | cognateObject
  /-- *The boy pushed his way through the crowd* ([levin-1993] §7.4).
      Unergative and transitive verbs. -/
  | wayConstruction
  /-- *hammer the metal flat*. Available to manner verbs. -/
  | resultative
  /-- *she ran to the store*. Manner-of-motion verbs with
      directional PPs (Talmy's satellite-framing). -/
  | directionalPhrase
  deriving DecidableEq, Repr

/-- Which family of [levin-1993] Part One each alternation belongs to.
    Classifies the 25 curated alternations into 6 families matching
    the chapter structure of Part One. -/
def DiathesisAlternation.family : DiathesisAlternation → AlternationFamily
  -- Ch 1: Transitivity alternations
  | .causativeInchoative | .inducedAction | .middle | .conative
  | .substanceSource | .unspecifiedObject | .understoodBodyPartObject
  | .understoodReflexiveObject | .understoodReciprocalObject => .transitivity
  -- Ch 2: VP-internal alternations
  | .dative | .benefactive | .locative | .bodyPartPossessorAscension
  | .swarm | .materialProduct | .totalTransformation => .vpInternal
  -- Ch 3: Oblique subject alternations
  | .instrumentSubject => .obliqueSubject
  -- Ch 5: Passive
  | .verbalPassive | .prepositionalPassive => .passive
  -- Ch 6: Postverbal subject alternations
  | .thereInsertion | .locativeInversion => .postverbalSubject
  -- Ch 7: Other constructions
  | .cognateObject | .wayConstruction | .resultative
  | .directionalPhrase => .otherConstructions

-- ════════════════════════════════════════════════════
-- § 2. Component-Derived Alternation Prediction
-- ════════════════════════════════════════════════════

/-- Predicted alternation participation derived from meaning components.

    The core claim of [levin-1993]: meaning components — diagnosed by
    alternation participation — form the bridge between verb semantics and
    verb syntax. Each diagnostic alternation corresponds to a specific
    configuration of meaning components:

    | Alternation | Required components |
    |---|---|
    | Causative/inchoative | changeOfState ∧ causation ∧ ¬instrumentSpec |
    | Middle | changeOfState |
    | Conative | contact ∧ motion |
    | Body-part possessor ascension | contact |
    | Instrument subject | causation ∧ ¬instrumentSpec |
    | Resultative | changeOfState ∧ ¬instrumentSpec (manner verbs) |

    The remaining alternations are class-specific rather than
    component-derived. -/
def MeaningComponents.predictedAlternation : MeaningComponents → DiathesisAlternation → Bool
  | mc, .causativeInchoative => mc.changeOfState && mc.causation && !mc.instrumentSpec
  | mc, .middle => mc.changeOfState
  | mc, .conative => mc.contact && mc.motion
  | mc, .bodyPartPossessorAscension => mc.contact
  | mc, .instrumentSubject => mc.causation && !mc.instrumentSpec
  | mc, .resultative => mc.changeOfState && !mc.instrumentSpec
  -- All remaining alternations are class-specific, not component-derived
  | _, .inducedAction => false
  | _, .substanceSource => false
  | _, .unspecifiedObject => false
  | _, .understoodBodyPartObject => false
  | _, .understoodReflexiveObject => false
  | _, .understoodReciprocalObject => false
  | _, .dative => false
  | _, .benefactive => false
  | _, .locative => false
  | _, .swarm => false
  | _, .materialProduct => false
  | _, .totalTransformation => false
  | _, .verbalPassive => false
  | _, .prepositionalPassive => false
  | _, .thereInsertion => false
  | _, .locativeInversion => false
  | _, .cognateObject => false
  | _, .wayConstruction => false
  | _, .directionalPhrase => false

-- ════════════════════════════════════════════════════
-- § 3. Structural properties of fusion + alternation prediction
-- ════════════════════════════════════════════════════

/-! These theorems characterize how `MeaningComponents.fuse` (componentwise OR)
interacts with `predictedAlternation`. They are stated purely over
`MeaningComponents` — no reference to specific constructions, verb classes,
or empirical data. Construction grammar modules use these as lemmas.

Note: `fuse` is componentwise OR; the substrate's design choice. NOT to be
attributed to Goldberg 1995 specifically (Goldberg's actual constructional
unification is more structured than disjunctive feature OR). -/

/-- **Enabling via CoS + causation**: fusing any verb (without instrumentSpec)
    with any meaning components contributing CoS + causation (without
    instrumentSpec) enables all four instrument-sensitive alternations. -/
theorem fuse_cos_caus_enables (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true)
    (hInstV : v.instrumentSpec = false) (hInstC : c.instrumentSpec = false) :
    let f := v.fuse c
    f.predictedAlternation .causativeInchoative = true ∧
    f.predictedAlternation .middle = true ∧
    f.predictedAlternation .instrumentSubject = true ∧
    f.predictedAlternation .resultative = true := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- **Partial enabling via CoS only**: fusing a verb (without instrumentSpec
    or causation) with meaning components contributing CoS but NOT causation
    enables middle and resultative alternation, but NOT causativeInchoative
    or instrumentSubject. -/
theorem fuse_cos_only_partial (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hNoCaus : c.causation = false)
    (hNoCausV : v.causation = false)
    (hInstV : v.instrumentSpec = false) (hInstC : c.instrumentSpec = false) :
    let f := v.fuse c
    f.predictedAlternation .middle = true ∧
    f.predictedAlternation .resultative = true ∧
    f.predictedAlternation .causativeInchoative = false ∧
    f.predictedAlternation .instrumentSubject = false := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- **instrumentSpec blocks unconditionally**: any meaning components with
    instrumentSpec = true are blocked from causativeInchoative,
    instrumentSubject, and resultative. -/
theorem instrumentSpec_blocks (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .causativeInchoative = false ∧
    mc.predictedAlternation .instrumentSubject = false ∧
    mc.predictedAlternation .resultative = false := by
  rcases mc with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.predictedAlternation]

/-- Corollary: instrumentSpec blocks after ANY fusion, since
    `v.instrumentSpec = true → (v.fuse c).instrumentSpec = true`. -/
theorem instrumentSpec_blocks_after_fuse (v c : MeaningComponents)
    (h : v.instrumentSpec = true) :
    (v.fuse c).predictedAlternation .causativeInchoative = false ∧
    (v.fuse c).predictedAlternation .instrumentSubject = false ∧
    (v.fuse c).predictedAlternation .resultative = false := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- **Monotonicity**: an instrument-free fusion never removes an alternation. -/
theorem fuse_alternation_monotone (v c : MeaningComponents) (alt : DiathesisAlternation)
    (h_no_inst : c.instrumentSpec = false)
    (h_bare : v.predictedAlternation alt = true) :
    (v.fuse c).predictedAlternation alt = true := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  rcases c with ⟨cos', con', mot', caus', inst', man'⟩
  cases alt <;> simp_all [MeaningComponents.predictedAlternation, MeaningComponents.fuse]

/-- **instrumentSpec persists through fusion**: once a verb has instrument
    specificity, no fusion can remove it (`true || b = true`). -/
theorem instrumentSpec_persists (v c : MeaningComponents)
    (h : v.instrumentSpec = true) :
    (v.fuse c).instrumentSpec = true := by
  simp [MeaningComponents.fuse, h]

/-- **Fusion is NOT generally monotone**: when instrumentSpec is added,
    it CAN block an alternation the verb had alone. -/
theorem fuse_not_generally_monotone :
    ∃ (v c : MeaningComponents) (alt : DiathesisAlternation),
      v.predictedAlternation alt = true ∧
      (v.fuse c).predictedAlternation alt = false :=
  ⟨⟨true, false, false, true, false, false⟩,
   ⟨false, false, false, false, true, false⟩,
   .causativeInchoative, rfl, rfl⟩

/-- **instrumentSpec is the sole blocker**: if a verb participates alone
    but NOT after fusion, instrumentSpec must have been introduced. -/
theorem fuse_blocks_only_via_instrumentSpec (v c : MeaningComponents)
    (alt : DiathesisAlternation)
    (h_bare : v.predictedAlternation alt = true)
    (h_fused : (v.fuse c).predictedAlternation alt = false) :
    (v.fuse c).instrumentSpec = true := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  rcases c with ⟨cos', con', mot', caus', inst', man'⟩
  cases alt <;> simp_all [MeaningComponents.predictedAlternation, MeaningComponents.fuse]

-- ════════════════════════════════════════════════════
-- § 4. Per-Class Participation Profile
-- ════════════════════════════════════════════════════

/-- Full alternation profile for a Levin class, combining component-derived
    predictions with class-specific overrides.

    Component-derived: causativeInchoative, middle, conative,
    bodyPartPossessorAscension, instrumentSubject, resultative.

    Class-specific overrides below; these are the formaliser's reading of
    [levin-1993] Part I verb lists and Part II class descriptions.
    UNVERIFIED: Per-class participation rows cited from memory; verify
    against the published monograph. -/
def LevinClass.participatesIn (c : LevinClass) (alt : DiathesisAlternation) : Bool :=
  c.meaningComponents.predictedAlternation alt ||
  match c, alt with
  -- Induced action: manner-of-motion causativization
  | .mannerOfMotion, .inducedAction | .vehicleMotion, .inducedAction
  | .rush, .inducedAction => true
  -- Substance/source: substance emission verbs
  | .substanceEmission, .substanceSource => true
  -- Unspecified object: activity verbs
  | .eat, .unspecifiedObject | .cut, .unspecifiedObject
  | .cooking, .unspecifiedObject | .wipe, .unspecifiedObject
  | .hit, .unspecifiedObject | .mannerOfSpeaking, .unspecifiedObject
  | .build, .unspecifiedObject | .imageCreation, .unspecifiedObject => true
  -- Understood body-part object: body verbs
  | .bodyProcess, .understoodBodyPartObject
  | .bodyInternalMotion, .understoodBodyPartObject => true
  -- Understood reflexive object: grooming verbs
  | .dress, .understoodReflexiveObject => true
  -- Understood reciprocal: social interaction verbs
  | .socialInteraction, .understoodReciprocalObject => true
  -- Dative: give/send/tell classes
  | .give, .dative | .send, .dative | .tell, .dative => true
  -- Benefactive: build/create/obtain verbs
  | .build, .benefactive | .create, .benefactive
  | .knead, .benefactive | .performance, .benefactive
  | .getObtain, .benefactive | .steal, .benefactive => true
  -- Locative: spray/load
  | .sprayLoad, .locative => true
  -- Material/product: build verbs
  | .build, .materialProduct | .knead, .materialProduct
  | .turn, .materialProduct => true
  -- Swarm: intransitive locative alternation
  | .exist, .swarm | .mannerOfMotion, .swarm
  | .bodyInternalMotion, .swarm => true
  -- Total transformation: turn/convert verbs
  | .turn, .totalTransformation => true
  -- Verbal passive: available to most transitive verbs
  -- CoS / causative classes
  | .break_, .verbalPassive | .bend, .verbalPassive
  | .cooking, .verbalPassive | .otherCoS, .verbalPassive
  | .destroy, .verbalPassive => true
  -- Contact / cutting
  | .hit, .verbalPassive | .swat, .verbalPassive
  | .poke, .verbalPassive | .touch, .verbalPassive
  | .cut, .verbalPassive | .carve, .verbalPassive => true
  -- Putting / removing / sending
  | .put, .verbalPassive | .sprayLoad, .verbalPassive
  | .remove, .verbalPassive | .clear, .verbalPassive
  | .wipe, .verbalPassive | .steal, .verbalPassive
  | .send, .verbalPassive | .carry, .verbalPassive => true
  -- Transfer / ingesting
  | .give, .verbalPassive | .eat, .verbalPassive
  | .devour, .verbalPassive => true
  -- Creation / transformation
  | .build, .verbalPassive | .create, .verbalPassive
  | .knead, .verbalPassive | .turn, .verbalPassive => true
  -- Killing
  | .murder, .verbalPassive | .poison, .verbalPassive => true
  -- Perception / psych
  | .see, .verbalPassive | .amuse, .verbalPassive
  | .admire, .verbalPassive => true
  -- Communication
  | .tell, .verbalPassive | .say, .verbalPassive => true
  -- Combining / separating
  | .mix, .verbalPassive | .separate, .verbalPassive => true
  -- Other transitive classes
  | .throw, .verbalPassive | .conceal, .verbalPassive
  | .color, .verbalPassive | .imageCreation, .verbalPassive
  | .hold, .verbalPassive | .pushPull, .verbalPassive
  | .appoint, .verbalPassive | .dress, .verbalPassive => true
  -- Prepositional passive: unergative diagnostic
  | .mannerOfMotion, .prepositionalPassive
  | .exist, .prepositionalPassive
  | .assumePosition, .prepositionalPassive
  | .bodyProcess, .prepositionalPassive
  | .mannerOfSpeaking, .prepositionalPassive => true
  -- There-insertion: existence/appearance verbs
  | .exist, .thereInsertion | .appear, .thereInsertion
  | .soundEmission, .thereInsertion | .lightEmission, .thereInsertion
  | .calibratableCoS, .thereInsertion => true
  -- Locative inversion: same core classes
  | .exist, .locativeInversion | .appear, .locativeInversion
  | .soundEmission, .locativeInversion | .lightEmission, .locativeInversion
  | .mannerOfMotion, .locativeInversion
  | .assumePosition, .locativeInversion => true
  -- Cognate object: unergative verbs. NOT manner of motion: run verbs
  -- have zero-related nominals but do not take cognate objects
  -- ([levin-1993] §51.3.2, ex. 998: *The horse jumped a high jump).
  | .mannerOfSpeaking, .cognateObject
  | .bodyProcess, .cognateObject | .dine, .cognateObject => true
  -- Way construction: manner verbs
  | .mannerOfMotion, .wayConstruction
  | .bodyInternalMotion, .wayConstruction
  | .rush, .wayConstruction => true
  -- Directional phrase: manner-of-motion verbs
  | .mannerOfMotion, .directionalPhrase
  | .vehicleMotion, .directionalPhrase
  | .rush, .directionalPhrase
  | .bodyInternalMotion, .directionalPhrase => true
  | _, _ => false

-- ════════════════════════════════════════════════════
-- § 5. Canonical diagnostic theorems
-- ════════════════════════════════════════════════════

/-! The four verbs *break*, *cut*, *hit*, *touch* are distinguished by exactly
their pattern of alternation participation (per [levin-1993] Introduction). -/

/-- Break participates in causative/inchoative and middle (CoS + causation). -/
theorem break_alternations :
    LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.break_.participatesIn .middle = true
    ∧ LevinClass.break_.participatesIn .conative = false
    ∧ LevinClass.break_.participatesIn .bodyPartPossessorAscension = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Cut participates in middle, conative, and BPPA but NOT causative/inchoative.
    Instrument specification blocks the inchoative ("*The string cut").
    Because *cut* inherently specifies an instrument, it requires an agent. -/
theorem cut_alternations :
    LevinClass.cut.participatesIn .causativeInchoative = false
    ∧ LevinClass.cut.participatesIn .middle = true
    ∧ LevinClass.cut.participatesIn .conative = true
    ∧ LevinClass.cut.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Hit participates in conative and body-part ascension (contact + motion, no CoS). -/
theorem hit_alternations :
    LevinClass.hit.participatesIn .causativeInchoative = false
    ∧ LevinClass.hit.participatesIn .middle = false
    ∧ LevinClass.hit.participatesIn .conative = true
    ∧ LevinClass.hit.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Touch participates only in body-part ascension (contact only). -/
theorem touch_alternations :
    LevinClass.touch.participatesIn .causativeInchoative = false
    ∧ LevinClass.touch.participatesIn .middle = false
    ∧ LevinClass.touch.participatesIn .conative = false
    ∧ LevinClass.touch.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Instrument specification blocks the causative/inchoative alternation. -/
theorem MeaningComponents.instrumentSpec_blocks_ci (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .causativeInchoative = false := by
  simp only [predictedAlternation, h, Bool.not_true, Bool.and_false]

/-- Corollary: instrument specification also blocks the resultative. -/
theorem MeaningComponents.instrumentSpec_blocks_resultative (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .resultative = false := by
  simp only [predictedAlternation, h, Bool.not_true, Bool.and_false]

/-! ### Cross-class predictions -/

/-- All CoS classes participate in the causative/inchoative alternation. -/
theorem cos_classes_causative :
    LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.bend.participatesIn .causativeInchoative = true
    ∧ LevinClass.cooking.participatesIn .causativeInchoative = true
    ∧ LevinClass.otherCoS.participatesIn .causativeInchoative = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Spray/load participates in the locative alternation. -/
theorem sprayLoad_locative :
    LevinClass.sprayLoad.participatesIn .locative = true := rfl

/-- Give class participates in the dative alternation. -/
theorem give_dative :
    LevinClass.give.participatesIn .dative = true := rfl

/-- Motion verbs don't participate in causative alternation (no causation component). -/
theorem motion_no_causative :
    LevinClass.mannerOfMotion.participatesIn .causativeInchoative = false
    ∧ LevinClass.inherentlyDirectedMotion.participatesIn .causativeInchoative = false := ⟨rfl, rfl⟩

/-- Contact verbs predict conative alternation participation. -/
theorem contact_motion_conative :
    LevinClass.hit.participatesIn .conative = true
    ∧ LevinClass.swat.participatesIn .conative = true
    ∧ LevinClass.poke.participatesIn .conative = true
    ∧ LevinClass.cut.participatesIn .conative = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Touch verbs lack motion → no conative despite having contact. -/
theorem touch_no_conative :
    LevinClass.touch.participatesIn .conative = false := rfl

/-- Cut blocked from resultative; break participates (no instrumentSpec). -/
theorem cut_no_resultative_break_resultative :
    LevinClass.cut.participatesIn .resultative = false
    ∧ LevinClass.break_.participatesIn .resultative = true := ⟨rfl, rfl⟩

/-- The causative/inchoative alternation implies the existence of an
    unaccusative variant. -/
theorem causativeInchoative_implies_unaccusative :
    LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.PredictsUnaccusative .break_
    ∧ LevinClass.otherCoS.participatesIn .causativeInchoative = true
    ∧ LevinClass.PredictsUnaccusative .otherCoS := ⟨rfl, trivial, rfl, trivial⟩

/-! ### Family classification theorems -/

/-- The canonical diagnostics all belong to the transitivity or VP-internal families. -/
theorem canonical_diagnostics_families :
    DiathesisAlternation.causativeInchoative.family = .transitivity
    ∧ DiathesisAlternation.middle.family = .transitivity
    ∧ DiathesisAlternation.conative.family = .transitivity
    ∧ DiathesisAlternation.bodyPartPossessorAscension.family = .vpInternal := ⟨rfl, rfl, rfl, rfl⟩

/-- Passive alternations form their own family. -/
theorem passive_family :
    DiathesisAlternation.verbalPassive.family = .passive
    ∧ DiathesisAlternation.prepositionalPassive.family = .passive := ⟨rfl, rfl⟩

/-! ### Class-specific alternation predictions -/

/-- Build verbs participate in both benefactive and material/product alternations. -/
theorem build_benefactive_materialProduct :
    LevinClass.build.participatesIn .benefactive = true
    ∧ LevinClass.build.participatesIn .materialProduct = true := ⟨rfl, rfl⟩

/-- Substance emission verbs participate in the substance/source alternation. -/
theorem substanceEmission_substanceSource :
    LevinClass.substanceEmission.participatesIn .substanceSource = true := rfl

/-- Eat verbs participate in the unspecified object alternation.
    Devour verbs do NOT — they require an expressed object. -/
theorem eat_unspecifiedObject_devour_blocked :
    LevinClass.eat.participatesIn .unspecifiedObject = true
    ∧ LevinClass.devour.participatesIn .unspecifiedObject = false := ⟨rfl, rfl⟩

/-- Social interaction verbs show the understood reciprocal object alternation. -/
theorem socialInteraction_reciprocal :
    LevinClass.socialInteraction.participatesIn .understoodReciprocalObject = true := rfl

/-- Existence and appearance verbs participate in there-insertion. -/
theorem existence_thereInsertion :
    LevinClass.exist.participatesIn .thereInsertion = true
    ∧ LevinClass.appear.participatesIn .thereInsertion = true := ⟨rfl, rfl⟩

/-- Existence and manner-of-motion verbs participate in locative inversion. -/
theorem existence_locativeInversion :
    LevinClass.exist.participatesIn .locativeInversion = true
    ∧ LevinClass.mannerOfMotion.participatesIn .locativeInversion = true := ⟨rfl, rfl⟩

/-- There-insertion and locative inversion align with unaccusativity. -/
theorem unaccusative_diagnostics_align :
    LevinClass.PredictsUnaccusative .exist
    ∧ LevinClass.exist.participatesIn .thereInsertion = true
    ∧ LevinClass.exist.participatesIn .locativeInversion = true
    ∧ LevinClass.PredictsUnaccusative .appear
    ∧ LevinClass.appear.participatesIn .thereInsertion = true
    ∧ LevinClass.appear.participatesIn .locativeInversion = true :=
  ⟨trivial, rfl, rfl, trivial, rfl, rfl⟩

/-- Instrument subject alternation is predicted by external causation. -/
theorem break_instrumentSubject_cut_blocked :
    LevinClass.break_.participatesIn .instrumentSubject = true
    ∧ LevinClass.cut.participatesIn .instrumentSubject = false := ⟨rfl, rfl⟩

/-- Instrument specification blocks both causative/inchoative and instrument
    subject alternations. -/
theorem instrumentSpec_blocks_ci_and_instrumentSubject (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .causativeInchoative = false
    ∧ mc.predictedAlternation .instrumentSubject = false := by
  constructor <;> simp only [MeaningComponents.predictedAlternation, h, Bool.not_true,
    Bool.and_false]

/-! ### Per-alternation predictions -/

/-- Manner-of-motion verbs participate in the induced action alternation. -/
theorem mannerOfMotion_inducedAction :
    LevinClass.mannerOfMotion.participatesIn .inducedAction = true := rfl

/-- Grooming verbs participate in the understood reflexive object alternation. -/
theorem dress_understoodReflexive :
    LevinClass.dress.participatesIn .understoodReflexiveObject = true := rfl

/-- Body process verbs participate in the understood body-part object alternation. -/
theorem bodyProcess_understoodBodyPart :
    LevinClass.bodyProcess.participatesIn .understoodBodyPartObject = true := rfl

/-- Turn/convert verbs participate in the total transformation alternation. -/
theorem turn_totalTransformation :
    LevinClass.turn.participatesIn .totalTransformation = true := rfl

/-- Manner-of-motion verbs participate in the way construction. -/
theorem mannerOfMotion_wayConstruction :
    LevinClass.mannerOfMotion.participatesIn .wayConstruction = true := rfl

/-- Manner-of-motion verbs participate in the directional phrase alternation. -/
theorem mannerOfMotion_directionalPhrase :
    LevinClass.mannerOfMotion.participatesIn .directionalPhrase = true := rfl

/-- Unergative diagnostics dissociate for manner-of-motion verbs: they take
    the prepositional passive but reject cognate objects, despite having
    zero-related nominals ([levin-1993] §51.3.2, ex. 998). -/
theorem unergative_diagnostics :
    LevinClass.mannerOfMotion.participatesIn .cognateObject = false
    ∧ LevinClass.mannerOfMotion.participatesIn .prepositionalPassive = true := ⟨rfl, rfl⟩

/-- Manner-of-motion verbs are diagnostic workhorses: 5 alternations
    from 4 different families. -/
theorem mannerOfMotion_breadth :
    LevinClass.mannerOfMotion.participatesIn .inducedAction = true
    ∧ LevinClass.mannerOfMotion.participatesIn .wayConstruction = true
    ∧ LevinClass.mannerOfMotion.participatesIn .directionalPhrase = true
    ∧ LevinClass.mannerOfMotion.participatesIn .prepositionalPassive = true
    ∧ LevinClass.mannerOfMotion.participatesIn .locativeInversion = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Verbal passive coverage -/

/-- Verbal passive is available across all major transitive class families. -/
theorem verbalPassive_coverage :
    LevinClass.break_.participatesIn .verbalPassive = true
    ∧ LevinClass.hit.participatesIn .verbalPassive = true
    ∧ LevinClass.put.participatesIn .verbalPassive = true
    ∧ LevinClass.give.participatesIn .verbalPassive = true
    ∧ LevinClass.build.participatesIn .verbalPassive = true
    ∧ LevinClass.murder.participatesIn .verbalPassive = true
    ∧ LevinClass.see.participatesIn .verbalPassive = true
    ∧ LevinClass.amuse.participatesIn .verbalPassive = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Measure verbs do NOT participate in verbal passive. -/
theorem measure_no_verbalPassive :
    LevinClass.measure.participatesIn .verbalPassive = false := rfl

/-- Weather verbs do NOT participate in verbal passive (no object to promote). -/
theorem weather_no_verbalPassive :
    LevinClass.weather.participatesIn .verbalPassive = false := rfl

/-! ### Prepositional passive and swarm coverage -/

/-- Prepositional passive aligns with unergativity. -/
theorem prepositionalPassive_unergatives :
    LevinClass.mannerOfMotion.participatesIn .prepositionalPassive = true
    ∧ LevinClass.bodyProcess.participatesIn .prepositionalPassive = true
    ∧ LevinClass.mannerOfSpeaking.participatesIn .prepositionalPassive = true
    ∧ LevinClass.assumePosition.participatesIn .prepositionalPassive = true := ⟨rfl, rfl, rfl, rfl⟩

/-- The swarm alternation applies to existence and manner-of-motion verbs. -/
theorem swarm_classes :
    LevinClass.exist.participatesIn .swarm = true
    ∧ LevinClass.mannerOfMotion.participatesIn .swarm = true
    ∧ LevinClass.bodyInternalMotion.participatesIn .swarm = true := ⟨rfl, rfl, rfl⟩

end ArgumentStructure
