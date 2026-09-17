import Mathlib.Data.Finset.Basic
import Linglib.Semantics.ArgumentStructure.LevinClass

/-!
# Diathesis alternations

Twenty-five of the alternations of [levin-1993] Part One, grouped by the chapter that presents
them, the Introduction's prediction of an alternation from a class's meaning components, and
each class's alternation profile as Part II records it: the alternations the class page
attests (`LevinClass.alternations`) and the ones it stars (`LevinClass.starredAlternations`),
with `LevinClass.Participates` as the attested relation.

## Implementation notes

The 25 alternations are the ones that discriminate the major classes; the remaining ones of
Part One are not encoded. `MeaningComponents.predictedAlternation` is a hypothesis, not data:
it agrees with Part II on the Introduction's quadruple (`quadruple_prediction_matches`) and
overshoots elsewhere (`prediction_not_sound`), which the studies that rely on it state
explicitly. The profiles are read off the class pages' property lists, a starred example
denying the alternation and an unstarred one attesting it.

## References

* [levin-1993]
-/

namespace ArgumentStructure

/-! ### Alternation Families -/

/-- Classification of diathesis alternations by the chapter of
    [levin-1993] Part One where they are primarily discussed.

    -/
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

/-! ### Diathesis Alternation Diagnostics -/

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

/-! ### Component-Derived Alternation Prediction -/

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

/-! ### Structural properties of fusion + alternation prediction -/

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

/-! ### Class profiles

The alternation profile of each class as [levin-1993] Part II records it: every class page
lists the alternations tested, an unstarred example attesting the alternation and a starred
one denying it. Classes at a parent grain (`search`, `mannerOfMotion`, `bodyProcess`,
`imageCreation`, `getObtain`) take the union over their subsections. Alternations a page does
not test are in neither set. -/

/-- The alternations [levin-1993] Part II attests for the class. -/
def LevinClass.alternations : LevinClass → Finset DiathesisAlternation
  | .put => ∅
  | .funnel => ∅
  | .putDirection => ∅
  | .pour => {DiathesisAlternation.causativeInchoative}
  | .coil => {DiathesisAlternation.causativeInchoative, .middle}
  | .sprayLoad => {DiathesisAlternation.causativeInchoative, .conative, .locative}
  | .remove => ∅
  | .clear => {DiathesisAlternation.causativeInchoative, .locative}
  | .wipe => {DiathesisAlternation.conative, .unspecifiedObject, .locative, .resultative}
  | .steal => ∅
  | .send => {DiathesisAlternation.dative}
  | .carry => {DiathesisAlternation.dative}
  | .drive => ∅
  | .pushPull => {DiathesisAlternation.conative, .resultative}
  | .give => {DiathesisAlternation.dative}
  | .contribute => ∅
  | .getObtain => {DiathesisAlternation.benefactive}
  | .exchange => ∅
  | .learn => ∅
  | .hold => {DiathesisAlternation.bodyPartPossessorAscension}
  | .conceal => ∅
  | .throw => {DiathesisAlternation.dative, .directionalPhrase}
  | .hit => {DiathesisAlternation.conative, .bodyPartPossessorAscension, .instrumentSubject,
      .resultative}
  | .swat => {DiathesisAlternation.conative, .bodyPartPossessorAscension, .resultative}
  | .spank => {DiathesisAlternation.bodyPartPossessorAscension}
  | .poke => {DiathesisAlternation.conative, .bodyPartPossessorAscension, .instrumentSubject}
  | .touch => {DiathesisAlternation.bodyPartPossessorAscension, .instrumentSubject}
  | .cut => {DiathesisAlternation.middle, .conative, .bodyPartPossessorAscension,
      .instrumentSubject, .resultative}
  | .carve => {DiathesisAlternation.middle, .instrumentSubject}
  | .mix => {DiathesisAlternation.causativeInchoative, .middle}
  | .amalgamate => {DiathesisAlternation.causativeInchoative, .middle}
  | .separate => {DiathesisAlternation.causativeInchoative, .middle}
  | .split => {DiathesisAlternation.causativeInchoative, .middle}
  | .color => ∅
  | .imageCreation => {DiathesisAlternation.unspecifiedObject}
  | .build => {DiathesisAlternation.unspecifiedObject, .benefactive, .materialProduct}
  | .grow => {DiathesisAlternation.causativeInchoative, .materialProduct}
  | .create => ∅
  | .knead => {DiathesisAlternation.causativeInchoative}
  | .turn => {DiathesisAlternation.causativeInchoative, .totalTransformation}
  | .performance => {DiathesisAlternation.unspecifiedObject, .dative, .benefactive}
  | .engender => ∅
  | .calve => ∅
  | .appoint => ∅
  | .characterize => ∅
  | .declare => ∅
  | .see => ∅
  | .sight => ∅
  | .amuse => {DiathesisAlternation.middle, .resultative}
  | .admire => ∅
  | .marvel => ∅
  | .want => ∅
  | .long => ∅
  | .judgment => ∅
  | .assessment => ∅
  | .search => {DiathesisAlternation.unspecifiedObject}
  | .socialInteraction => {DiathesisAlternation.understoodReciprocalObject}
  | .say => ∅
  | .tell => {DiathesisAlternation.dative}
  | .mannerOfSpeaking => ∅
  | .talk => ∅
  | .animalSound => {DiathesisAlternation.resultative}
  | .eat => {DiathesisAlternation.conative, .unspecifiedObject}
  | .devour => ∅
  | .dine => ∅
  | .bodyProcess => ∅
  | .nonverbalExpression => {DiathesisAlternation.resultative}
  | .flinch => ∅
  | .hurt => ∅
  | .dress => {DiathesisAlternation.causativeInchoative, .understoodReflexiveObject}
  | .murder => ∅
  | .poison => {DiathesisAlternation.resultative}
  | .lightEmission => {DiathesisAlternation.causativeInchoative, .locative, .thereInsertion,
      .locativeInversion}
  | .soundEmission => {DiathesisAlternation.causativeInchoative, .locative, .thereInsertion,
      .locativeInversion, .directionalPhrase}
  | .substanceEmission => {DiathesisAlternation.causativeInchoative, .substanceSource, .locative,
      .thereInsertion, .locativeInversion}
  | .destroy => {DiathesisAlternation.instrumentSubject}
  | .break_ => {DiathesisAlternation.causativeInchoative, .middle, .instrumentSubject, .resultative}
  | .bend => {DiathesisAlternation.causativeInchoative, .middle, .instrumentSubject, .resultative}
  | .cooking => {DiathesisAlternation.causativeInchoative, .instrumentSubject, .resultative}
  | .otherCoS => {DiathesisAlternation.causativeInchoative, .middle, .instrumentSubject,
      .resultative}
  | .entitySpecificCoS => ∅
  | .calibratableCoS => {DiathesisAlternation.causativeInchoative}
  | .lodge => {DiathesisAlternation.causativeInchoative}
  | .exist => {DiathesisAlternation.thereInsertion, .locativeInversion}
  | .appear => {DiathesisAlternation.thereInsertion, .locativeInversion}
  | .disappearance => ∅
  | .bodyInternalMotion => {DiathesisAlternation.resultative, .directionalPhrase}
  | .assumePosition => ∅
  | .inherentlyDirectedMotion => ∅
  | .leave => ∅
  | .mannerOfMotion => {DiathesisAlternation.causativeInchoative, .inducedAction, .thereInsertion,
      .locativeInversion, .resultative}
  | .vehicleMotion => {DiathesisAlternation.inducedAction, .resultative}
  | .chase => ∅
  | .avoid => ∅
  | .linger => ∅
  | .rush => {DiathesisAlternation.causativeInchoative}
  | .measure => ∅
  | .aspectual => {DiathesisAlternation.causativeInchoative}
  | .weather => ∅

/-- The alternations [levin-1993] Part II stars for the class. -/
def LevinClass.starredAlternations : LevinClass → Finset DiathesisAlternation
  | .put => {DiathesisAlternation.causativeInchoative, .middle, .locative}
  | .funnel => {DiathesisAlternation.causativeInchoative, .middle, .locative}
  | .putDirection => {DiathesisAlternation.causativeInchoative, .middle, .dative, .locative}
  | .pour => {DiathesisAlternation.middle, .conative, .locative}
  | .coil => {DiathesisAlternation.conative, .locative}
  | .sprayLoad => ∅
  | .remove => {DiathesisAlternation.causativeInchoative, .conative, .locative}
  | .clear => {DiathesisAlternation.conative, .resultative}
  | .wipe => {DiathesisAlternation.causativeInchoative}
  | .steal => {DiathesisAlternation.causativeInchoative, .conative, .benefactive, .locative}
  | .send => {DiathesisAlternation.causativeInchoative, .middle, .conative}
  | .carry => {DiathesisAlternation.causativeInchoative, .middle, .conative}
  | .drive => {DiathesisAlternation.causativeInchoative, .middle, .conative}
  | .pushPull => {DiathesisAlternation.causativeInchoative}
  | .give => {DiathesisAlternation.causativeInchoative}
  | .contribute => {DiathesisAlternation.causativeInchoative, .dative}
  | .getObtain => {DiathesisAlternation.dative, .locative}
  | .exchange => {DiathesisAlternation.dative, .benefactive}
  | .learn => ∅
  | .hold => {DiathesisAlternation.middle, .conative}
  | .conceal => {DiathesisAlternation.locative}
  | .throw => {DiathesisAlternation.causativeInchoative, .middle, .conative}
  | .hit => {DiathesisAlternation.causativeInchoative, .middle}
  | .swat => {DiathesisAlternation.causativeInchoative, .middle, .instrumentSubject}
  | .spank => {DiathesisAlternation.causativeInchoative, .middle, .conative, .instrumentSubject}
  | .poke => {DiathesisAlternation.causativeInchoative, .middle}
  | .touch => {DiathesisAlternation.causativeInchoative, .middle, .conative, .resultative}
  | .cut => {DiathesisAlternation.causativeInchoative}
  | .carve => {DiathesisAlternation.causativeInchoative, .conative, .bodyPartPossessorAscension}
  | .mix => ∅
  | .amalgamate => ∅
  | .separate => {DiathesisAlternation.locative}
  | .split => ∅
  | .color => ∅
  | .imageCreation => ∅
  | .build => {DiathesisAlternation.causativeInchoative, .totalTransformation}
  | .grow => {DiathesisAlternation.totalTransformation}
  | .create => {DiathesisAlternation.causativeInchoative, .benefactive}
  | .knead => {DiathesisAlternation.materialProduct, .totalTransformation}
  | .turn => {DiathesisAlternation.materialProduct}
  | .performance => {DiathesisAlternation.causativeInchoative}
  | .engender => {DiathesisAlternation.causativeInchoative}
  | .calve => ∅
  | .appoint => {DiathesisAlternation.dative}
  | .characterize => ∅
  | .declare => {DiathesisAlternation.dative}
  | .see => {DiathesisAlternation.middle}
  | .sight => {DiathesisAlternation.middle}
  | .amuse => {DiathesisAlternation.causativeInchoative}
  | .admire => {DiathesisAlternation.middle}
  | .marvel => ∅
  | .want => ∅
  | .long => ∅
  | .judgment => {DiathesisAlternation.middle}
  | .assessment => ∅
  | .search => ∅
  | .socialInteraction => ∅
  | .say => {DiathesisAlternation.dative}
  | .tell => ∅
  | .mannerOfSpeaking => {DiathesisAlternation.dative}
  | .talk => ∅
  | .animalSound => {DiathesisAlternation.directionalPhrase}
  | .eat => {DiathesisAlternation.instrumentSubject}
  | .devour => {DiathesisAlternation.conative, .unspecifiedObject}
  | .dine => {DiathesisAlternation.conative, .unspecifiedObject}
  | .bodyProcess => {DiathesisAlternation.resultative}
  | .nonverbalExpression => ∅
  | .flinch => {DiathesisAlternation.causativeInchoative}
  | .hurt => ∅
  | .dress => ∅
  | .murder => {DiathesisAlternation.causativeInchoative, .middle, .instrumentSubject, .resultative}
  | .poison => {DiathesisAlternation.causativeInchoative, .middle}
  | .lightEmission => ∅
  | .soundEmission => ∅
  | .substanceEmission => ∅
  | .destroy => {DiathesisAlternation.causativeInchoative, .middle, .conative, .materialProduct,
      .totalTransformation, .resultative}
  | .break_ => {DiathesisAlternation.conative, .bodyPartPossessorAscension}
  | .bend => {DiathesisAlternation.conative, .bodyPartPossessorAscension}
  | .cooking => {DiathesisAlternation.conative}
  | .otherCoS => {DiathesisAlternation.conative, .locative, .thereInsertion, .locativeInversion}
  | .entitySpecificCoS => {DiathesisAlternation.causativeInchoative}
  | .calibratableCoS => {DiathesisAlternation.thereInsertion, .locativeInversion}
  | .lodge => {DiathesisAlternation.locative, .thereInsertion, .locativeInversion}
  | .exist => {DiathesisAlternation.causativeInchoative, .locative}
  | .appear => {DiathesisAlternation.causativeInchoative}
  | .disappearance => {DiathesisAlternation.causativeInchoative}
  | .bodyInternalMotion => {DiathesisAlternation.causativeInchoative}
  | .assumePosition => {DiathesisAlternation.thereInsertion, .locativeInversion}
  | .inherentlyDirectedMotion => {DiathesisAlternation.causativeInchoative, .resultative}
  | .leave => ∅
  | .mannerOfMotion => ∅
  | .vehicleMotion => ∅
  | .chase => {DiathesisAlternation.causativeInchoative}
  | .avoid => ∅
  | .linger => {DiathesisAlternation.causativeInchoative}
  | .rush => ∅
  | .measure => {DiathesisAlternation.causativeInchoative, .dative}
  | .aspectual => ∅
  | .weather => ∅

/-- The class shows the alternation in [levin-1993] Part II. -/
def LevinClass.Participates (c : LevinClass) (a : DiathesisAlternation) : Prop :=
  a ∈ c.alternations

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Participates a) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- No class both shows and lacks an alternation. -/
theorem LevinClass.disjoint_alternations_starredAlternations (c : LevinClass) :
    Disjoint c.alternations c.starredAlternations := by
  cases c <;> decide

/-! ### The Introduction's quadruple

*break*, *cut*, *hit* and *touch* are told apart by the four diagnostic alternations, and on
these four classes the component prediction agrees with Part II. -/

/-- The four diagnostic alternations of the Introduction. -/
def diagnosticAlternations : List DiathesisAlternation :=
  [.causativeInchoative, .middle, .conative, .bodyPartPossessorAscension]

/-- The quadruple takes four distinct profiles over the diagnostic alternations. -/
theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map fun c ↦
      diagnosticAlternations.map fun a ↦ decide (c.Participates a)).Pairwise (· ≠ ·) := by
  decide

/-- On the quadruple, the component prediction matches Part II for every diagnostic
alternation. -/
theorem quadruple_prediction_matches :
    ∀ c ∈ [LevinClass.break_, .cut, .hit, .touch], ∀ a ∈ diagnosticAlternations,
      c.meaningComponents.predictedAlternation a = decide (c.Participates a) := by
  decide

/-- The prediction is not sound in general: destroy verbs are change-of-state causatives that
Part II stars for the causative/inchoative alternation. -/
theorem prediction_not_sound :
    LevinClass.destroy.meaningComponents.predictedAlternation .causativeInchoative = true ∧
      DiathesisAlternation.causativeInchoative ∈ LevinClass.destroy.starredAlternations := by
  decide

end ArgumentStructure
