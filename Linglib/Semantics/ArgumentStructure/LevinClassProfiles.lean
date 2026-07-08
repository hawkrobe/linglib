import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.ArgumentStructure.LevinTheory

/-!
# Levin Class → Entailment Profile Mapping

[levin-1993] [dowty-1991] [beavers-2010]
[beavers-koontz-garboden-2020] [rappaport-hovav-levin-1998]

Maps [levin-1993] verb classes to proto-role entailment profiles
([dowty-1991]), encoding the argument-structure generalizations
that hold at the class level.

The mapping is organized by **argument structure template**: groups of
Levin classes that share the same subject/object entailment profile.
This reflects the field consensus ([beavers-koontz-garboden-2020])
that root meaning determines which entailments hold:

- **Manner verbs** (hit, touch): agent subject, contacted object (no CoS)
- **Result verbs** (break, destroy): agent subject, affected object (CoS)
- **Creation verbs** (build, create): agent subject, created object (CoS+DE)
- **Motion verbs** (run, walk): agent subject (no causation), no object
- **Perception verbs** (see, hear): experiencer subject
- **Psych-causal verbs** (amuse): stimulus subject

Individual verbs can override class-level profiles via explicit
`subjectEntailments`/`objectEntailments` on `Verb`.
-/

namespace ArgumentStructure

-- ════════════════════════════════════════════════════
-- § 1. Argument Structure Templates
-- ════════════════════════════════════════════════════

/-- Subject + object entailment profile pair for a verb class.
    `objectProfile = none` for intransitive classes. -/
structure ArgTemplate where
  subjectProfile : EntailmentProfile
  objectProfile : Option EntailmentProfile := none
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Named Templates
-- ════════════════════════════════════════════════════

/-! Named per-class argument profiles. These are the class-level consensus
rows formerly hand-stored per verb in `EntailmentProfile.lean`; consumers
(studies, fragments, `Morphology/RootTypology.lean`) reference these or the
template accessors below. -/

/-- Experiencer argument: sentient with respect to the event, without
    volition or causation ([dowty-1991] (38): "the Experiencer is entailed
    to be sentient/perceiving"); independent existence per the p. 573
    generalization that every verb entailing any of (27a–d) also entails
    subject existence. -/
def experiencerProfile : EntailmentProfile :=
  { sentience := true, independentExistence := true }

/-- Stimulus argument: causes the experience without being sentient with
    respect to it ([dowty-1991] (38): "the Stimulus causes some emotional
    reaction or cognitive judgment in the Experiencer ... though the
    Stimulus is not [entailed to be sentient/perceiving]"). -/
def stimulusProfile : EntailmentProfile :=
  { causation := true, independentExistence := true }

/-- Contacted-but-unaffected object of the surface-contact classes: CA+St,
    no CoS. [dowty-1991] never attributes a change of state to hit-class
    objects ((64 III): no Incremental Theme, no CoS for either non-subject
    argument); [beavers-2011] eq. (60c): impact verbs impose only *potential*
    for change. -/
def contactObject : EntailmentProfile :=
  { causallyAffected := true, stationary := true }

/-- Created object: CoS+IT+CA+DE — incremental theme with dependent
    existence ([dowty-1991] (30e)(i): the effected argument "does not exist
    before ... the event"). -/
def creationObject : EntailmentProfile :=
  { changeOfState := true, incrementalTheme := true, causallyAffected := true,
    dependentExistence := true }

/-- Consumed object: CoS+IT+CA — incremental theme without DE (the object
    pre-exists the event). The missing DE is load-bearing for the Grimm
    bridge: `PersistenceLevel.fromPatientProfile` separates creation (DE+IT →
    `exPersEnd`) from consumption (IT alone → `exPersBeginning`); see
    `Studies/Dowty1991.lean` for the (30e) destruction-criterion tension. -/
def consumptionObject : EntailmentProfile :=
  { changeOfState := true, incrementalTheme := true, causallyAffected := true }

/-- Full agent acting on a contacted but unaffected object.
    Subject: V+S+C+M+IE. Object: CA+St (no CoS).
    [beavers-2010]: "unspecified" affectedness — the verb's
    truth conditions don't entail a change of state in the object.
    [beavers-koontz-garboden-2020]: manner verbs lack result
    entailments. -/
def mannerContact : ArgTemplate where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- Full agent causing change of state in the object.
    Subject: V+S+C+M+IE. Object: CoS+CA (causally affected, changed).
    [beavers-2010]: "quantized" affectedness — the verb entails
    a definite change of state (the object reaches an end state).
    [beavers-koontz-garboden-2020]: result verbs entail CoS. -/
def resultChange : ArgTemplate where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some accomplishmentObjectProfile

/-- Full agent creating an entity (object comes into existence).
    Subject: V+S+C+M+IE. Object: CoS+IT+CA+DE.
    [beavers-2010]: quantized affectedness + dependent existence.
    The object is an incremental theme whose extent measures the event. -/
def creation : ArgTemplate where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some creationObject

/-- Agent consuming/destroying an incremental theme (Levin 39.1 eat verbs:
    *eat, drink*; 39.4 devour verbs: *devour, consume, ingest*).
    Subject: V+S+C+M+IE. Object: CoS+IT+CA.
    Like creation but without dependent existence (the object
    pre-exists the event). -/
def consumption : ArgTemplate where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some consumptionObject

/-- Self-propelled motion (no caused result, no object).
    Subject: V+S+M+IE (no causation — the mover doesn't cause
    a change in another participant). -/
def selfMotion : ArgTemplate where
  subjectProfile := activitySubjectProfile

/-- Perception / experiencer-subject.
    Subject: S+IE (sentient, independently existing, but not
    volitional or causal). -/
def perception : ArgTemplate where
  subjectProfile := experiencerProfile
  objectProfile  := some ⟨false, false, false, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer (Class II psych, Levin 31.1 amuse verbs;
    [belletti-rizzi-1988]). Subject: C+IE (causal stimulus). Object: S+IE
    (experiencer). Mirror image of `psychState`. -/
def psychCausal : ArgTemplate where
  subjectProfile := stimulusProfile
  objectProfile  := some experiencerProfile

/-- Experiencer-subject psych state (Levin 31.2 admire verbs: *admire, like,
    love, fear, envy*). Subject: sentient experiencer; object: causing
    stimulus — [dowty-1991] (38): the predicate "entails that the Experiencer
    has some perception of the Stimulus", and the Stimulus "causes some
    emotional reaction or cognitive judgment in the Experiencer". Mirror
    image of `psychCausal` — the argument-selection tie behind the
    *like*/*please* doublets (§8.3). Distinct from `desire`: admire-class
    subjects are sentience-entailed, want-class subjects are not. -/
def psychState : ArgTemplate where
  subjectProfile := experiencerProfile
  objectProfile  := some stimulusProfile

/-- Desire states (Levin 32.1 want verbs: *covet, crave, desire, need,
    want*). Subject: independent existence ALONE — [dowty-1991] (29e) "John
    needs a new car", glossed p. 573 as "verbs that entail subject existence
    but have none of (a)–(d)": NO sentience entailment, unlike the admire
    class (*this situation needs a solution*). Object: de dicto/nonspecific,
    so dependent existence — (30e) "John needs a car/seeks a unicorn ...
    (de dicto objects: no existence)". -/
def desire : ArgTemplate where
  subjectProfile := { independentExistence := true }
  objectProfile  := some { dependentExistence := true }

/-- Change of possession (Levin 13.1 give verbs: *give, lend, pass, sell*;
    13.5 verbs of obtaining: *buy, get, obtain*). Subject: volitional agent
    without entailed movement (V+S+C+IE) — [dowty-1991] §3.2: "both buyer
    and seller must act agentively (voluntarily)". Buyer and seller profiles
    are identical; that is the §8.3 argument-selection tie behind the
    *buy*/*sell* doublet. No object profile: Dowty flags the goods/currency
    "two Themes" worry (§3.2) and attributes no object entailments. -/
def possessionTransfer : ArgTemplate where
  subjectProfile := { volition := true, sentience := true, causation := true,
                      independentExistence := true }

/-- Surface-contact manner (Levin 10.4.1 wipe verbs, manner subclass:
    *wipe, scrub, sweep, rub, wash*). Subject: M+IE only — underspecified
    for volition, so agentivity is pragmatically resolved
    ([rappaport-hovav-levin-1998] on *sweep*; [dowty-1991] never discusses
    *sweep*). Object: contacted, no entailed change ([beavers-2010]
    potential affectedness). -/
def wipeManner : ArgTemplate where
  subjectProfile := { movement := true, independentExistence := true }
  objectProfile  := some contactObject

/-- Instrument subclass of the wipe verbs (Levin 10.4.2: *brush, comb, mop,
    vacuum*; [rappaport-hovav-levin-1998]'s *sweep with a broom*): instrument
    lexicalization forces an obligatory volitional agent (V+S+C+M+IE).
    Not in the class map — `LevinClass.argTemplate .wipe` gives the manner
    subclass default; instrument-sense entries override per verb. -/
def wipeInstrument : ArgTemplate where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- Unaccusative change of state (inchoative).
    Subject: CoS+CA (undergoes change, no agentive features).
    No external argument. -/
def unaccusativeCoS : ArgTemplate where
  subjectProfile := accomplishmentObjectProfile

/-- Directed motion (unaccusative).
    Subject: M+IE+CoS (moves, changes location). -/
def directedMotion : ArgTemplate where
  subjectProfile := achievementSubjectProfile

/-- Disappearance (Levin 48.2: *die, disappear, expire, perish, vanish* —
    "describe the disappearance or going out of existence of some entity").
    Sole argument: CoS+CA+DE — like `unaccusativeCoS` plus dependent
    existence, since the argument goes out of existence ([dowty-1991]
    (30e)(i): the effected argument "will not exist after the event"). -/
def disappearance : ArgTemplate where
  subjectProfile := { changeOfState := true, causallyAffected := true,
                      dependentExistence := true }

-- ════════════════════════════════════════════════════
-- § 3. LevinClass → ArgTemplate
-- ════════════════════════════════════════════════════

end ArgumentStructure

namespace ArgumentStructure

/-- Map a Levin class to its argument structure template.
    Returns `none` for classes whose profiles haven't been determined yet. -/
def LevinClass.argTemplate : LevinClass → Option ArgTemplate
  -- § 18: Contact by Impact — manner verbs, no CoS entailment
  | .hit | .swat              => some mannerContact
  -- § 20: Contact: Touch — like hit but lighter force
  | .touch                    => some mannerContact
  -- § 21: Cutting — manner + result (CoS entailed)
  | .cut | .carve             => some resultChange
  -- § 44: Destroy
  | .destroy                  => some resultChange
  -- § 42: Killing
  | .murder | .poison         => some resultChange
  -- § 45: Change of State (causative/inchoative alternation)
  | .break_ | .bend | .cooking
  | .otherCoS | .entitySpecificCoS
  | .calibratableCoS          => some resultChange
  -- § 26: Creation and Transformation
  | .build | .create | .knead => some creation
  | .grow                     => some creation
  -- § 25: Image Creation
  | .imageCreation            => some creation
  -- § 39: Ingesting
  | .eat | .devour            => some consumption
  -- § 51.3: Manner of Motion
  | .mannerOfMotion           => some selfMotion
  -- § 51.6: Chase
  | .chase                    => some selfMotion
  -- § 51.1: Inherently Directed Motion
  | .inherentlyDirectedMotion => some directedMotion
  -- § 30: Perception
  | .see | .sight             => some perception
  -- § 31.1: Amuse-class psych verbs (stimulus subject)
  | .amuse                    => some psychCausal
  -- § 31.2: Admire-class psych verbs (experiencer subject)
  | .admire                   => some psychState
  -- § 32.1: Want verbs (desire states)
  | .want                     => some desire
  -- § 13.1 / § 13.5: Change of possession (give / obtain)
  | .give | .getObtain        => some possessionTransfer
  -- § 10.4: Wipe verbs (manner-subclass default; instrument-sense
  -- entries override with `wipeInstrument` per verb)
  | .wipe                     => some wipeManner
  -- § 48.2: Disappearance
  | .disappearance            => some ArgumentStructure.disappearance
  -- Not yet classified
  | _                         => none

-- ════════════════════════════════════════════════════
-- § 4. Convenience accessors
-- ════════════════════════════════════════════════════

/-- Subject entailment profile for a Levin class. -/
def LevinClass.subjectProfile (c : LevinClass) : Option EntailmentProfile :=
  c.argTemplate.map (·.subjectProfile)

/-- Object entailment profile for a Levin class. -/
def LevinClass.objectProfile (c : LevinClass) : Option EntailmentProfile :=
  c.argTemplate.bind (·.objectProfile)

end ArgumentStructure

namespace ArgumentStructure
open Verb
open Verb.Root.Kinds

-- ════════════════════════════════════════════════════
-- § 5. Manner roots lack result entailments
-- ════════════════════════════════════════════════════

/-- Hit-class object lacks CoS (manner verbs don't entail change of state) —
    the Beavers & Koontz-Garboden generalization that manner roots lack result
    entailments, read off the class-level template. -/
theorem mannerContact_object_no_cos :
    (mannerContact.objectProfile.map (·.changeOfState)) = some false := rfl

-- ════════════════════════════════════════════════════
-- § 6. Derived role labels match expectations
-- ════════════════════════════════════════════════════

/-- Hit-class subject → agent label. -/
theorem hit_subject_role :
    mannerContact.subjectProfile.toRole = some .agent := by decide

/-- Hit-class object → patient label (CA+St maps to patient). -/
theorem hit_object_role :
    contactObject.toRole = some .patient := by decide

/-- Self-motion subject → agent label. -/
theorem selfMotion_subject_role :
    selfMotion.subjectProfile.toRole = some .agent := by decide

/-- Perception subject → experiencer label. -/
theorem perception_subject_role :
    perception.subjectProfile.toRole = some .experiencer := by decide

/-- Psych-causal subject → stimulus label. -/
theorem psychCausal_subject_role :
    psychCausal.subjectProfile.toRole = some .stimulus := by decide

/-- Directed-motion subject → patient: the unaccusative subject of *arrive*
    undergoes a change of location (`changeOfState`) without agentivity. Formerly
    `none` (the moving subject was dropped); `toRole` now restores it. -/
theorem directedMotion_subject_role :
    directedMotion.subjectProfile.toRole = some .patient := by decide

/-- Admire-class subject → experiencer, and its stimulus object matches the
    amuse-class subject exactly — the doublet mirror ([dowty-1991] (38)). -/
theorem psychState_mirrors_psychCausal :
    psychState.subjectProfile.toRole = some .experiencer ∧
    psychState.objectProfile = some psychCausal.subjectProfile ∧
    psychCausal.objectProfile = some psychState.subjectProfile := by decide

/-- Disappearance-class subject → patient (pure Proto-Patient: *die*). -/
theorem disappearance_subject_role :
    disappearance.subjectProfile.toRole = some .patient := by decide

-- ════════════════════════════════════════════════════
-- § 7. Root.Kinds → ArgTemplate (the missing derivation)
-- ════════════════════════════════════════════════════

/-! Root kind signatures determine argument templates — the derivational
direction in the argument-realization tradition ([beavers-koontz-garboden-2020]
roots, [rappaport-hovav-levin-1998] event-template linking). The chain runs:

    Root.Kinds → Template → ArgTemplate → ThetaRole labels

`toArgTemplate` formalizes the default derivation. It
captures the majority pattern: causative roots produce agent subjects
and affected objects; manner-only roots produce agent subjects without
causation; result-only roots produce unaccusative subjects; state-only
roots produce experiencer subjects.

Two classes of systematic overrides exist:
- **Psych-causal verbs** (amuse): `causativeResult` roots where the
  subject is a non-volitional stimulus, not a volitional agent.
  Override: `psychCausal` template.
- **Creation verbs** (build): `causativeResult` roots where the object
  has dependent existence and incremental theme structure.
  Override: `creation` template.

These overrides are documented and verified below. -/

/-- Derive a default ArgTemplate from a root kind signature.

    The derivation follows B&KG's event structure decomposition:

    - `cause`: subject is external causer → full agent (V+S+C+M+IE),
      object undergoes change → CoS+CA
    - `result` without `cause`: internally caused change → unaccusative,
      sole argument is patient (CoS+CA)
    - `manner` without `cause`/`result`: activity → agent without
      causation (V+S+M+IE), no affected object
    - `state` only: stative → experiencer subject (S+IE)
    - no entailments: no default derivation

    For `cause+manner` (fullSpec) vs `cause` without `manner`
    (causativeResult): both produce the same default ArgTemplate.
    The manner flag restricts HOW the cause proceeds (cutting vs.
    breaking), not WHETHER there's an agent. -/
def toArgTemplate (re : Root.Kinds) : Option ArgTemplate :=
  if .cause ∈ re then
    some resultChange
  else if .result ∈ re then
    some unaccusativeCoS
  else if .manner ∈ re then
    some selfMotion
  else if .state ∈ re then
    some perception
  else
    none

-- ════════════════════════════════════════════════════
-- § 8. Consistency: rootEntailments vs argTemplate
-- ════════════════════════════════════════════════════

/-! For each LevinClass with both `rootEntailments` and `argTemplate`
defined, we verify that the derived ArgTemplate either MATCHES the
hand-specified one or is a documented override. -/

-- § 8a. The table is not the naive derivation

/-- `argTemplate` is not merely `toArgTemplate ∘ rootEntailments`: it diverges
    for the documented overrides (creation, psych-causal). *Build* witnesses
    this — its `causativeResult` root derives `resultChange`, but the class
    template is `creation` (incremental-theme object). A table that always
    matched the derivation would be redundant with it; this divergence is why
    `argTemplate` exists as a separate label, and §8b documents the overrides. -/
theorem argTemplate_diverges_from_derivation :
    ∃ c : LevinClass,
      LevinClass.argTemplate c ≠ toArgTemplate (LevinClass.rootEntailments c) :=
  ⟨.build, by decide⟩

-- § 8b. Documented overrides (derivation gives a default that the
--        class specializes)

/-- Build-class: causativeResult derives `resultChange`, but build
    verbs have a CREATION object (CoS+IT+CA+DE) — the object comes
    into existence. Dependent existence and incremental theme are
    additional entailments not captured by root structural features. -/
theorem build_override_creation :
    toArgTemplate (LevinClass.rootEntailments .build) = some resultChange ∧
    LevinClass.argTemplate .build = some creation := ⟨rfl, rfl⟩

/-- Amuse-class: causativeResult derives `resultChange` (agent subject),
    but psych-causal verbs have a STIMULUS subject (C+IE, no volition)
    and EXPERIENCER object (S+IE). The nature of causation (volitional
    vs. stimulus) isn't encoded in root entailments. -/
theorem amuse_override_psychCausal :
    toArgTemplate (LevinClass.rootEntailments .amuse) = some resultChange ∧
    LevinClass.argTemplate .amuse = some psychCausal := ⟨rfl, rfl⟩

/-- Eat/devour: default from rootEntailments is not defined (minimal),
    but class-level argTemplate specifies `consumption`. -/
theorem eat_has_class_template :
    LevinClass.argTemplate .eat = some consumption := rfl

/-- The remaining documented overrides, in one place. Root kind signatures
    are too coarse for these classes: manner roots don't distinguish the
    wipe class's underspecified-volition subject from full-agent self-motion;
    state roots don't distinguish sentience-entailed psych states (admire)
    from bare desire states (want); and result roots don't see the
    disappearance class's dependent existence. -/
theorem class_templates_override_derivation :
    (toArgTemplate (LevinClass.rootEntailments .wipe) = some selfMotion ∧
      LevinClass.argTemplate .wipe = some wipeManner) ∧
    (toArgTemplate (LevinClass.rootEntailments .admire) = some perception ∧
      LevinClass.argTemplate .admire = some psychState) ∧
    (toArgTemplate (LevinClass.rootEntailments .want) = some perception ∧
      LevinClass.argTemplate .want = some desire) ∧
    (toArgTemplate (LevinClass.rootEntailments .disappearance)
        = some unaccusativeCoS ∧
      LevinClass.argTemplate .disappearance
        = some ArgumentStructure.disappearance) ∧
    (toArgTemplate (LevinClass.rootEntailments .getObtain) = none ∧
      LevinClass.argTemplate .getObtain = some possessionTransfer) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩

-- § 8c. Subject agreement: even for overrides, the subject profile's
--        core agentivity features agree

/-- Build-class subject matches the derivation's subject
    (both are full agent V+S+C+M+IE). The override affects only
    the object, not the subject. -/
theorem build_subject_agrees :
    resultChange.subjectProfile = creation.subjectProfile := rfl

-- § 8d. The derivation produces well-formed ArgTemplates

/-- All canonical root signatures derive well-formed internal constraints
    (volition → sentience holds for derived subject profiles). The
    `Option.elim False` form simultaneously checks that `toArgTemplate`
    succeeds on each input and that the resulting template's subject
    profile is well-formed. -/
theorem derived_subjects_wellformed :
    (toArgTemplate causativeResult).elim False
      (WellFormedInternal ·.subjectProfile) ∧
    (toArgTemplate pureManner).elim False
      (WellFormedInternal ·.subjectProfile) ∧
    (toArgTemplate pureResult).elim False
      (WellFormedInternal ·.subjectProfile) ∧
    (toArgTemplate propertyConcept).elim False
      (WellFormedInternal ·.subjectProfile) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show WellFormedInternal resultChange.subjectProfile; decide
  · show WellFormedInternal selfMotion.subjectProfile; decide
  · show WellFormedInternal unaccusativeCoS.subjectProfile; decide
  · show WellFormedInternal perception.subjectProfile; decide

-- ════════════════════════════════════════════════════
-- § 9. Grimm persistence placements
-- ════════════════════════════════════════════════════

section GrimmPlacements



/-! [grimm-2011]'s persistence bridge (`PersistenceLevel.fromPatientProfile`)
evaluated on the class-level object profiles — the canonical placements
consumed by `Studies/Grimm2011.lean` and `Studies/Beavers2010.lean`. -/

/-- Contact objects (kick, hit): no entailed change → total persistence.
    Follows [beavers-2011] eq. (60c) on surface contact; [grimm-2011]'s own
    Fig. 5 instead places contact objects at `quPersBeginning`. -/
theorem contactObject_persistence :
    PersistenceLevel.fromPatientProfile contactObject = .totalPersistence := rfl

/-- Created objects (build, invent): come into existence → `exPersEnd`. -/
theorem creationObject_persistence :
    PersistenceLevel.fromPatientProfile creationObject = .exPersEnd := rfl

/-- Consumed objects (eat, devour): cease to exist → `exPersBeginning`. -/
theorem consumptionObject_persistence :
    PersistenceLevel.fromPatientProfile consumptionObject = .exPersBeginning := rfl

/-- Disappearance-class subjects (die, vanish), read as patients: cease to
    exist → `exPersBeginning`. -/
theorem disappearance_subject_persistence :
    PersistenceLevel.fromPatientProfile disappearance.subjectProfile
      = .exPersBeginning := rfl

end GrimmPlacements

end ArgumentStructure
