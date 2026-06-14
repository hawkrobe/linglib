import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.Lexical.LevinTheory

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

namespace Features.LevinClassProfiles

open Semantics.Lexical
open Semantics.ArgumentStructure.EntailmentProfile

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

/-- Full agent acting on a contacted but unaffected object.
    Subject: V+S+C+M+IE. Object: CA+St (no CoS).
    [beavers-2010]: "unspecified" affectedness — the verb's
    truth conditions don't entail a change of state in the object.
    [beavers-koontz-garboden-2020]: manner verbs lack result
    entailments. -/
def mannerContact : ArgTemplate where
  subjectProfile := ⟨true, true, true, true, true,  false, false, false, false, false⟩
  objectProfile  := some ⟨false, false, false, false, false, false, false, true, true, false⟩

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
  objectProfile  := some ⟨false, false, false, false, false, true, true, true, false, true⟩

/-- Agent consuming/destroying an incremental theme.
    Subject: V+S+C+M+IE. Object: CoS+IT+CA.
    Like creation but without dependent existence (the object
    pre-exists the event). -/
def consumption : ArgTemplate where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some ⟨false, false, false, false, false, true, true, true, false, false⟩

/-- Self-propelled motion (no caused result, no object).
    Subject: V+S+M+IE (no causation — the mover doesn't cause
    a change in another participant). -/
def selfMotion : ArgTemplate where
  subjectProfile := activitySubjectProfile

/-- Perception / experiencer-subject.
    Subject: S+IE (sentient, independently existing, but not
    volitional or causal). -/
def perception : ArgTemplate where
  subjectProfile := stateSubjectProfile
  objectProfile  := some ⟨false, false, false, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer (Class II psych, [belletti-rizzi-1988]).
    Subject: C+IE (causal stimulus). Object: S+IE (experiencer). -/
def psychCausal : ArgTemplate where
  subjectProfile := ⟨false, false, true, false, true,  false, false, false, false, false⟩
  objectProfile  := some stateSubjectProfile

/-- Unaccusative change of state (inchoative).
    Subject: CoS+CA (undergoes change, no agentive features).
    No external argument. -/
def unaccusativeCoS : ArgTemplate where
  subjectProfile := accomplishmentObjectProfile

/-- Directed motion (unaccusative).
    Subject: M+IE+CoS (moves, changes location). -/
def directedMotion : ArgTemplate where
  subjectProfile := achievementSubjectProfile

-- ════════════════════════════════════════════════════
-- § 3. LevinClass → ArgTemplate
-- ════════════════════════════════════════════════════

end Features.LevinClassProfiles

namespace Semantics.Lexical
open Features.LevinClassProfiles
open Semantics.ArgumentStructure.EntailmentProfile

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

end Semantics.Lexical

namespace Features.LevinClassProfiles
open Semantics.Lexical
open Semantics.ArgumentStructure.EntailmentProfile
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
    kickObjectProfile.toRole = some .patient := by decide

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
      (·.subjectProfile.WellFormedInternal) ∧
    (toArgTemplate pureManner).elim False
      (·.subjectProfile.WellFormedInternal) ∧
    (toArgTemplate pureResult).elim False
      (·.subjectProfile.WellFormedInternal) ∧
    (toArgTemplate propertyConcept).elim False
      (·.subjectProfile.WellFormedInternal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show resultChange.subjectProfile.WellFormedInternal; decide
  · show selfMotion.subjectProfile.WellFormedInternal; decide
  · show unaccusativeCoS.subjectProfile.WellFormedInternal; decide
  · show perception.subjectProfile.WellFormedInternal; decide

end Features.LevinClassProfiles
