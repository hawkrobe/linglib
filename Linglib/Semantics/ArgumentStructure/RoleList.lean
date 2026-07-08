import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.ArgumentStructure.Projection

/-!
# Argument-structure templates

[levin-1993] [dowty-1991] [beavers-2010] [beavers-koontz-garboden-2020]
[rappaport-hovav-levin-1998]

A `RoleList` pairs a subject with an optional object `EntailmentProfile` —
the argument-structure generalization a whole verb class shares. The named
templates are the class-level consensus rows (manner vs result vs creation
vs psych ...); the map from [levin-1993]'s class inventory onto them lives
with the classes (`Semantics/Verb/Class.lean`), and individual verbs can
override via explicit `subjectEntailments`/`objectEntailments` on `Verb`.
-/

namespace ArgumentStructure

/-- A verb class's semantic role list, in realization order: the subject's
    entailment set, then the object's (`none` for intransitives). The
    stored order records the class's attested linking; the ASP derives it
    wherever dominance is strict, and it is a genuine lexical choice
    exactly at the alternation ties (the psych doublets) — see
    `roleList_linking_asp_sanctioned` in `Semantics/Verb/Class.lean`. -/
structure RoleList where
  subjectProfile : EntailmentProfile
  objectProfile : Option EntailmentProfile := none
  deriving DecidableEq, Repr

/-- The role list as a list, subject first ([levin-rappaport-hovav-2005]
    ch. 2's presentation shape). -/
def RoleList.args (r : RoleList) : List EntailmentProfile :=
  r.subjectProfile :: r.objectProfile.toList

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
def mannerContact : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- Full agent causing change of state in the object.
    Subject: V+S+C+M+IE. Object: CoS+CA (causally affected, changed).
    [beavers-2010]: "quantized" affectedness — the verb entails
    a definite change of state (the object reaches an end state).
    [beavers-koontz-garboden-2020]: result verbs entail CoS. -/
def resultChange : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some accomplishmentObjectProfile

/-- Full agent creating an entity (object comes into existence).
    Subject: V+S+C+M+IE. Object: CoS+IT+CA+DE.
    [beavers-2010]: quantized affectedness + dependent existence.
    The object is an incremental theme whose extent measures the event. -/
def creation : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some creationObject

/-- Agent consuming/destroying an incremental theme (Levin 39.1 eat verbs:
    *eat, drink*; 39.4 devour verbs: *devour, consume, ingest*).
    Subject: V+S+C+M+IE. Object: CoS+IT+CA.
    Like creation but without dependent existence (the object
    pre-exists the event). -/
def consumption : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some consumptionObject

/-- Self-propelled motion (no caused result, no object).
    Subject: V+S+M+IE (no causation — the mover doesn't cause
    a change in another participant). -/
def selfMotion : RoleList where
  subjectProfile := activitySubjectProfile

/-- Perception / experiencer-subject.
    Subject: S+IE (sentient, independently existing, but not
    volitional or causal). -/
def perception : RoleList where
  subjectProfile := experiencerProfile
  objectProfile  := some ⟨false, false, false, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer (Class II psych, Levin 31.1 amuse verbs;
    [belletti-rizzi-1988]). Subject: C+IE (causal stimulus). Object: S+IE
    (experiencer). Mirror image of `psychState`. -/
def psychCausal : RoleList where
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
def psychState : RoleList where
  subjectProfile := experiencerProfile
  objectProfile  := some stimulusProfile

/-- Desire states (Levin 32.1 want verbs: *covet, crave, desire, need,
    want*). Subject: independent existence ALONE — [dowty-1991] (29e) "John
    needs a new car", glossed p. 573 as "verbs that entail subject existence
    but have none of (a)–(d)": NO sentience entailment, unlike the admire
    class (*this situation needs a solution*). Object: de dicto/nonspecific,
    so dependent existence — (30e) "John needs a car/seeks a unicorn ...
    (de dicto objects: no existence)". -/
def desire : RoleList where
  subjectProfile := { independentExistence := true }
  objectProfile  := some { dependentExistence := true }

/-- Change of possession (Levin 13.1 give verbs: *give, lend, pass, sell*;
    13.5 verbs of obtaining: *buy, get, obtain*). Subject: volitional agent
    without entailed movement (V+S+C+IE) — [dowty-1991] §3.2: "both buyer
    and seller must act agentively (voluntarily)". Buyer and seller profiles
    are identical; that is the §8.3 argument-selection tie behind the
    *buy*/*sell* doublet. No object profile: Dowty flags the goods/currency
    "two Themes" worry (§3.2) and attributes no object entailments. -/
def possessionTransfer : RoleList where
  subjectProfile := { volition := true, sentience := true, causation := true,
                      independentExistence := true }

/-- Surface-contact manner (Levin 10.4.1 wipe verbs, manner subclass:
    *wipe, scrub, sweep, rub, wash*). Subject: M+IE only — underspecified
    for volition, so agentivity is pragmatically resolved
    ([rappaport-hovav-levin-1998] on *sweep*; [dowty-1991] never discusses
    *sweep*). Object: contacted, no entailed change ([beavers-2010]
    potential affectedness). -/
def wipeManner : RoleList where
  subjectProfile := { movement := true, independentExistence := true }
  objectProfile  := some contactObject

/-- Instrument subclass of the wipe verbs (Levin 10.4.2: *brush, comb, mop,
    vacuum*; [rappaport-hovav-levin-1998]'s *sweep with a broom*): instrument
    lexicalization forces an obligatory volitional agent (V+S+C+M+IE).
    Not in the class map — `LevinClass.roleList .wipe` gives the manner
    subclass default; instrument-sense entries override per verb. -/
def wipeInstrument : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- Unaccusative change of state (inchoative).
    Subject: CoS+CA (undergoes change, no agentive features).
    No external argument. -/
def unaccusativeCoS : RoleList where
  subjectProfile := accomplishmentObjectProfile

/-- Directed motion (unaccusative).
    Subject: M+IE+CoS (moves, changes location). -/
def directedMotion : RoleList where
  subjectProfile := achievementSubjectProfile

/-- Disappearance (Levin 48.2: *die, disappear, expire, perish, vanish* —
    "describe the disappearance or going out of existence of some entity").
    Sole argument: CoS+CA+DE — like `unaccusativeCoS` plus dependent
    existence, since the argument goes out of existence ([dowty-1991]
    (30e)(i): the effected argument "will not exist after the event"). -/
def disappearance : RoleList where
  subjectProfile := { changeOfState := true, causallyAffected := true,
                      dependentExistence := true }

-- ════════════════════════════════════════════════════
-- § 2. Manner roots lack result entailments
-- ════════════════════════════════════════════════════

/-- Hit-class object lacks CoS (manner verbs don't entail change of state) —
    the Beavers & Koontz-Garboden generalization that manner roots lack result
    entailments, read off the class-level template. -/
theorem mannerContact_object_no_cos :
    (mannerContact.objectProfile.map (·.changeOfState)) = some false := rfl

-- ════════════════════════════════════════════════════
-- § 3. Derived role labels match expectations
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
