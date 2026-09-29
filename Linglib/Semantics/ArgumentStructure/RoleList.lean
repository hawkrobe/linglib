module

public import Linglib.Semantics.ArgumentStructure.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Projection

/-!
# Argument-structure templates

This file defines role lists, the argument-structure generalizations that whole verb classes
share. A role list gives the entailment profile of a subject and of an optional object, in
realization order, and the named templates are the consensus role lists of verb classes such as
manner contact, change of state, creation, consumption and the psych verbs. The map from Levin's
verb classes onto the templates lives with the classes, and individual verbs can override a
template with their own entailments.

## Main definitions

* `RoleList`: the entailment profiles of a subject and an optional object.
* `RoleList.args`: the profiles of a role list, subject first.

## References

* [D. Dowty, *Thematic Proto-Roles and Argument Selection* (1991)][dowty-1991]
* [B. Levin, *English Verb Classes and Alternations: A Preliminary Investigation*
  (1993)][levin-1993]
* [B. Levin and M. Rappaport Hovav, *Argument Realization* (2005)][levin-rappaport-hovav-2005]
* [M. Rappaport Hovav and B. Levin, *Building Verb Meanings* (1998)][rappaport-hovav-levin-1998]
* [J. Beavers and A. Koontz-Garboden, *The Roots of Verbal Meaning*
  (2020)][beavers-koontz-garboden-2020]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [A. Belletti and L. Rizzi, *Psych-Verbs and θ-Theory* (1988)][belletti-rizzi-1988]
-/

@[expose] public section

namespace ArgumentStructure

/-- A verb class's role list gives the entailment profile of its subject and then of its object,
`none` for an intransitive. The stored order records the class's attested linking. Dowty's argument
selection principle derives it wherever one profile dominates the other, and it is a lexical choice
exactly at the ties behind the psych doublets (`roleList_not_asp_reversed`). -/
structure RoleList where
  subjectProfile : EntailmentProfile
  objectProfile : Option EntailmentProfile := none
  deriving DecidableEq, Repr

/-- `r.args` lists the profiles of the role list, subject first, as
[levin-rappaport-hovav-2005] (ch. 2) present role lists. -/
def RoleList.args (r : RoleList) : List EntailmentProfile :=
  r.subjectProfile :: r.objectProfile.toList

/-! ### Named templates

The consensus profiles of verb classes, which studies and fragments reference. -/

/-- An experiencer is sentient with respect to the event but neither volitional nor causal
([dowty-1991] (38)), and exists independently, by Dowty's generalization that every verb entailing
any of (27a–d) also entails the existence of its subject (p. 573). -/
def experiencerProfile : EntailmentProfile :=
  { sentience := true, independentExistence := true }

/-- A stimulus causes the experience without being sentient with respect to it
([dowty-1991] (38)). -/
def stimulusProfile : EntailmentProfile :=
  { causation := true, independentExistence := true }

/-- The object of the surface-contact classes is contacted but not changed, causally affected and
stationary without a change of state. [dowty-1991] attributes no change of state to the objects of
the hit class ((64 III)), and [beavers-2011] (60c) gives impact verbs only potential for change. -/
def contactObject : EntailmentProfile :=
  { causallyAffected := true, stationary := true }

/-- A created object changes state, is an incremental theme, is causally affected and does not
exist before the event ([dowty-1991] (30e)(i)). -/
def creationObject : EntailmentProfile :=
  { changeOfState := true, incrementalTheme := true, causallyAffected := true,
    dependentExistence := true }

/-- A consumed object is like a created one but exists before the event. That difference is what
lets `PersistenceLevel.fromPatientProfile` separate creation (`exPersEnd`) from consumption
(`exPersBeginning`). -/
def consumptionObject : EntailmentProfile :=
  { changeOfState := true, incrementalTheme := true, causallyAffected := true }

/-- In manner contact a full agent acts on an object it contacts without changing it. Manner verbs
lack result entailments ([beavers-koontz-garboden-2020]). -/
def mannerContact : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- In result change a full agent causes the object to change state, as result verbs entail
([beavers-koontz-garboden-2020]). -/
def resultChange : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some accomplishmentObjectProfile

/-- In creation a full agent brings the object into existence, an incremental theme whose extent
measures the event. -/
def creation : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some creationObject

/-- In consumption an agent consumes or destroys an incremental theme, as with the eat verbs
(Levin 39.1, *eat, drink*) and the devour verbs (39.4, *devour, consume, ingest*). It is creation
without dependent existence. -/
def consumption : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some consumptionObject

/-- In self-propelled motion the subject moves but causes no change in another participant, and
there is no object. -/
def selfMotion : RoleList where
  subjectProfile := activitySubjectProfile

/-- In perception the subject is a sentient, independently existing experiencer, neither volitional
nor causal. -/
def perception : RoleList where
  subjectProfile := experiencerProfile
  objectProfile  := some ⟨false, false, false, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer psych verbs (Levin 31.1, the amuse verbs; [belletti-rizzi-1988]) have a
causal stimulus as subject and an experiencer as object, the mirror image of `psychState`. -/
def psychCausal : RoleList where
  subjectProfile := stimulusProfile
  objectProfile  := some experiencerProfile

/-- Experiencer-subject psych verbs (Levin 31.2, the admire verbs *admire, like, love, fear, envy*)
have a sentient experiencer as subject and a causing stimulus as object ([dowty-1991] (38)). They
are the mirror image of `psychCausal`, the tie in argument selection behind the *like*/*please*
doublets (§8.3). Unlike the want verbs of `desire`, their subjects are entailed to be sentient. -/
def psychState : RoleList where
  subjectProfile := experiencerProfile
  objectProfile  := some stimulusProfile

/-- Desire verbs (Levin 32.1, *covet, crave, desire, need, want*) entail only the independent
existence of their subject. [dowty-1991] (29e) *John needs a new car* is among the "verbs that
entail subject existence but have none of (a)–(d)" (p. 573), so there is no entailment of
sentience, unlike the admire class (*this situation needs a solution*). The object is de dicto or
nonspecific, and so exists dependently ((30e)). -/
def desire : RoleList where
  subjectProfile := { independentExistence := true }
  objectProfile  := some { dependentExistence := true }

/-- Change of possession (Levin 13.1, the give verbs *give, lend, pass, sell*; 13.5, the verbs of
obtaining *buy, get, obtain*) has a volitional agent as subject without entailed movement, since
"both buyer and seller must act agentively (voluntarily)" ([dowty-1991] §3.2). Buyer and seller
have identical profiles, the tie behind the *buy*/*sell* doublet (§8.3). There is no object
profile, Dowty raising a "two Themes" worry about the goods and the currency (§3.2) and
attributing no entailments to the object. -/
def possessionTransfer : RoleList where
  subjectProfile := { volition := true, sentience := true, causation := true,
                      independentExistence := true }

/-- The manner subclass of the wipe verbs (Levin 10.4.1, *wipe, scrub, sweep, rub, wash*) has a
subject that only moves and exists independently, underspecified for volition, so that agentivity
is resolved pragmatically ([rappaport-hovav-levin-1998] on *sweep*, which [dowty-1991] does not
discuss). The object is contacted without an entailed change. -/
def wipeManner : RoleList where
  subjectProfile := { movement := true, independentExistence := true }
  objectProfile  := some contactObject

/-- The instrument subclass of the wipe verbs (Levin 10.4.2, *brush, comb, mop, vacuum*)
lexicalizes an instrument, which forces an obligatory volitional agent as subject;
[rappaport-hovav-levin-1998]'s canonical realization rule pairs instrument constants such as
*brush, hammer, saw, shovel* with the activity template. The subclass is not in the class map, so
`LevinClass.roleList .wipe` gives the manner subclass and verbs with the instrument sense override
it. -/
def wipeInstrument : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- An unaccusative change of state, the inchoative, has no external argument, and its subject
changes state and is causally affected without any agentive entailment. -/
def unaccusativeCoS : RoleList where
  subjectProfile := accomplishmentObjectProfile

/-- In unaccusative directed motion the subject moves and changes location. -/
def directedMotion : RoleList where
  subjectProfile := achievementSubjectProfile

/-- Disappearance verbs (Levin 48.2, *die, disappear, expire, perish, vanish*) have a sole argument
that changes state, is causally affected and exists dependently, since the effected argument
"will not exist after the event" ([dowty-1991] (30e)(i)). -/
def disappearance : RoleList where
  subjectProfile := { changeOfState := true, causallyAffected := true,
                      dependentExistence := true }

/-! ### Manner roots lack result entailments -/

/-- The object of the hit class does not change state, the generalization of
[beavers-koontz-garboden-2020] that manner roots lack result entailments. -/
theorem mannerContact_object_no_cos :
    (mannerContact.objectProfile.map (·.changeOfState)) = some false := rfl

/-! ### Derived role labels -/

/-- The subject of the hit class is an agent. -/
theorem hit_subject_role :
    mannerContact.subjectProfile.toRole = some .agent := by decide

/-- The object of the hit class, causally affected and stationary, is a patient. -/
theorem hit_object_role :
    contactObject.toRole = some .patient := by decide

/-- The subject of self-motion is an agent. -/
theorem selfMotion_subject_role :
    selfMotion.subjectProfile.toRole = some .agent := by decide

/-- The subject of perception is an experiencer. -/
theorem perception_subject_role :
    perception.subjectProfile.toRole = some .experiencer := by decide

/-- The subject of a stimulus-experiencer psych verb is a stimulus. -/
theorem psychCausal_subject_role :
    psychCausal.subjectProfile.toRole = some .stimulus := by decide

/-- The directed-motion subject is a theme, since the unaccusative subject of *arrive* moves and
changes location but is not causally affected, which is what distinguishes a patient from the
broader theme in [dowty-1991]. -/
theorem directedMotion_subject_role :
    directedMotion.subjectProfile.toRole = some .theme := by decide

/-- The subject of the admire class is an experiencer, and its stimulus object is exactly the
subject of the amuse class, the mirror behind the doublets ([dowty-1991] (38)). -/
theorem psychState_mirrors_psychCausal :
    psychState.subjectProfile.toRole = some .experiencer ∧
    psychState.objectProfile = some psychCausal.subjectProfile ∧
    psychCausal.objectProfile = some psychState.subjectProfile := by decide

/-- The sole argument of the disappearance class, as of *die*, is a patient, a pure
proto-patient. -/
theorem disappearance_subject_role :
    disappearance.subjectProfile.toRole = some .patient := by decide

end ArgumentStructure
