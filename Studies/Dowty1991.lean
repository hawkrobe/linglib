module

public import Linglib.Semantics.ArgumentStructure.Projection
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Data.ProtoRoles.Dowty1991

/-!
# Dowty (1991): Thematic proto-roles and argument selection

Dowty replaces thematic roles by two cluster concepts, the Proto-Agent and the Proto-Patient,
each a list of five entailments a predicate may impose on an argument, (27) and (28). The
Argument Selection Principle (31) lexicalizes as subject the argument with the most
Proto-Agent entailments and as direct object the one with the most Proto-Patient entailments.
Every argument profile here is read off a row of `Data/ProtoRoles/Dowty1991.json`, from the
single-entailment exemplars of (29) and (30) to the three verb classes of (64).

## Main results

* `alternates_iff`, `hierarchies`: Corollary 1 is the failure of (31) to select either way, and
  the role hierarchies of (36) follow from the principle.
* `primary_transitives`, `buy_sell`, `psych_doublet`: the primary transitive verbs of (35) are
  selected outright, while *buy* and *sell* and *like* and *please* tie.
* `directObjectOver_of_changeOfState`, `three_classes`: a change of state entailed for one
  nonsubject argument alone fixes it as direct object, so of the three classes of (64) only the
  break class does not alternate.
* `intransClass_unergative`, `intransClass_unaccusative`: the pure cells of Table 1.
* `primary_transitives_match_templates`: the substrate's class templates agree with the paper's
  attributions, save at three deliberate divergences.

## Implementation notes

A row's profile takes the attributions it states and treats what the paper leaves open as
absent, so the principle compares counts of stated entailments; the parenthesized (27e) and (28e)
count like the others. `Outranks` reads the Proto-Agent clause of (31) first and lets the
Proto-Patient clause decide ties, and "approximately equal" in the corollaries is read as equal.
The incremental theme homomorphism of §6 and the material of §11 are not represented.

## References

* [dowty-1991]
* [fillmore-1968]
-/

@[expose] public section

namespace Dowty1991

open ArgumentStructure
open scoped Finset

/-! ### The profile a row states -/

/-- The attribution a row makes about one entailment, stated present, stated absent, or left
open. -/
def ProtoRoleDatum.stated (d : ProtoRoleDatum) : ProtoRoleFeature → Option Bool
  | .volition => d.volition
  | .sentience => d.sentience
  | .causation => d.causation
  | .movement => d.movement
  | .independentExistence => d.independentExistence
  | .changeOfState => d.changeOfState
  | .incrementalTheme => d.incrementalTheme
  | .causallyAffected => d.causallyAffected
  | .stationary => d.stationary
  | .dependentExistence => d.dependentExistence

/-- The profile of a row's stated attributions, with what the paper leaves open absent. -/
def ProtoRoleDatum.profile (d : ProtoRoleDatum) : EntailmentProfile :=
  Finset.univ.filter fun f ↦ (d.stated f).getD false = true

@[simp] theorem ProtoRoleDatum.mem_profile {d : ProtoRoleDatum} {f : ProtoRoleFeature} :
    f ∈ d.profile ↔ (d.stated f).getD false = true := by
  simp [ProtoRoleDatum.profile]

/-- A profile agrees with every entailment a row states; what the row leaves open is
unconstrained. -/
def Matches (d : ProtoRoleDatum) (p : EntailmentProfile) : Prop :=
  ∀ f, ∀ b ∈ d.stated f, (f ∈ p ↔ b = true)

instance (d : ProtoRoleDatum) (p : EntailmentProfile) : Decidable (Matches d p) := by
  unfold Matches; infer_instance

theorem matches_profile (d : ProtoRoleDatum) : Matches d d.profile := fun f b h ↦ by
  simp [Option.mem_def.1 h]

/-! ### The selection principle and its corollaries, (31) to (34) -/

variable (p q : EntailmentProfile)

/-- By the selection principle (31), `p` is lexicalized as subject over `q` when it has strictly
more Proto-Agent entailments, or as many and strictly fewer Proto-Patient entailments. -/
def Outranks : Prop :=
  #q.protoAgent < #p.protoAgent ∨
    (#p.protoAgent = #q.protoAgent ∧ #p.protoPatient < #q.protoPatient)

/-- Two arguments with equal counts may be lexicalized either way, Corollary 1 (32). -/
def Alternates : Prop := #p.protoAgent = #q.protoAgent ∧ #p.protoPatient = #q.protoPatient

/-- Of two nonsubject arguments, the one with more Proto-Patient entailments is lexicalized as
direct object and the other as oblique, Corollary 2 (33). -/
def DirectObjectOver : Prop := #q.protoPatient < #p.protoPatient

/-- Two nonsubject arguments with equal Proto-Patient counts may either be direct object
(33). -/
def EitherObject : Prop := #p.protoPatient = #q.protoPatient

instance : Decidable (Outranks p q) := by unfold Outranks; infer_instance
instance : Decidable (Alternates p q) := by unfold Alternates; infer_instance
instance : Decidable (DirectObjectOver p q) := by unfold DirectObjectOver; infer_instance
instance : Decidable (EitherObject p q) := by unfold EitherObject; infer_instance

/-- Corollary 1 is exactly the failure of (31) to select either way. -/
theorem alternates_iff : Alternates p q ↔ ¬ Outranks p q ∧ ¬ Outranks q p := by
  unfold Alternates Outranks; omega

/-- The principle does not select uniquely (34): a profile ties with itself, so a relation
lexicalized twice with the arguments swapped is licensed. -/
theorem alternates_self : Alternates p p := ⟨rfl, rfl⟩

/-- One Proto-Agent entailment against none qualifies an argument for subject (§8.2). -/
theorem outranks_of_protoAgent_nonempty (hp : p.protoAgent.Nonempty) (hq : q.protoAgent = ∅) :
    Outranks p q :=
  .inl (by simpa [hq] using hp.card_pos)

/-- The hierarchies of (36) fall out of the principle over the canonical role profiles:
Agent over Instrument, Instrument and Experiencer over Patient, and Patient over Goal for
direct object. -/
theorem hierarchies :
    Outranks (ThetaRole.canonicalProfile .agent) (ThetaRole.canonicalProfile .instrument) ∧
      Outranks (ThetaRole.canonicalProfile .instrument) (ThetaRole.canonicalProfile .patient) ∧
      Outranks (ThetaRole.canonicalProfile .experiencer)
        (ThetaRole.canonicalProfile .patient) ∧
      DirectObjectOver (ThetaRole.canonicalProfile .patient)
        (ThetaRole.canonicalProfile .goal) := by
  decide

/-! ### The stable case and the ties, (35) and §8.3 -/

/-- In the primary transitive verbs of (35) a subject with four Proto-Agent entailments and no
Proto-Patient entailment faces an object with the reverse, and (31) selects outright. -/
theorem primary_transitives :
    Outranks Rows.buildSubject.profile Rows.buildObject.profile ∧
      Outranks Rows.writeSubject.profile Rows.writeObject.profile ∧
      Outranks Rows.murderSubject.profile Rows.murderObject.profile ∧
      Outranks Rows.eatSubject.profile Rows.eatObject.profile ∧
      Outranks Rows.washSubject.profile Rows.washObject.profile := by
  decide

/-- By Corollary 2, the theme of *put* and *remove*, changed and affected, outranks the
stationary goal or source for direct object (§8.2). -/
theorem put_remove :
    DirectObjectOver Rows.putTheme.profile Rows.putGoal.profile ∧
      DirectObjectOver Rows.removeTheme.profile Rows.removeSource.profile := by
  decide

/-- Buyer and seller are both volitional and otherwise alike, so *buy* and *sell* are licensed
as a doublet (§3.2, §8.3). -/
theorem buy_sell : Alternates Rows.buySubject.profile Rows.buySeller.profile ∧
    Alternates Rows.sellSubject.profile Rows.sellBuyer.profile := by
  decide

/-- The experiencer is sentient and the stimulus causal, one Proto-Agent entailment each, so
*like* and *please* tie (38). -/
theorem psych_doublet :
    Alternates Rows.likeSubject.profile Rows.likeObject.profile ∧
      Alternates Rows.pleaseObject.profile Rows.pleaseSubject.profile := by
  decide

/-- Under the inchoative interpretation the experiencer undergoes a change of state, the
Proto-Patient entailment that selects the stimulus as subject, which is Croft's generalization
that only stimulus-subject psych verbs take the inchoative reading (§9.2). -/
theorem inchoative_stimulus_subject :
    Outranks Rows.surpriseSubject.profile Rows.surpriseObjectInchoative.profile := by
  decide

/-! ### Partially symmetric interactive predicates, §9.1 -/

/-- The subject of *kiss*, entailed volitional. -/
def kissSubjectProfile : EntailmentProfile := Rows.kissSubject.profile

/-- The object of *kiss*, not entailed volitional. -/
def kissObjectProfile : EntailmentProfile := Rows.kissObject.profile

/-- Volition, entailed for the subject alone, selects it, (43); with symmetric volition the
collective subject of (42) is a tie. -/
theorem kiss_subject_outranks :
    Outranks kissSubjectProfile kissObjectProfile ∧
      Alternates kissSubjectProfile kissSubjectProfile := by
  decide

/-- The entailment distinguishing the subject of *collide* from its oblique is motion, not
volition (45). -/
theorem collide_subject_outranks :
    Outranks Rows.collideSubject.profile Rows.collideObject.profile := by
  decide

/-! ### Alternations in direct versus oblique objects, §9.3 and (64) -/

/-- Two nonsubject arguments agree on the change-of-state entailment. -/
def CosSymmetric : Prop := .changeOfState ∈ p ↔ .changeOfState ∈ q

instance : Decidable (CosSymmetric p q) := by unfold CosSymmetric; infer_instance

/-- A change of state entailed for one nonsubject argument but not the other, the remaining
Proto-Patient entailments being equal, fixes it as direct object (§9.3.3). -/
theorem directObjectOver_of_changeOfState (hp : .changeOfState ∈ p) (hq : .changeOfState ∉ q)
    (h : p.protoPatient.erase .changeOfState = q.protoPatient.erase .changeOfState) :
    DirectObjectOver p q := by
  have hp' : .changeOfState ∈ p.protoPatient := Finset.mem_inter.2 ⟨hp, by decide⟩
  have hq' : .changeOfState ∉ q.protoPatient := fun h ↦ hq (Finset.mem_inter.1 h).1
  unfold DirectObjectOver
  rw [← Finset.card_erase_add_one hp', h, Finset.erase_eq_of_notMem hq']
  omega

/-- Nonsubject arguments alike in the change-of-state entailment and the rest may either
be direct object. -/
theorem eitherObject_of_cosSymmetric (h : CosSymmetric p q)
    (h' : p.protoPatient.erase .changeOfState = q.protoPatient.erase .changeOfState) :
    EitherObject p q := by
  have : p.protoPatient = q.protoPatient := by
    ext f
    by_cases hf : f = .changeOfState
    · subst hf
      simp only [EntailmentProfile.protoPatient, Finset.mem_inter]
      exact and_congr_left fun _ ↦ h
    · simpa [hf] using congrArg (f ∈ ·) h'
  unfold EitherObject; rw [this]

/-- The hay and the truck of (49), (64 I), which both change state. -/
def sprayLoadTheme : EntailmentProfile := Rows.loadTheme.profile

def sprayLoadLocation : EntailmentProfile := Rows.loadLocation.profile

/-- The fence and the stick of (63), (64 II), of which only the direct object changes state. -/
def breakDirectObject : EntailmentProfile := Rows.breakObject.profile

def breakInstrument : EntailmentProfile := Rows.breakInstrument.profile

/-- The fence and the stick of (62), (64 III), neither of which changes state or measures the
event. -/
def hitArg1 : EntailmentProfile := Rows.hitObject.profile

def hitArg2 : EntailmentProfile := Rows.hitInstrument.profile

/-- The spray/load class alternates, the break class fixes its direct object, and the hit class
alternates with complete synonymy (64). -/
theorem three_classes :
    EitherObject sprayLoadTheme sprayLoadLocation ∧
      DirectObjectOver breakDirectObject breakInstrument ∧
      EitherObject hitArg1 hitArg2 := by
  decide

/-- In the hit class puzzle the instrument moves, a Proto-Agent entailment the principle leaves
out of object selection (§9.3.3). -/
theorem hit_instrument_moves : #hitArg2.protoAgent = 1 ∧ #hitArg1.protoAgent = 0 := by
  decide

/-! ### The unaccusative hypothesis, §12 -/

/-- The three cases of Table 1, the two pure cells and the two mixed cells that vary across
languages. -/
inductive IntransClass
  | unergative
  | unaccusative
  | unstable
  deriving DecidableEq, Repr

/-- Table 1 crosses agentivity with telicity. -/
def table1 : Bool → Bool → IntransClass
  | true, false => .unergative
  | false, true => .unaccusative
  | _, _ => .unstable

/-- The most important Proto-Agent entailment for the contrast: volition. -/
def Agentive : Prop := .volition ∈ p

/-- The most important Proto-Patient property for the contrast: an incremental or holistic
theme, that is, telicity. -/
def Telic : Prop := .incrementalTheme ∈ p ∨ .changeOfState ∈ p

instance : DecidablePred Agentive := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

instance : DecidablePred Telic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The class Table 1 assigns to an intransitive by its sole argument's profile. -/
def intransClass : IntransClass := table1 (decide (Agentive p)) (decide (Telic p))

/-- Predicates high in agentivity and low in patient properties are invariably
unergative. -/
theorem intransClass_unergative (h : Agentive p) (h' : ¬ Telic p) :
    intransClass p = .unergative := by
  simp only [intransClass, decide_eq_true h, decide_eq_false h', table1]

/-- Predicates low in agentivity and high in patient properties are invariably
unaccusative. -/
theorem intransClass_unaccusative (h : ¬ Agentive p) (h' : Telic p) :
    intransClass p = .unaccusative := by
  simp only [intransClass, decide_eq_false h, decide_eq_true h', table1]

/-- *run* is unergative and *die* and *arrive* unaccusative, from the substrate's class
profiles. -/
theorem intransClass_examples :
    intransClass selfMotion.subjectProfile = .unergative ∧
      intransClass disappearance.subjectProfile = .unaccusative ∧
      intransClass directedMotion.subjectProfile = .unaccusative := by
  decide

/-! ### The substrate's templates against the paper's attributions -/

/-- The (35) attributions hold of the accomplishment templates and the creation and
consumption objects. -/
theorem primary_transitives_match_templates :
    Matches Rows.buildSubject accomplishmentSubjectProfile ∧
      Matches Rows.writeSubject accomplishmentSubjectProfile ∧
      Matches Rows.murderSubject accomplishmentSubjectProfile ∧
      Matches Rows.eatSubject accomplishmentSubjectProfile ∧
      Matches Rows.washSubject accomplishmentSubjectProfile ∧
      Matches Rows.murderObject accomplishmentObjectProfile ∧
      Matches Rows.washObject accomplishmentObjectProfile ∧
      Matches Rows.writeObject creationObject ∧
      Matches Rows.eatObject consumptionObject := by
  decide

/-- The hit class attributions, (64 III), hold of the contacted object template. -/
theorem hit_class_matches_contact_object : Matches Rows.hitObject contactObject := by decide

/-- The single-entailment exemplars of (29) and (30) land in the perception and desire
templates. -/
theorem exemplars_match_templates :
    Matches Rows.seeSubject perception.subjectProfile ∧
      Matches Rows.needSubject desire.subjectProfile ∧
      desire.objectProfile.all (Matches Rows.needObject ·) ∧
      desire.objectProfile.all (Matches Rows.seekObject ·) := by
  decide

/-- The psych-state and desire templates split as the paper does: the *like* experiencer is
sentient, (38), and the *need* subject entails existence but none of (27a) to (27d). -/
theorem psych_desire_split :
    Matches Rows.likeSubject psychState.subjectProfile ∧
      Matches Rows.needSubject desire.subjectProfile ∧
      ¬ Matches Rows.needSubject psychState.subjectProfile := by
  decide

/-- The creation template omits (28d), which "all of 28" for the object of *build* includes:
the template follows the (35) hedge that creation objects are only mostly stationary. -/
theorem build_object_stationary_divergence :
    ¬ Matches Rows.buildObject creationObject ∧
      Matches Rows.buildObject (insert .stationary creationObject) := by
  decide

/-- The accomplishment object template carries no incremental themehood, which (64 II)
attributes to the object of *break*; the template adds it per verb. -/
theorem break_object_it_divergence :
    ¬ Matches Rows.breakObject accomplishmentObjectProfile ∧
      Matches Rows.breakObject (insert .incrementalTheme accomplishmentObjectProfile) := by
  decide

/-- (30e) counts destruction as dependent existence, which the paper never states for the
object of *eat*; the consumption template omits it because adding it moves the object from
the consumption to the creation persistence level. -/
theorem eat_object_de_tension :
    Matches Rows.eatObject consumptionObject ∧
      PersistenceLevel.fromPatientProfile consumptionObject = .exPersBeginning ∧
      PersistenceLevel.fromPatientProfile
        (insert .dependentExistence consumptionObject) = .exPersEnd := by
  decide

end Dowty1991
