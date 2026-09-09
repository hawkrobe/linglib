import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Data.ProtoRoles.Dowty1991

/-!
# Dowty (1991): Thematic Proto-Roles and Argument Selection

This file formalizes the argument selection theory of [dowty-1991]. Thematic roles are
replaced by two cluster concepts, the Proto-Agent and Proto-Patient, each a list of five
entailments a predicate may impose on an argument, (27) and (28), the substrate's
`ArgumentStructure.EntailmentProfile`; the per-argument attributions the paper states, from
the single-entailment exemplars of (29) and (30) to the three verb classes of (64), are the
rows of `Data/ProtoRoles/Dowty1991.json`, and every argument profile here is read off a
row, `ProtoRoleDatum.profile`. The Argument Selection
Principle, (31), lexicalizes as subject the argument with the greatest number of Proto-Agent
entailments and as direct object the one with the greatest number of Proto-Patient
entailments, `Outranks`; its first corollary, (32), lets equal counts be lexicalized either
way, `Alternates`, and its second, (33), selects among the nonsubject arguments of a
three-place predicate the one with more Proto-Patient entailments as direct object,
`DirectObjectOver`. The primary transitive verbs of (35) are the stable case; the role
hierarchies of (36) fall out of the principle over the canonical role profiles; the doublets
*buy* and *sell* and *like* and *please* are ties, (38), which Croft's inchoative
interpretation breaks in favour of the stimulus subject, §9.2; the partially symmetric
interactive predicates of §9.1 entail volition, or with *collide* motion, for the subject
alone. The three classes of direct and oblique object alternation are (64): a change of
state entailed for one nonsubject argument but not the other fixes it as direct object,
`directObjectOver_of_changeOfState`, so *break* does not alternate, while the spray/load
class with change of state in both arguments and the hit class with it in neither do,
`eitherObject_of_cosSymmetric`. Table 1 of §12 classifies intransitives by agentivity and
telicity, `intransClass`: agentive atelic predicates are invariably unergative and
non-agentive telic ones invariably unaccusative, the mixed cells varying across languages.
The final section checks the substrate's class-level templates against the paper's rows,
`Matches`, and records the three points at which the templates deliberately diverge.

## Implementation notes

A row's profile takes the attributions it states and treats what the paper leaves open as
absent, so the counts the principle compares are counts of stated entailments; the
parenthesized entailments (27e) and (28e) count like the others. `Outranks` reads the two
clauses of (31) with the Proto-Agent clause first and the Proto-Patient clause deciding ties,
which is how the inchoative psych verbs of §9.2 are selected; "approximately equal" in the
corollaries is read as equal. Telicity in Table 1 is incremental themehood or a change of
state, the paper's "incremental or holistic theme". The incremental theme homomorphism of
§6, the representation-source predicates of §9.3.4, and the psycholinguistic and typological
material of §11 are not represented.

## References

* [dowty-1991]
* [fillmore-1968]
-/

namespace Dowty1991

open ArgumentStructure

/-! ### The profile a row states -/

/-- The attribution a row makes about one entailment: stated present, stated absent, or
left open. -/
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
  EntailmentProfile.equivFeatures.symm λ f => (d.stated f).getD false

theorem ProtoRoleDatum.feature_profile (d : ProtoRoleDatum) (f : ProtoRoleFeature) :
    d.profile.feature f = (d.stated f).getD false :=
  congrFun (EntailmentProfile.equivFeatures.apply_symm_apply _) f

/-- A profile agrees with every entailment a row states; what the row leaves open is
unconstrained. -/
def Matches (d : ProtoRoleDatum) (p : EntailmentProfile) : Prop :=
  ∀ f b, d.stated f = some b → p.feature f = b

instance (d : ProtoRoleDatum) (p : EntailmentProfile) : Decidable (Matches d p) := by
  unfold Matches; infer_instance

theorem matches_profile (d : ProtoRoleDatum) : Matches d d.profile := λ f b h => by
  rw [ProtoRoleDatum.feature_profile, h]; rfl

/-! ### The selection principle and its corollaries, (31) to (34) -/

variable (p q : EntailmentProfile)

/-- (31): `p` is lexicalized as subject over `q` when it has strictly more Proto-Agent
entailments, or as many and strictly fewer Proto-Patient entailments. -/
def Outranks : Prop :=
  q.pAgentScore < p.pAgentScore ∨
    (p.pAgentScore = q.pAgentScore ∧ p.pPatientScore < q.pPatientScore)

/-- (32), Corollary 1: two arguments with equal counts may be lexicalized either way. -/
def Alternates : Prop := p.pAgentScore = q.pAgentScore ∧ p.pPatientScore = q.pPatientScore

/-- (33), Corollary 2: of two nonsubject arguments, the one with more Proto-Patient
entailments is lexicalized as direct object and the other as oblique. -/
def DirectObjectOver : Prop := q.pPatientScore < p.pPatientScore

/-- (33): two nonsubject arguments with equal Proto-Patient counts may either be direct
object. -/
def EitherObject : Prop := p.pPatientScore = q.pPatientScore

instance : Decidable (Outranks p q) := by unfold Outranks; infer_instance
instance : Decidable (Alternates p q) := by unfold Alternates; infer_instance
instance : Decidable (DirectObjectOver p q) := by unfold DirectObjectOver; infer_instance
instance : Decidable (EitherObject p q) := by unfold EitherObject; infer_instance

/-- Corollary 1 is exactly the failure of (31) to select either way. -/
theorem alternates_iff : Alternates p q ↔ ¬ Outranks p q ∧ ¬ Outranks q p := by
  unfold Alternates Outranks; omega

/-- (34): the principle does not select uniquely; a profile ties with itself, so a relation
lexicalized twice with the arguments swapped is licensed. -/
theorem alternates_self : Alternates p p := ⟨rfl, rfl⟩

/-- §8.2: one Proto-Agent entailment against none qualifies an argument for subject. -/
theorem outranks_of_pAgentScore_pos (hp : 0 < p.pAgentScore) (hq : q.pAgentScore = 0) :
    Outranks p q :=
  Or.inl (hq ▸ hp)

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

/-- The primary transitive verbs of (35): a subject with four Proto-Agent entailments and
no Proto-Patient entailment against an object with the reverse, (31) selecting outright. -/
theorem primary_transitives :
    Outranks Rows.buildSubject.profile Rows.buildObject.profile ∧
      Outranks Rows.writeSubject.profile Rows.writeObject.profile ∧
      Outranks Rows.murderSubject.profile Rows.murderObject.profile ∧
      Outranks Rows.eatSubject.profile Rows.eatObject.profile ∧
      Outranks Rows.washSubject.profile Rows.washObject.profile := by
  decide

/-- Corollary 2 on *put* and *remove*, §8.2: the theme, changed and affected, outranks the
stationary goal or source for direct object. -/
theorem put_remove :
    DirectObjectOver Rows.putTheme.profile Rows.putGoal.profile ∧
      DirectObjectOver Rows.removeTheme.profile Rows.removeSource.profile := by
  decide

/-- §3.2 and §8.3: buyer and seller are both volitional and otherwise alike, so *buy* and
*sell* are licensed as a doublet. -/
theorem buy_sell : Alternates Rows.buySubject.profile Rows.buySeller.profile ∧
    Alternates Rows.sellSubject.profile Rows.sellBuyer.profile := by
  decide

/-- (38): the experiencer is sentient and the stimulus causal, one Proto-Agent entailment
each, so *like* and *please* tie. -/
theorem psych_doublet :
    Alternates Rows.likeSubject.profile Rows.likeObject.profile ∧
      Alternates Rows.pleaseObject.profile Rows.pleaseSubject.profile := by
  decide

/-- §9.2: under the inchoative interpretation the experiencer undergoes a change of state,
the Proto-Patient entailment that selects the stimulus as subject; Croft's generalization
that only stimulus-subject psych verbs take the inchoative reading. -/
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

/-- *collide*, (45): the entailment distinguishing subject from oblique is motion, not
volition. -/
theorem collide_subject_outranks :
    Outranks Rows.collideSubject.profile Rows.collideObject.profile := by
  decide

/-! ### Alternations in direct versus oblique objects, §9.3 and (64) -/

/-- Two nonsubject arguments agree on the change-of-state entailment. -/
def CosSymmetric : Prop := p.changeOfState = q.changeOfState

instance : Decidable (CosSymmetric p q) := by unfold CosSymmetric; infer_instance

/-- §9.3.3: a change of state entailed for one nonsubject argument but not the other, the
remaining Proto-Patient entailments being equal, fixes it as direct object. -/
theorem directObjectOver_of_changeOfState (hp : p.changeOfState = true)
    (hq : q.changeOfState = false) (hIT : p.incrementalTheme = q.incrementalTheme)
    (hCA : p.causallyAffected = q.causallyAffected) (hSt : p.stationary = q.stationary)
    (hDE : p.dependentExistence = q.dependentExistence) : DirectObjectOver p q := by
  unfold DirectObjectOver EntailmentProfile.pPatientScore
  rw [hp, hq, hIT, hCA, hSt, hDE]
  simp only [Bool.toNat_true, Bool.toNat_false]
  omega

/-- Nonsubject arguments alike in the change-of-state entailment and the rest may either
be direct object. -/
theorem eitherObject_of_cosSymmetric (h : CosSymmetric p q)
    (hIT : p.incrementalTheme = q.incrementalTheme)
    (hCA : p.causallyAffected = q.causallyAffected) (hSt : p.stationary = q.stationary)
    (hDE : p.dependentExistence = q.dependentExistence) : EitherObject p q := by
  unfold EitherObject EntailmentProfile.pPatientScore
  rw [h, hIT, hCA, hSt, hDE]

/-- The hay and the truck of (49), (64 I): both change state. -/
def sprayLoadTheme : EntailmentProfile := Rows.loadTheme.profile

def sprayLoadLocation : EntailmentProfile := Rows.loadLocation.profile

/-- The fence and the stick of (63), (64 II): only the direct object changes state. -/
def breakDirectObject : EntailmentProfile := Rows.breakObject.profile

def breakInstrument : EntailmentProfile := Rows.breakInstrument.profile

/-- The fence and the stick of (62), (64 III): neither changes state nor measures the
event. -/
def hitArg1 : EntailmentProfile := Rows.hitObject.profile

def hitArg2 : EntailmentProfile := Rows.hitInstrument.profile

/-- (64): the spray/load class alternates, the break class fixes its direct object, and the
hit class alternates with complete synonymy. -/
theorem three_classes :
    EitherObject sprayLoadTheme sprayLoadLocation ∧
      DirectObjectOver breakDirectObject breakInstrument ∧
      EitherObject hitArg1 hitArg2 := by
  decide

/-- The hit class puzzle, §9.3.3: the instrument moves, a Proto-Agent entailment the
principle leaves out of object selection. -/
theorem hit_instrument_moves : hitArg2.pAgentScore = 1 ∧ hitArg1.pAgentScore = 0 := by
  decide

/-! ### The unaccusative hypothesis, §12 -/

/-- The three cases of Table 1: the two pure cells and the two mixed cells that vary
across languages. -/
inductive IntransClass
  | unergative
  | unaccusative
  | unstable
  deriving DecidableEq, Repr

/-- Table 1: agentivity crossed with telicity. -/
def table1 : Bool → Bool → IntransClass
  | true, false => .unergative
  | false, true => .unaccusative
  | _, _ => .unstable

/-- The most important Proto-Agent entailment for the contrast: volition. -/
def Agentive : Prop := p.volition = true

/-- The most important Proto-Patient property for the contrast: an incremental or holistic
theme, that is, telicity. -/
def Telic : Prop := p.incrementalTheme = true ∨ p.changeOfState = true

instance : DecidablePred Agentive := λ p => by unfold Agentive; infer_instance

instance : DecidablePred Telic := λ p => by unfold Telic; infer_instance

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
      Matches Rows.buildObject { creationObject with stationary := true } := by
  decide

/-- The accomplishment object template carries no incremental themehood, which (64 II)
attributes to the object of *break*; the template adds it per verb. -/
theorem break_object_it_divergence :
    ¬ Matches Rows.breakObject accomplishmentObjectProfile ∧
      Matches Rows.breakObject { accomplishmentObjectProfile with incrementalTheme := true } := by
  decide

/-- (30e) counts destruction as dependent existence, which the paper never states for the
object of *eat*; the consumption template omits it because adding it moves the object from
the consumption to the creation persistence level. -/
theorem eat_object_de_tension :
    Matches Rows.eatObject consumptionObject ∧
      PersistenceLevel.fromPatientProfile consumptionObject = .exPersBeginning ∧
      PersistenceLevel.fromPatientProfile
        { consumptionObject with dependentExistence := true } = .exPersEnd := by
  decide

end Dowty1991
