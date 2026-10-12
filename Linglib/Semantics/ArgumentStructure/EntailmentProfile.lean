module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype

/-!
# Proto-role entailment profiles

An `EntailmentProfile` is the set of Dowty's ten proto-role entailments a verb imposes on one of
its arguments. Proto-Agent and Proto-Patient are cluster concepts: each is a set of five
entailments, and an argument's agenthood and patienthood are the parts of its profile that fall in
each cluster, `protoAgent` and `protoPatient`. Following Grimm, the Argument Selection Principle
is stated by inclusion: subjecthood tracks strict inclusion of Proto-Agent parts, Proto-Patient
inclusion breaking ties.

## Main definitions

* `EntailmentProfile`: the entailments a verb imposes on an argument.
* `EntailmentProfile.protoAgent`, `EntailmentProfile.protoPatient`: its parts in the two
  clusters.
* `OutranksForSubject`: the Argument Selection Principle by inclusion.
* `activitySubjectProfile`, …, `accomplishmentObjectProfile`: Rappaport Hovav and Levin's
  template-level defaults.

## Implementation notes

The entailments are not independent: volition presupposes sentience (`WellFormedInternal`).
Since profiles are sets, `p ⊆ q` is entailment inclusion and `p ∪ q` imposes both profiles'
entailments, Reinhart and Siloni's role bundling; Davis and Koenig's causation priority needs no
extra clause. Dowty's flat principle counts the parts, in `Studies/Dowty1991.lean`, and the
projection to Grimm's agentivity lattice is in `Projection.lean`.

## References

* [dowty-1991]
* [grimm-2011]
* [davis-koenig-2000]
* [levin-2019]
* [reinhart-siloni-2005]
* [rappaport-hovav-levin-1998]
-/

@[expose] public section

namespace ArgumentStructure

/-- Three-valued volitional involvement of a participant, `neutral` where a form
leaves it open. -/
inductive Volitionality where
  | nonvolitional
  | neutral
  | volitional
  deriving DecidableEq, Repr

/-- The ten entailments defining the proto-roles ([dowty-1991] pp.572–573): the first five are
Proto-Agent, the last five Proto-Patient. -/
inductive ProtoRoleFeature where
  /-- Volitional involvement in the event. -/
  | volition
  /-- Sentience or perception. -/
  | sentience
  /-- Causes an event or change of state in another participant. -/
  | causation
  /-- Movement relative to another participant. -/
  | movement
  /-- Exists independently of the event named by the verb. -/
  | independentExistence
  /-- Undergoes a change of state. -/
  | changeOfState
  /-- The argument is an incremental theme, measuring out the event. -/
  | incrementalTheme
  /-- Causally affected by another participant. -/
  | causallyAffected
  /-- Stationary relative to another participant. -/
  | stationary
  /-- Does not exist independently of the event. -/
  | dependentExistence
  deriving DecidableEq, Repr, Fintype

namespace ProtoRoleFeature

/-- Dowty's five Proto-Agent entailments. -/
def agentCluster : Finset ProtoRoleFeature :=
  {.volition, .sentience, .causation, .movement, .independentExistence}

/-- Dowty's five Proto-Patient entailments. -/
def patientCluster : Finset ProtoRoleFeature :=
  {.changeOfState, .incrementalTheme, .causallyAffected, .stationary, .dependentExistence}

theorem disjoint_agentCluster_patientCluster : Disjoint agentCluster patientCluster := by
  decide

theorem agentCluster_union_patientCluster : agentCluster ∪ patientCluster = Finset.univ := by
  decide

end ProtoRoleFeature

open ProtoRoleFeature

/-- The proto-role entailments a verb imposes on one of its arguments. -/
abbrev EntailmentProfile := Finset ProtoRoleFeature

/-- A profile is printed as the list of its entailments in Dowty's order. -/
instance : Repr EntailmentProfile where
  reprPrec p _ := repr ([ProtoRoleFeature.volition, .sentience, .causation, .movement,
    .independentExistence, .changeOfState, .incrementalTheme, .causallyAffected, .stationary,
    .dependentExistence].filter (· ∈ p))

namespace EntailmentProfile

variable {p q : EntailmentProfile}

/-- The Proto-Agent entailments of a profile. -/
def protoAgent (p : EntailmentProfile) : Finset ProtoRoleFeature := p ∩ agentCluster

/-- The Proto-Patient entailments of a profile. -/
def protoPatient (p : EntailmentProfile) : Finset ProtoRoleFeature := p ∩ patientCluster

theorem protoAgent_mono : Monotone protoAgent := fun _ _ h ↦ Finset.inter_subset_inter_right h

theorem protoPatient_mono : Monotone protoPatient := fun _ _ h ↦ Finset.inter_subset_inter_right h

/-- The profile imposes entailments from both proto-role clusters, [reinhart-siloni-2005]'s
complex role. -/
def IsComplexRole (p : EntailmentProfile) : Prop := p.protoAgent.Nonempty ∧ p.protoPatient.Nonempty

instance : DecidablePred IsComplexRole := fun p ↦
  inferInstanceAs (Decidable (p.protoAgent.Nonempty ∧ p.protoPatient.Nonempty))

/-- Bundling an agentive profile with an affected one yields a complex role. -/
theorem isComplexRole_union (ha : p.protoAgent.Nonempty) (hp : q.protoPatient.Nonempty) :
    IsComplexRole (p ∪ q) :=
  ⟨ha.mono (protoAgent_mono Finset.subset_union_left),
    hp.mono (protoPatient_mono Finset.subset_union_right)⟩

end EntailmentProfile

open EntailmentProfile

variable (p subj obj : EntailmentProfile)

/-! ### Argument selection -/

/-- The Argument Selection Principle by inclusion ([grimm-2011], [davis-koenig-2000]): `subj`
outranks `obj` for subjecthood when its Proto-Agent entailments strictly include `obj`'s, or
when neither Proto-Agent part strictly includes the other and `obj`'s Proto-Patient entailments
strictly include `subj`'s. Causation priority is structural: `{causation, independentExistence}`
strictly includes `{independentExistence}` yet is incomparable with
`{sentience, independentExistence}`. -/
def OutranksForSubject : Prop :=
  obj.protoAgent ⊂ subj.protoAgent ∨
    (¬ subj.protoAgent ⊂ obj.protoAgent ∧ subj.protoPatient ⊂ obj.protoPatient)

instance : Decidable (OutranksForSubject subj obj) := by
  unfold OutranksForSubject; infer_instance

/-! ### Split intransitivity -/

/-- The sole argument lacks the priority Proto-Agent entailments, volition and causation
([davis-koenig-2000]), and bears at least one Proto-Patient entailment ([dowty-1991] Table 1).
Unlike flat counting, this classifies *arrive* as unaccusative. -/
def PredictsUnaccusative : Prop :=
  .volition ∉ p ∧ .causation ∉ p ∧ p.protoPatient.Nonempty

instance : DecidablePred PredictsUnaccusative := fun p ↦ by
  unfold PredictsUnaccusative; infer_instance

/-! ### Well-formedness -/

/-- Volition presupposes sentience: only sentient entities can act volitionally ([dowty-1991]
p.607, [levin-2019] §2.1). -/
def WellFormedInternal : Prop := .volition ∈ p → .sentience ∈ p

instance : DecidablePred WellFormedInternal := fun _ ↦
  inferInstanceAs (Decidable (_ → _))

/-! ### Template-level proto-role defaults

Per-template subject and object defaults, [rappaport-hovav-levin-1998]'s templates with
[dowty-1991]'s entailments, consumed by Fragment-level verb entries. Per-verb entailments live in
the Levin-class map (`LevinClass.subjectProfile`), and Dowty's own per-verb attributions are the
rows of `Data/ProtoRoles/Dowty1991.json` consumed by `Studies/Dowty1991.lean`. -/

/-- The activity template's subject, with volition, sentience, movement and independent existence.
Transitive activities like *hit* add causation at the class level via root-contributed objects. -/
def activitySubjectProfile : EntailmentProfile :=
  {.volition, .sentience, .movement, .independentExistence}

/-- The achievement template's subject, which moves, exists independently and undergoes a change of
state. The movement entailment fits directed-motion achievements (*arrive*) but overgeneralizes to
non-motion achievements (*recognize*, *notice*), whose subjects are sentient rather than moving;
those pattern with the psych-state templates in `LevinClass.subjectProfile`. -/
def achievementSubjectProfile : EntailmentProfile :=
  {.movement, .independentExistence, .changeOfState}

/-- The accomplishment template's subject, a full proto-agent with volition, sentience, causation,
movement and independent existence. Dowty confirms it at the class level: the primary transitive
verbs of [dowty-1991] (35) (*build*, *write*, *murder*, *eat*, *wash*) have subjects with "volition,
sentience, causation, and movement" and no Proto-Patient entailments (p. 577); independent existence
is the parenthesized (27e). -/
def accomplishmentSubjectProfile : EntailmentProfile :=
  {.volition, .sentience, .causation, .movement, .independentExistence}

/-- The accomplishment template's object, a result patient that changes state and is causally
affected. Dowty confirms it at the class level: the (35) objects have "change, causally affected"
(p. 577); the remaining Proto-Patient entailments are hedged there as "(mostly) incremental theme,
stationary, dependent existence", so incremental themes (*eat*, *build*) add IT per class or per
verb — not all accomplishment objects measure the event. -/
def accomplishmentObjectProfile : EntailmentProfile :=
  {.changeOfState, .causallyAffected}

end ArgumentStructure
