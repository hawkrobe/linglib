module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic

/-!
# Theta roles as proto-role clusters

Dowty replaces the traditional list of thematic roles by two cluster concepts, the Proto-Agent and
Proto-Patient entailments, and reads the familiar role types off combinations of them: an agent is
volitional, sentient, causing, and moving; an experiencer is sentient without volition or causation;
an instrument causes and moves without volition or sentience; a theme changes, measures out the
event, and depends on it, and a patient is the causally affected theme; a source or goal has no
defining entailment at all. The recipient of a transfer, for which Primus proposes a Recipient
Proto-role of its own, has none here either. This file carries those labels, the profile each names,
and the classifier that reads a label off a profile, so that a label is a derived classification of
an argument's entailment profile and never a stored primitive.

## Main declarations

* `ArgumentStructure.ThetaRole`: the nine traditional labels.
* `ThetaRole.canonicalProfile`: the entailments a label combines, none for source, goal and
  recipient;
  `ThetaRole.IsDefined` says a label has defining entailments.
* `EntailmentProfile.toRole`: the label of a profile, with `toRole_eq_some_agent_iff` and its
  siblings characterizing each label and `toRole_canonicalProfile` recovering a defined label
  from its profile.

## Implementation notes

The classifier tests the Proto-Agent entailments first, volition before sentience before
causation, and among the Proto-Patient entailments causal affectedness before the rest, so a
profile with both sentience and causation but no volition, which Dowty's definitions do not
name, has no label. Independent existence, which Dowty parenthesizes, never decides a label.
Dowty's role hierarchies follow from the selection principle over these profiles in
`Studies/Dowty1991.lean`.

## References

* [dowty-1991]
* [levin-rappaport-hovav-2005]
* [primus-1999]
-/

@[expose] public section

namespace ArgumentStructure

/-- The traditional thematic-role labels, read as clusters of proto-role entailments. -/
inductive ThetaRole where
  | agent
  | patient
  | theme
  | experiencer
  | goal
  | source
  | instrument
  | stimulus
  /-- The recipient of a transfer, for which [primus-1999] introduces a Recipient Proto-role
  ([levin-rappaport-hovav-2005], p. 60). -/
  | recipient
  deriving DecidableEq, Repr, Fintype

namespace ThetaRole

/-- `canonicalProfile r` is the set of entailments the label `r` combines in Dowty's reading of the
traditional roles, the agent all four core Proto-Agent entailments, the experiencer sentience, the
stimulus causation, the instrument causation and movement, the theme change with incremental theme
and dependent existence, the patient the causally affected theme, and the source, goal and recipient
nothing. -/
def canonicalProfile : ThetaRole → EntailmentProfile
  | .agent => {.volition, .sentience, .causation, .movement}
  | .experiencer => {.sentience}
  | .stimulus => {.causation}
  | .instrument => {.causation, .movement}
  | .theme => {.changeOfState, .incrementalTheme, .dependentExistence}
  | .patient => {.changeOfState, .incrementalTheme, .causallyAffected, .dependentExistence}
  | .goal | .source | .recipient => ∅

/-- A label is defined by proto-role entailments; source, goal and recipient are not. -/
def IsDefined (r : ThetaRole) : Prop := r ≠ .source ∧ r ≠ .goal ∧ r ≠ .recipient

instance : DecidablePred IsDefined := fun r ↦
  inferInstanceAs (Decidable (r ≠ .source ∧ r ≠ .goal ∧ r ≠ .recipient))

@[simp] theorem canonicalProfile_source : canonicalProfile .source = ∅ := rfl

@[simp] theorem canonicalProfile_goal : canonicalProfile .goal = ∅ := rfl

@[simp] theorem canonicalProfile_recipient : canonicalProfile .recipient = ∅ := rfl

/-- A label has defining entailments iff its profile is not empty. -/
theorem isDefined_iff_canonicalProfile_nonempty (r : ThetaRole) :
    r.IsDefined ↔ r.canonicalProfile.Nonempty := by
  cases r <;> decide

/-- A patient is a theme that is causally affected. -/
theorem canonicalProfile_theme_le_patient :
    canonicalProfile .theme ⊆ canonicalProfile .patient := by
  decide

/-- Every canonical profile satisfies Dowty's internal constraint that volition entails
sentience. -/
theorem wellFormedInternal_canonicalProfile (r : ThetaRole) :
    WellFormedInternal r.canonicalProfile := by
  cases r <;> decide

end ThetaRole

namespace EntailmentProfile

/-- `p.toRole` is the label of the profile `p`, agent if volitional, else experiencer if sentient
and not causing, else instrument or stimulus if causing according to movement, else patient if
causally affected, else theme if changing, measuring out the event, depending on it, or moving, and
otherwise none. -/
def toRole (p : EntailmentProfile) : Option ThetaRole :=
  if .volition ∈ p then some .agent
  else if .sentience ∈ p then if .causation ∈ p then none else some .experiencer
  else if .causation ∈ p then some (if .movement ∈ p then .instrument else .stimulus)
  else if .causallyAffected ∈ p then some .patient
  else if .changeOfState ∈ p ∨ .incrementalTheme ∈ p ∨ .dependentExistence ∈ p ∨ .movement ∈ p
  then some .theme
  else none

variable {p : EntailmentProfile}

theorem toRole_eq_some_agent_iff : p.toRole = some .agent ↔ .volition ∈ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_experiencer_iff : p.toRole = some .experiencer ↔
    .volition ∉ p ∧ .sentience ∈ p ∧ .causation ∉ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_instrument_iff : p.toRole = some .instrument ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∈ p ∧ .movement ∈ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_stimulus_iff : p.toRole = some .stimulus ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∈ p ∧ .movement ∉ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_patient_iff : p.toRole = some .patient ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∉ p ∧ .causallyAffected ∈ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_theme_iff : p.toRole = some .theme ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∉ p ∧ .causallyAffected ∉ p ∧
      (.changeOfState ∈ p ∨ .incrementalTheme ∈ p ∨ .dependentExistence ∈ p ∨ .movement ∈ p) := by
  unfold toRole; split_ifs <;> simp_all

/-- Source, goal and recipient are never read off a profile: they are not defined by
entailments. -/
theorem toRole_ne_some_source : p.toRole ≠ some .source := by
  unfold toRole; split_ifs <;> simp

theorem toRole_ne_some_goal : p.toRole ≠ some .goal := by
  unfold toRole; split_ifs <;> simp

theorem toRole_ne_some_recipient : p.toRole ≠ some .recipient := by
  unfold toRole; split_ifs <;> simp

/-- A label read off a profile is a defined one. -/
theorem isDefined_of_toRole_eq_some {r : ThetaRole} (h : p.toRole = some r) : r.IsDefined :=
  ⟨fun hr ↦ toRole_ne_some_source (hr ▸ h), fun hr ↦ toRole_ne_some_goal (hr ▸ h),
    fun hr ↦ toRole_ne_some_recipient (hr ▸ h)⟩

theorem causation_mem_of_toRole_eq_some_stimulus (h : p.toRole = some .stimulus) :
    .causation ∈ p :=
  (toRole_eq_some_stimulus_iff.mp h).2.2.1

end EntailmentProfile

namespace ThetaRole

/-- The classifier recovers every defined label from its canonical profile. -/
theorem toRole_canonicalProfile {r : ThetaRole} (h : r.IsDefined) :
    r.canonicalProfile.toRole = some r := by
  cases r <;> first | rfl | exact absurd rfl h.1 | exact absurd rfl h.2.1 | exact absurd rfl h.2.2

/-- Distinct defined labels have distinct canonical profiles. -/
theorem canonicalProfile_injOn : Set.InjOn canonicalProfile {r | r.IsDefined} := by
  intro r hr s hs h
  have hr' := toRole_canonicalProfile hr
  rw [h, toRole_canonicalProfile hs] at hr'
  exact (Option.some.inj hr').symm

end ThetaRole

end ArgumentStructure
