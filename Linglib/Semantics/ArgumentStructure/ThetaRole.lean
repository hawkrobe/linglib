import Linglib.Semantics.ArgumentStructure.EntailmentProfile

/-!
# Theta roles as proto-role clusters

Dowty replaces the traditional list of thematic roles by two cluster concepts, the Proto-Agent
and Proto-Patient entailments, and reads the familiar role types off combinations of them: an
agent is volitional, sentient, causing, and moving; an experiencer is sentient without volition
or causation; an instrument causes and moves without volition or sentience; a theme changes,
measures out the event, and depends on it, and a patient is the causally affected theme; a
source or goal has no defining entailment at all. This file carries those labels, the profile
each names, and the classifier that reads a label off a profile, so that a label is a derived
classification of an argument's entailment profile and never a stored primitive.

## Main declarations

* `ArgumentStructure.ThetaRole`: the eight traditional labels.
* `ThetaRole.canonicalProfile`: the entailments a label combines, `⊥` for source and goal;
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
-/

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
  deriving DecidableEq, Repr, Fintype

namespace ThetaRole

/-- The entailments a label combines, in Dowty's reading of the traditional roles: the agent
all four core Proto-Agent entailments, the experiencer sentience, the stimulus causation, the
instrument causation and movement, the theme change with incremental theme and dependent
existence, the patient the causally affected theme, and the source and goal nothing. -/
def canonicalProfile : ThetaRole → EntailmentProfile
  | .agent => { volition := true, sentience := true, causation := true, movement := true }
  | .experiencer => { sentience := true }
  | .stimulus => { causation := true }
  | .instrument => { causation := true, movement := true }
  | .theme => { changeOfState := true, incrementalTheme := true, dependentExistence := true }
  | .patient =>
    { changeOfState := true, incrementalTheme := true, causallyAffected := true,
      dependentExistence := true }
  | .goal | .source => ⊥

/-- A label is defined by proto-role entailments; source and goal are not. -/
def IsDefined (r : ThetaRole) : Prop := r ≠ .source ∧ r ≠ .goal

instance : DecidablePred IsDefined := fun r ↦ inferInstanceAs (Decidable (r ≠ .source ∧ r ≠ .goal))

@[simp] theorem canonicalProfile_source : canonicalProfile .source = ⊥ := rfl

@[simp] theorem canonicalProfile_goal : canonicalProfile .goal = ⊥ := rfl

/-- A label has defining entailments iff its profile is not empty. -/
theorem isDefined_iff_canonicalProfile_ne_bot (r : ThetaRole) :
    r.IsDefined ↔ r.canonicalProfile ≠ ⊥ := by
  cases r <;> decide

/-- A patient is a theme that is causally affected. -/
theorem canonicalProfile_theme_le_patient :
    canonicalProfile .theme ≤ canonicalProfile .patient := by
  decide

/-- Every canonical profile satisfies Dowty's internal constraint that volition entails
sentience. -/
theorem wellFormedInternal_canonicalProfile (r : ThetaRole) :
    WellFormedInternal r.canonicalProfile := by
  cases r <;> decide

end ThetaRole

namespace EntailmentProfile

/-- The label of a profile: agent if volitional, else experiencer if sentient and not causing,
else instrument or stimulus if causing according to movement, else patient if causally
affected, else theme if changing, measuring out the event, depending on it, or moving, and
otherwise none. -/
def toRole (p : EntailmentProfile) : Option ThetaRole :=
  if p.volition then some .agent
  else if p.sentience then if p.causation then none else some .experiencer
  else if p.causation then some (if p.movement then .instrument else .stimulus)
  else if p.causallyAffected then some .patient
  else if p.changeOfState || p.incrementalTheme || p.dependentExistence || p.movement then
    some .theme
  else none

variable {p : EntailmentProfile}

theorem toRole_eq_some_agent_iff : p.toRole = some .agent ↔ p.volition = true := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_experiencer_iff : p.toRole = some .experiencer ↔
    p.volition = false ∧ p.sentience = true ∧ p.causation = false := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_instrument_iff : p.toRole = some .instrument ↔
    p.volition = false ∧ p.sentience = false ∧ p.causation = true ∧ p.movement = true := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_stimulus_iff : p.toRole = some .stimulus ↔
    p.volition = false ∧ p.sentience = false ∧ p.causation = true ∧ p.movement = false := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_patient_iff : p.toRole = some .patient ↔
    p.volition = false ∧ p.sentience = false ∧ p.causation = false ∧
      p.causallyAffected = true := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_theme_iff : p.toRole = some .theme ↔
    p.volition = false ∧ p.sentience = false ∧ p.causation = false ∧
      p.causallyAffected = false ∧
        (p.changeOfState || p.incrementalTheme || p.dependentExistence || p.movement) = true := by
  unfold toRole; split_ifs <;> simp_all

/-- Source and goal are never read off a profile: they are not defined by entailments. -/
theorem toRole_ne_some_source : p.toRole ≠ some .source := by
  unfold toRole; split_ifs <;> simp

theorem toRole_ne_some_goal : p.toRole ≠ some .goal := by
  unfold toRole; split_ifs <;> simp

/-- A label read off a profile is a defined one. -/
theorem isDefined_of_toRole_eq_some {r : ThetaRole} (h : p.toRole = some r) : r.IsDefined :=
  ⟨fun hr ↦ toRole_ne_some_source (hr ▸ h), fun hr ↦ toRole_ne_some_goal (hr ▸ h)⟩

theorem causation_of_toRole_eq_some_stimulus (h : p.toRole = some .stimulus) :
    p.causation = true :=
  (toRole_eq_some_stimulus_iff.mp h).2.2.1

end EntailmentProfile

namespace ThetaRole

/-- The classifier recovers every defined label from its canonical profile. -/
theorem toRole_canonicalProfile {r : ThetaRole} (h : r.IsDefined) :
    r.canonicalProfile.toRole = some r := by
  cases r <;> first | rfl | exact absurd rfl h.1 | exact absurd rfl h.2

/-- Distinct defined labels have distinct canonical profiles. -/
theorem canonicalProfile_injOn : Set.InjOn canonicalProfile {r | r.IsDefined} := by
  intro r hr s hs h
  have hr' := toRole_canonicalProfile hr
  rw [h, toRole_canonicalProfile hs] at hr'
  exact (Option.some.inj hr').symm

end ThetaRole

end ArgumentStructure
