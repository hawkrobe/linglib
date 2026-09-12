import Linglib.Pragmatics.GriceanMaxims
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Fragments.Romance.French.Predicates

/-!
# Martin, Schäfer and Kastner (2025): The Lexical Pragmatics of Reflexive Marking

This file formalizes the pragmatic account of French anticausative marking of
[martin-schaefer-kastner-2025]. Anticausatives marked with *se* and unmarked ones do not
differ in meaning; the *se* form is ambiguous between anticausative and reflexive voice while
the bare form is not (`Form.voiceOptions`, `se_ambiguous`), and cooperative speakers manage
that ambiguity under the Manner supermaxim. With a human argument the reflexive parse is
salient, by the bias to read humans as agents; for a limited-control verb, *rougir* 'blush',
the parse misleads, so the unmarked form is preferred, the unmarked limited-control
preference (4), and for an in-control verb, *(se) plier* 'bend', the bare form's inference
that no agentive construal was intended misleads instead, so the marked form is preferred,
the marked in-control preference (5). With a nonhuman argument no parse is salient and no
preference arises, unless the speaker means to present the nonhuman as responsible, when
the marked form is preferred since the reflexive parse is the only way to assign it agency,
the marked responsibility preference (`preference`, `generalizations`). The control level is
not read off the entailment profile, limited-control and in-control property-change verbs
sharing one (`control_level_not_from_entailments`), and the opposite preferences of the two
classes falsify any uniform semantic difference between the two forms
(`opposite_preferences_falsify_uniform_semantics`). Preferences arise only for verbs with
both forms (`SeMarking.HasChoice`).

## Implementation notes

The voice flavours are the substrate's non-thematic and reflexive flavours after
[schaefer-2008], and the entailment profiles of anticausative subjects the substrate's; the
account presupposes the reflexive–anticausative syncretism of [koontz-garboden-2009]. The
experiments' rating means are described in the paper and not represented.

## References

* [martin-schaefer-kastner-2025]
* [schaefer-2008]
* [koontz-garboden-2009]
-/

namespace MartinSchaeferKastner2025

open Minimalist.Voice ArgumentStructure French.Predicates

/-! ### The classes -/

/-- The morphological class of an anticausative: the bare form only, *changer de position*;
the *se* form only, *s'affaiblir*; or both, *casser*, *plier*, *rougir*. -/
inductive SeMarking where
  | minusSe
  | plusSe
  | plusMinusSe
  deriving DecidableEq

/-- Whether the speaker has a choice of form: only the verbs with both forms. -/
def SeMarking.HasChoice : SeMarking → Prop
  | .plusMinusSe => True
  | _ => False

instance : DecidablePred SeMarking.HasChoice := λ m => by
  cases m <;> unfold SeMarking.HasChoice <;> infer_instance

/-- Whether the change a verb names is typically under its human undergoer's control (§1.1):
*rougir* 'blush' and *pâlir* 'get pale' are limited-control, *plier* 'bend' and
*s'approcher* 'get close' in-control. The distinction is world knowledge, not entailment. -/
inductive ControlLevel where
  | limitedControl
  | inControl
  deriving DecidableEq

/-- The animacy of the sole argument. -/
inductive Animacy where
  | human
  | nonhuman
  deriving DecidableEq

/-- Whether the speaker means to present the entity as responsible for the change. -/
inductive ResponsibilityGoal where
  | neutral
  | conveyResponsibility
  deriving DecidableEq

/-- The control level is not derivable from the entailment profile: the limited-control
*rougir* and the in-control *refroidir* share one. -/
theorem control_level_not_from_entailments :
    rougir.subjectEntailments = refroidir.subjectEntailments := by decide

/-- Movement entailments suffice for in-control status, *approcher*, but are not necessary,
*refroidir* being in-control without them. -/
theorem movement_sufficient_not_necessary :
    approcher.subjectEntailments = some motionCosSubjectProfile ∧
      refroidir.subjectEntailments = some cosSubjectProfile ∧
      motionCosSubjectProfile.movement = true ∧ cosSubjectProfile.movement = false := by
  decide

/-! ### The voice ambiguity of *se* -/

/-- The two forms of a verb with a choice. -/
inductive Form where
  | bare
  | se
  deriving DecidableEq

/-- The voice flavours a form admits: the bare form only the non-thematic anticausative, the
*se* form the reflexive as well, the syncretism of [schaefer-2008] and
[koontz-garboden-2009]. -/
def Form.voiceOptions : Form → List Flavor
  | .bare => [.nonThematic]
  | .se => [.nonThematic, .reflexive]

/-- Both forms share the anticausative parse, and only the *se* form has the reflexive one. -/
theorem se_ambiguous :
    (∀ f : Form, Flavor.nonThematic ∈ f.voiceOptions) ∧
      Flavor.reflexive ∈ Form.se.voiceOptions ∧ Flavor.reflexive ∉ Form.bare.voiceOptions := by
  refine ⟨λ f => ?_, by decide, by decide⟩
  cases f <;> decide

/-! ### Managing the ambiguity (§2) -/

/-- The agent bias: the reflexive parse of the *se* form is salient for a human argument. -/
def ReflexiveSalient : Animacy → Prop
  | .human => True
  | .nonhuman => False

/-- The reflexive parse clashes with shared assumptions for a limited-control verb, whose
change is not under the undergoer's control, and aligns with them for an in-control verb. -/
def ReflexiveClashes : ControlLevel → Prop
  | .limitedControl => True
  | .inControl => False

instance : DecidablePred ReflexiveSalient := λ a => by
  cases a <;> unfold ReflexiveSalient <;> infer_instance

instance : DecidablePred ReflexiveClashes := λ c => by
  cases c <;> unfold ReflexiveClashes <;> infer_instance

/-- The preferred form of a verb with a choice. -/
inductive Preference where
  | unmarked
  | marked
  deriving DecidableEq

/-- The predicted preference, from the Manner supermaxim: where the reflexive parse is salient,
avoid the ambiguous form when that parse misleads and keep it when the bare form's inference
that no agent was intended misleads instead; where no parse is salient, the marked form only
when the speaker means to convey responsibility, the reflexive parse being the only way to
assign a nonhuman agency. -/
def preference (ctrl : ControlLevel) (anim : Animacy) (goal : ResponsibilityGoal) :
    Option Preference :=
  if ReflexiveSalient anim then some (if ReflexiveClashes ctrl then .unmarked else .marked)
  else match goal with
    | .neutral => none
    | .conveyResponsibility => some .marked

/-- The three generalizations: the unmarked limited-control preference and the marked
in-control preference with a human argument, the marked responsibility preference with a
nonhuman one, and no preference for a nonhuman argument otherwise. -/
theorem generalizations (g : ResponsibilityGoal) (c : ControlLevel) :
    preference .limitedControl .human g = some .unmarked ∧
      preference .inControl .human g = some .marked ∧
      preference c .nonhuman .conveyResponsibility = some .marked ∧
      preference c .nonhuman .neutral = none := by
  cases g <;> cases c <;> decide

/-- Against the causation claim of [labelle-1992] and [labelle-doron-2010]: the same class of
verbs with a choice shows opposite preferences by control level, which no uniform semantic
difference between the two forms could produce. -/
theorem opposite_preferences_falsify_uniform_semantics (g : ResponsibilityGoal) :
    preference .limitedControl .human g ≠ preference .inControl .human g := by
  cases g <;> decide

/-! ### Unaccusativity -/

/-- The anticausative subject profiles predict unaccusativity: no volition, no causation, a
patient. -/
theorem cos_profiles_unaccusative :
    PredictsUnaccusative cosSubjectProfile ∧ PredictsUnaccusative motionCosSubjectProfile := by
  decide

end MartinSchaeferKastner2025
