import Linglib.Theories.Semantics.Events.ProtoRoles
import Linglib.Core.Discourse.CoherenceRelation
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Solstad & Bott (2024) — Proto-Role Bridge

@cite{solstad-bott-2024}

Connects IC bias predictions to proto-role infrastructure and coherence
relations.

## Core argument

Solstad & Bott (2024) argue that IC bias arises from the interaction of:
1. **Verb semantics** — specifically, the entailment profile of the subject
2. **Discourse coherence** — specifically, the Explanation relation (triggered
   by "because")

The key insight is that occasion verb subjects are **agent-evocators**: they
pass the do-test pragmatically (and thus evoke agency) but do NOT entail
volition or causation. Their entailment profile is like experiencers
(sentience + independent existence), not like agents.

This explains why OccV patterns with AgExp for IC bias: both have subjects
whose entailment profiles lack causation, making the subject's internal state
(rather than external action) the natural locus of causal explanation.

## Entailment profiles by verb class

| Class   | Subject profile          | P-Agent entailments      |
|---------|--------------------------|--------------------------|
| OccV    | S + IE                   | sentience, indep.exist.  |
| AgExp   | S + IE                   | sentience, indep.exist.  |
| StimExp | C + IE (stimulus/causer) | causation, indep.exist.  |
| AgPat   | V + S + C + M + IE       | all five                 |
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge

open Semantics.Events.ProtoRoles
open Core.Discourse.CoherenceRelation
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Entailment Profiles for Verb Classes
-- ════════════════════════════════════════════════════

/-- Occasion verb subject profile: sentience + independent existence.

    Occasion verb subjects are "agent-evocators" (Solstad & Bott 2024, §2.2):
    they pragmatically pass the do-test but do NOT entail volition or causation.
    Their entailment profile matches experiencers, not agents. -/
def occasionVerbSubjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- Agent-experiencer verb subject profile: sentience + independent existence.
    Same as occasion verbs — the subject is an experiencer. -/
def agExpSubjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- Agent-experiencer verb object profile: causation + independent existence.
    The object is a stimulus (cause of the experience). -/
def agExpObjectProfile : EntailmentProfile :=
  ⟨false, false, true, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer verb subject profile: causation + independent existence.
    The subject is a stimulus/cause (Levin 31.1 amuse class). -/
def stimExpSubjectProfile : EntailmentProfile :=
  ⟨false, false, true, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer verb object profile: sentience + independent existence.
    The object is an experiencer. -/
def stimExpObjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- Agent-patient verb subject profile: full agent (all 5 P-Agent).
    Identical to existing kickSubjectProfile. -/
def agPatSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

-- ════════════════════════════════════════════════════
-- § 2. OccV ≈ AgExp (same entailment profile)
-- ════════════════════════════════════════════════════

/-- Occasion verb subjects have the SAME entailment profile as AgExp subjects. -/
theorem occV_matches_agExp_profile :
    occasionVerbSubjectProfile = agExpSubjectProfile := rfl

/-- Both OccV and AgExp subjects have P-Agent score = 2. -/
theorem occV_agExp_same_pAgent :
    occasionVerbSubjectProfile.pAgentScore =
    agExpSubjectProfile.pAgentScore := rfl

/-- OccV subjects have strictly fewer P-Agent entailments than AgPat subjects. -/
theorem occV_fewer_pAgent_than_agPat :
    occasionVerbSubjectProfile.pAgentScore <
    agPatSubjectProfile.pAgentScore := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Do-Test Behavior
-- ════════════════════════════════════════════════════

/-- OccV subjects do NOT pass the do-test from their entailment profile.

    This captures Solstad & Bott's "agent-evocator" concept: the do-test
    passes pragmatically (because the complement denotes a volitional action)
    but the verb itself does NOT entail volition, causation, or movement. -/
theorem occV_subject_fails_doTest :
    passesDoTestFromProfile occasionVerbSubjectProfile = false := by native_decide

/-- AgExp subjects also fail the do-test (experiencers don't "do" anything). -/
theorem agExp_subject_fails_doTest :
    passesDoTestFromProfile agExpSubjectProfile = false := by native_decide

/-- AgPat subjects pass the do-test (full agents). -/
theorem agPat_subject_passes_doTest :
    passesDoTestFromProfile agPatSubjectProfile = true := by native_decide

/-- StimExp subjects pass the do-test (they have causation). -/
theorem stimExp_subject_passes_doTest :
    passesDoTestFromProfile stimExpSubjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Bridge to ThetaRole
-- ════════════════════════════════════════════════════

/-- OccV subject profile matches ThetaRole.experiencer's canonical profile. -/
theorem occV_profile_matches_experiencer :
    occasionVerbSubjectProfile = ThetaRole.canonicalProfile .experiencer := rfl

/-- AgPat subject profile matches ThetaRole.agent's canonical profile. -/
theorem agPat_profile_matches_agent :
    agPatSubjectProfile = ThetaRole.canonicalProfile .agent := rfl

/-- StimExp subject profile matches ThetaRole.stimulus's canonical profile. -/
theorem stimExp_profile_matches_stimulus :
    stimExpSubjectProfile = ThetaRole.canonicalProfile .stimulus := rfl

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Fragment: Theta Role Annotations
-- ════════════════════════════════════════════════════

/-- Occasion verbs assign experiencer to subject in the occasion sense.

    `manage` has two entries: `manage` (`.agent`, traditional) and
    `manage_occasion` (`.experiencer`, Solstad & Bott 2024). The other
    occasion verbs (dare, bother, hesitate) have only the experiencer entry,
    since they lack an independent implicative tradition. -/
theorem occasion_verbs_experiencer_subject :
    manage_occasion.subjectTheta = some .experiencer ∧
    dare.subjectTheta = some .experiencer ∧
    bother.subjectTheta = some .experiencer ∧
    hesitate.subjectTheta = some .experiencer :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The two senses of "manage" diverge on subject theta role:
    traditional says agent, Solstad & Bott say experiencer.
    This is the core of the "agent-evocator" tension. -/
theorem manage_senses_diverge_on_theta :
    manage.subjectTheta = some .agent ∧
    manage_occasion.subjectTheta = some .experiencer :=
  ⟨rfl, rfl⟩

/-- Despite different theta labels, both senses share implicative semantics. -/
theorem manage_senses_share_semantics :
    manage.implicativeBuilder = manage_occasion.implicativeBuilder := rfl

/-- AgExp verbs assign experiencer to subject. -/
theorem agExp_verbs_experiencer_subject :
    enjoy.subjectTheta = some .experiencer ∧
    like.subjectTheta = some .experiencer ∧
    love.subjectTheta = some .experiencer ∧
    hate.subjectTheta = some .experiencer :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- StimExp verbs assign stimulus to subject. -/
theorem stimExp_verbs_stimulus_subject :
    frighten.subjectTheta = some .stimulus ∧
    amuse.subjectTheta = some .stimulus ∧
    fascinate.subjectTheta = some .stimulus ∧
    irritate.subjectTheta = some .stimulus :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. IC Bias Prediction via Coherence Relations
-- ════════════════════════════════════════════════════

/-- The Explanation relation (triggered by "because") selects for causes. -/
theorem because_triggers_causal_search :
    CoherenceRelation.explanation.selectsCause = true := rfl

/-- The Occasion relation (triggered by "and then") does NOT select for causes. -/
theorem andThen_no_causal_search :
    CoherenceRelation.occasion.selectsCause = false := rfl

/-- IC bias prediction: under Explanation, the participant whose entailment
    profile includes sentience (without causation) is the locus of
    causal explanation → NP1 bias for experiencer-subject verbs.

    For OccV and AgExp: subject has sentience but not causation →
    the subject's internal state is the natural cause → NP1 bias.

    For StimExp: subject has causation but not sentience →
    the subject is the cause, object is the experiencer →
    the *object*'s internal state is the natural cause → NP2 bias. -/
def predictICBias (subjProfile : EntailmentProfile) : ICBias :=
  if subjProfile.sentience && !subjProfile.causation then .np1
  else if subjProfile.causation && !subjProfile.sentience then .np2
  else .np1  -- Default: agents default to NP1

/-- OccV predicted as NP1 (experiencer subject). -/
theorem occV_predicted_np1 :
    predictICBias occasionVerbSubjectProfile = .np1 := by native_decide

/-- AgExp predicted as NP1 (experiencer subject). -/
theorem agExp_predicted_np1 :
    predictICBias agExpSubjectProfile = .np1 := by native_decide

/-- StimExp predicted as NP2 (stimulus subject). -/
theorem stimExp_predicted_np2 :
    predictICBias stimExpSubjectProfile = .np2 := by native_decide

/-- AgPat predicted as NP1 (agent subject — default). -/
theorem agPat_predicted_np1 :
    predictICBias agPatSubjectProfile = .np1 := by native_decide

/-- The prediction matches the empirical data for all four classes. -/
theorem predictions_match_data :
    predictICBias occasionVerbSubjectProfile = VerbClass.predictedBias .occasionVerb ∧
    predictICBias agExpSubjectProfile = VerbClass.predictedBias .agentExp ∧
    predictICBias stimExpSubjectProfile = VerbClass.predictedBias .stimExp ∧
    predictICBias agPatSubjectProfile = VerbClass.predictedBias .agentPat := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge
