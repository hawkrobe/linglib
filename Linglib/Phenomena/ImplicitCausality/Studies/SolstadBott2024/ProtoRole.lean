import Linglib.Theories.Semantics.Events.ProtoRoles
import Linglib.Core.Discourse.CoherenceRelation
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.Reference.Studies.RosaArnold2017

/-!
# Psych Verb IC Bias — Proto-Role Bridge

@cite{solstad-bott-2022} @cite{solstad-bott-2024} @cite{dowty-1991} @cite{kehler-2002}

Connects IC bias predictions to @cite{dowty-1991} proto-role infrastructure and
coherence relations.

## Core argument

IC bias tracks the **stimulus** argument:
explanations in *because*-continuations target the participant whose entailment
profile includes causation (the stimulus/cause), regardless of whether that
participant is the subject or the object.

- **StimExp** (B&R Class II): stimulus = subject → NP1 bias (87.4%, Table 1)
- **ExpStim** (B&R Class I): stimulus = object → NP2 bias (96.0%, Table 1)

## Entailment profiles by verb class

| Class    | Subject profile          | P-Agent entailments      |
|----------|--------------------------|--------------------------|
| StimExp  | C + IE (stimulus/causer) | causation, indep.exist.  |
| ExpStim  | S + IE (experiencer)     | sentience, indep.exist.  |
| AgPat    | V + S + C + M + IE       | all five                 |
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024.ProtoRole

open Semantics.Events.ProtoRoles
open Core.Discourse.CoherenceRelation
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Entailment Profiles for Verb Classes
-- ════════════════════════════════════════════════════

/-- Stimulus-experiencer verb subject profile: causation + independent existence.
    The subject is a stimulus/cause (B&R Class II, Levin 31.1 amuse class).
    @cite{solstad-bott-2022}: STIM-EXP verbs show NP1 I-Caus bias. -/
def stimExpSubjectProfile : EntailmentProfile :=
  ⟨false, false, true, false, true, false, false, false, false, false⟩

/-- Stimulus-experiencer verb object profile: sentience + independent existence.
    The object is an experiencer. -/
def stimExpObjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- Experiencer-stimulus verb subject profile: sentience + independent existence.
    The subject is an experiencer (B&R Class I, temere class).
    @cite{solstad-bott-2022}: EXP-STIM verbs show NP2 I-Caus bias. -/
def expStimSubjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- Experiencer-stimulus verb object profile: causation + independent existence.
    The object is a stimulus (cause of the experience). -/
def expStimObjectProfile : EntailmentProfile :=
  ⟨false, false, true, false, true, false, false, false, false, false⟩

/-- Agent-patient verb subject profile: full agent (all 5 P-Agent).
    Identical to existing kickSubjectProfile. -/
def agPatSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

-- ════════════════════════════════════════════════════
-- § 2. Profile Symmetry
-- ════════════════════════════════════════════════════

/-- StimExp subject profile = ExpStim object profile (both are stimulus/C+IE). -/
theorem stimExp_subject_eq_expStim_object :
    stimExpSubjectProfile = expStimObjectProfile := rfl

/-- ExpStim subject profile = StimExp object profile (both are experiencer/S+IE). -/
theorem expStim_subject_eq_stimExp_object :
    expStimSubjectProfile = stimExpObjectProfile := rfl

/-- This is the B&R theta-role reversal expressed at the proto-role level:
    Class I and Class II swap the same two profiles between subject and object. -/
theorem theta_reversal_at_proto_level :
    stimExpSubjectProfile = expStimObjectProfile ∧
    stimExpObjectProfile = expStimSubjectProfile := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Do-Test Behavior
-- ════════════════════════════════════════════════════

/-- StimExp subjects pass the do-test (they have causation).
    "What the noise did was frighten John" is grammatical because the
    subject has the causation entailment (Dowty's P-Agent (c)). -/
theorem stimExp_subject_passes_doTest :
    passesDoTestFromProfile stimExpSubjectProfile = true := by native_decide

/-- ExpStim subjects fail the do-test (experiencers lack volition,
    causation, and movement). "??What Mary did was admire John" is marginal. -/
theorem expStim_subject_fails_doTest :
    passesDoTestFromProfile expStimSubjectProfile = false := by native_decide

/-- AgPat subjects pass the do-test (full agents). -/
theorem agPat_subject_passes_doTest :
    passesDoTestFromProfile agPatSubjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Bridge to ThetaRole
-- ════════════════════════════════════════════════════

/-- StimExp subject profile matches ThetaRole.stimulus's canonical profile. -/
theorem stimExp_profile_matches_stimulus :
    stimExpSubjectProfile = ThetaRole.canonicalProfile .stimulus := rfl

/-- ExpStim subject profile matches ThetaRole.experiencer's canonical profile. -/
theorem expStim_profile_matches_experiencer :
    expStimSubjectProfile = ThetaRole.canonicalProfile .experiencer := rfl

/-- AgPat subject profile matches ThetaRole.agent's canonical profile. -/
theorem agPat_profile_matches_agent :
    agPatSubjectProfile = ThetaRole.canonicalProfile .agent := rfl

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Fragment: Theta Role Annotations
-- ════════════════════════════════════════════════════

/-- ExpStim (Class I) verbs assign experiencer to subject. -/
theorem expStim_verbs_experiencer_subject :
    enjoy.subjectTheta = some .experiencer ∧
    like.subjectTheta = some .experiencer ∧
    love.subjectTheta = some .experiencer ∧
    hate.subjectTheta = some .experiencer :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- StimExp (Class II) verbs assign stimulus to subject. -/
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

/-- IC bias prediction: under Explanation (because), the continuation targets
    the STIMULUS argument — the participant whose entailment profile includes
    causation.

    - StimExp: subject has causation → explanation about subject → NP1
    - ExpStim: subject has sentience only → explanation about object → NP2
    - AgPat: subject has causation (+ volition, etc.) → NP1 -/
def predictICBias (subjProfile : EntailmentProfile) : ICBias :=
  if subjProfile.causation && !subjProfile.sentience then .np1
  else if subjProfile.sentience && !subjProfile.causation then .np2
  else .np1  -- Default: full agents (V+S+C+M+IE) → NP1

/-- StimExp predicted as NP1 (stimulus subject has causation). -/
theorem stimExp_predicted_np1 :
    predictICBias stimExpSubjectProfile = .np1 := by native_decide

/-- ExpStim predicted as NP2 (experiencer subject lacks causation). -/
theorem expStim_predicted_np2 :
    predictICBias expStimSubjectProfile = .np2 := by native_decide

/-- AgPat predicted as NP1 (agent subject — default). -/
theorem agPat_predicted_np1 :
    predictICBias agPatSubjectProfile = .np1 := by native_decide

/-- The prediction matches the empirical data for all tested classes. -/
theorem predictions_match_data :
    predictICBias stimExpSubjectProfile = VerbClass.predictedBias .stimExp ∧
    predictICBias expStimSubjectProfile = VerbClass.predictedBias .expStim ∧
    predictICBias agPatSubjectProfile = VerbClass.predictedBias .agentPat := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 7. Occasion Verbs (@cite{solstad-bott-2024}, S&P 17:11)
-- ════════════════════════════════════════════════════

/-- Occasion verbs in the S&P paper's sense (manage, dare, bother, hesitate)
    have experiencer subjects — same profile as ExpStim (S+IE). They
    presuppose a prior occasioning eventuality but their IC bias properties
    are not directly tested in the 2022 experiment (which studies only
    psych verbs). The fragment entries assign `.experiencer` to their
    subject theta role. -/
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

-- ════════════════════════════════════════════════════
-- § 8. Cross-Study Bridge: @cite{rosa-arnold-2017}
-- ════════════════════════════════════════════════════

open Phenomena.Reference.Studies.RosaArnold2017

/-- @cite{rosa-arnold-2017} and @cite{solstad-bott-2022} demonstrate the same
    mechanism operating across different verb classes and phenomena: **thematic
    roles determine discourse bias independently of grammatical position**.

    IC bias: stimulus argument → causal explanation target → NP1/NP2 bias
    Transfer bias: goal argument → next-mention prediction → pronominalization

    In both cases, swapping the thematic role between subject and object
    changes the bias direction, proving that the role — not the grammatical
    position — drives the effect. This is clearest in the IC reversal: StimExp
    (stimulus=subject) yields NP1 bias while ExpStim (stimulus=object) yields
    NP2 bias, with the bias direction fully predicted by which argument has
    the causation entailment. -/
theorem theta_role_drives_bias_across_phenomena :
    -- Transfer verbs: goal → high next-mention (Rosa & Arnold)
    transferNextMention .goal = .high ∧
    -- IC verbs: stimulus subject → NP1 bias (Solstad & Bott)
    predictICBias stimExpSubjectProfile = .np1 ∧
    -- IC verbs: experiencer subject → NP2 bias (role reversal)
    predictICBias expStimSubjectProfile = .np2 := by
  exact ⟨rfl, by native_decide, by native_decide⟩

/-- Both papers demonstrate coherence-driven modulation of thematic role bias.

    @cite{rosa-arnold-2017}: Occasion/Result coherence amplifies the goal bias
    (β=1.22, p=.002) while Other coherence does not (β=0.86, p=.12). Result
    and Occasion focus on the endpoint/aftermath of the event — the Goal.

    @cite{solstad-bott-2024}: Explanation coherence selects for causes
    (`selectsCause`), and IC bias tracks the argument with the causation
    entailment profile.

    In both cases, the coherence relation TYPE interacts with the thematic
    structure of the verb: Explanation selects the cause/stimulus; Occasion/Result
    selects the endpoint/goal. The coherence relation amplifies a bias that is
    already latent in the verb's thematic structure. -/
theorem coherence_modulates_theta_bias_across_phenomena :
    -- Explanation selects causes (Solstad & Bott)
    CoherenceRelation.explanation.selectsCause = true ∧
    -- Occasion/Result amplifies goal bias (Rosa & Arnold)
    occasionResult_interaction.significant = true ∧
    -- Other coherence does NOT amplify goal bias
    other_interaction.significant = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- @cite{rosa-arnold-2017} explicitly challenges @cite{kehler-rohde-2013}'s
    independence hypothesis: P(pronoun | referent) should depend ONLY on
    subjecthood, not on thematic role. Rosa & Arnold violate this for transfer
    verbs (goals get more pronouns than sources in the same grammatical role).

    The IC data provides an even stronger violation: the ENTIRE continuation
    bias direction (NP1 vs NP2) reverses based on which argument is the
    stimulus, with grammatical position (subject vs object) fully dissociated
    from the bias direction by the StimExp/ExpStim design. -/
theorem ic_reversal_violates_position_only :
    -- StimExp (stimulus=subject): NP1 bias — subject gets continuation
    predictICBias stimExpSubjectProfile = .np1 ∧
    -- ExpStim (stimulus=object): NP2 bias — object gets continuation
    predictICBias expStimSubjectProfile = .np2 ∧
    -- Transfer: goals get more pronouns than sources even in same position
    -- (Rosa & Arnold Exp 1 subject: 64% goal vs 37% source)
    ¬ kehlerRohdeIndependence
      (fun role gram => match role, gram with
        | .goal, .subject => 64 | .source, .subject => 37
        | .goal, .nonsubject => 31 | .source, .nonsubject => 18)
      .subject := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  simp [kehlerRohdeIndependence]

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.ProtoRole
