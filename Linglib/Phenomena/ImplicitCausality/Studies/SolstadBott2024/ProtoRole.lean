import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking
import Linglib.Core.Discourse.CoherenceRelation
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.Reference.Studies.RosaArnold2017
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013

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

open Semantics.Lexical.Verb.EntailmentProfile
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

/-- Despite different sense labels, both senses of "manage" share implicative semantics. -/
theorem manage_senses_share_semantics :
    manage.implicativeBuilder = manage_occasion.implicativeBuilder := rfl

-- ════════════════════════════════════════════════════
-- § 8. Cross-Study Bridge: @cite{rosa-arnold-2017}
-- ════════════════════════════════════════════════════

open Phenomena.Reference.Studies.RosaArnold2017

/-- The IC reversal (StimExp→NP1, ExpStim→NP2) and the transfer verb
    goal bias are both instances of the same deeper pattern: **swapping
    which argument carries a discourse-prominent thematic role reverses
    the discourse bias direction**.

    For IC: swapping stimulus between subject (StimExp) and object (ExpStim)
    reverses the IC bias from NP1 to NP2.
    For transfer: swapping goal between subject and nonsubject doesn't
    eliminate the goal bias — goals still get more pronouns in BOTH positions.

    The IC reversal is the stronger demonstration: it shows the bias direction
    is ENTIRELY determined by the thematic role, not the grammatical position.
    @cite{rosa-arnold-2017}'s data corroborates this by showing that thematic
    role affects form even when grammatical role is held constant, violating
    @cite{kehler-rohde-2013}'s independence hypothesis. -/
theorem thematic_role_not_position_determines_bias :
    -- IC: stimulus=subject → NP1 (derived from entailment profile)
    predictICBias stimExpSubjectProfile = .np1 ∧
    -- IC: stimulus=object (experiencer=subject) → NP2 (reversal!)
    predictICBias expStimSubjectProfile = .np2 ∧
    -- Transfer: goal gets more reduced form than source
    -- (derived from transferNextMention, not stipulated)
    (transferNextMention .goal).predictedForm.rank >
    (transferNextMention .source).predictedForm.rank ∧
    -- Rosa & Arnold's data confirms: independence is violated
    ¬ kehlerRohdeIndependence
      (fun role gram => match role, gram with
        | .goal, .subject => 64 | .source, .subject => 37
        | .goal, .nonsubject => 31 | .source, .nonsubject => 18)
      .subject := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_⟩
  simp [kehlerRohdeIndependence]

/-- Coherence relations select for COMPLEMENTARY thematic roles in the
    two phenomena, demonstrating that the coherence–role interaction is
    systematic rather than accidental:

    Explanation (because) → selects CAUSE → stimulus in psych verbs
    Occasion/Result       → selects ENDPOINT → goal in transfer verbs

    This complementarity is predicted by the semantics of the coherence
    relations: Explanation asks "why did this happen?" (→ cause), while
    Occasion/Result asks "what happened next?" (→ endpoint). The same
    verb may participate in both patterns depending on which coherence
    relation the continuation establishes.

    The empirical signatures differ accordingly:
    - @cite{solstad-bott-2024}: because-continuations target the stimulus
    - @cite{rosa-arnold-2017}: Occasion/Result amplifies goal bias while
      Other (including Explanation) does not -/
theorem coherence_selects_complementary_roles :
    -- Explanation selects causes (the IC mechanism)
    CoherenceRelation.explanation.selectsCause = true ∧
    -- Occasion/Result is the coherence class that amplifies goal bias
    -- (significant for O/R, NOT significant for Other)
    occasionResult_interaction.significant = true ∧
    other_interaction.significant = false ∧
    -- These are genuinely different coherence classes
    CoherenceRelation.explanation.toClass ≠
    CoherenceRelation.occasion.toClass := by
  refine ⟨rfl, rfl, rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 9. Cross-Study Bridge: @cite{kehler-rohde-2013}
-- ════════════════════════════════════════════════════

open Phenomena.Reference.Studies.KehlerRohde2013

/-- @cite{kehler-rohde-2013}'s Table 2 establishes that Explanation
    coherence relations are Source-biased (80% Source for transfer
    verbs). This study's IC data instantiates the same mechanism for
    psych verbs: Explanation (triggered by "because") selects for
    causes, and IC bias tracks whichever argument carries the
    causation entailment — the stimulus.

    K&R's coherence-marginalized model (eq. 9) predicts that IC bias
    should be driven by P(referent | Explanation), not by grammatical
    position. The StimExp/ExpStim reversal confirms this: the bias
    direction is ENTIRELY determined by which argument is the stimulus,
    regardless of subject/object position. -/
theorem ic_instantiates_KR_explanation_bias :
    -- K&R: Explanation is Source-biased and selects for causes
    cr_explanation.cr.selectsCause = true ∧
    cr_explanation.sourceGivenCR > 50 ∧
    -- IC: StimExp (stimulus=subject) → NP1 under "because" (Explanation)
    predictICBias stimExpSubjectProfile = .np1 ∧
    -- IC: ExpStim (stimulus=object) → NP2 under "because" (Explanation)
    predictICBias expStimSubjectProfile = .np2 := by
  exact ⟨rfl, by native_decide, by native_decide, by native_decide⟩

/-- @cite{kehler-rohde-2013}'s key structural claim is that coherence
    relations and referential form contribute to DIFFERENT terms in
    Bayes' rule: P(referent) vs P(pronoun|referent). The IC data
    provides the strongest evidence for the P(referent) side:

    - K&R: P(referent) = Σ_CR P(CR) × P(referent | CR)
    - IC context: "because" sets P(Explanation) ≈ 1
    - Therefore: P(referent) ≈ P(referent | Explanation)
    - P(referent | Explanation) = whichever argument has causation

    This is exactly what the IC data shows: under "because" prompts,
    the bias aligns perfectly with the causation entailment profile,
    as predicted by a model where P(CR=Explanation) dominates the
    mixture and P(referent|Explanation) tracks the stimulus. -/
theorem because_collapses_KR_mixture :
    -- "because" maps to Explanation
    (Connective.toRelation .because) = .explanation ∧
    -- Explanation selects causes (backward causal)
    CoherenceRelation.explanation.selectsCause = true ∧
    -- When P(CR=Explanation) ≈ 1, the mixture reduces to
    -- P(referent | Explanation), which tracks the stimulus:
    -- StimExp stimulus=subject → NP1, ExpStim stimulus=object → NP2
    predictICBias stimExpSubjectProfile = .np1 ∧
    predictICBias expStimSubjectProfile = .np2 := by
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.ProtoRole
