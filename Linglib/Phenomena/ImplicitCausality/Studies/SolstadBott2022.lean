import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking
import Linglib.Core.Discourse.CoherenceRelation
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.Reference.Studies.RosaArnold2017
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013

/-!
# Solstad & Bott (2022): Implicit causality and consequentiality for psych verbs

@cite{solstad-bott-2022} @cite{dowty-1991} @cite{kehler-2002}

Experimental data on implicit causality (I-Caus) and implicit consequentiality
(I-Cons) for German psych verbs, with proto-role analysis and cross-study bridges.

## Verb classes

- **StimExp** (Stimulus-Experiencer): frighten, annoy, amuse — NP1 bias
- **ExpStim** (Experiencer-Stimulus): admire, like, fear — NP2 bias
- **AgentEvocator** (Agent-Evocator): criticise, congratulate — NP2 bias
- **AgentPatient** (Agent-Patient): kick, chase, hit — NP1 bias

## Key empirical findings

1. **Exp 1** (sentence continuation): I-Caus and I-Cons biases mirror each
   other for psych verbs. STIM-EXP: 87.4% NP1 with *weil*; EXP-STIM: 96%
   NP2 with *weil*.
2. **Exp 2** (coherence relations): Explanations dominate over consequences
   for both classes; consequence rate differs by class.
3. **Exp 3** (forced coreference): Asymmetry Hypothesis confirmed — even
   bias-incongruent continuations produce explanations.
4. **Exp 4** (explanation types): Explanatory specifications appear almost
   exclusively in congruent explanations; consequence specifications are
   never produced — supporting verb-semantic I-Caus (Empty Slot Theory)
   vs. discourse-structural I-Cons (Contiguity Principle).

## Two-Mechanism Account (Asymmetry Hypothesis)

I-Caus is verb-semantic: the verb's meaning contains an underspecified causal
slot (Empty Slot Theory) that the continuation fills. I-Cons is discourse-structural:
the Contiguity Principle prefers temporal continuation, defaulting to the endpoint
of the described eventuality.

## Proto-role analysis (@cite{dowty-1991})

IC bias tracks the **stimulus** argument: explanations in *because*-continuations
target the participant whose entailment profile includes causation, regardless
of grammatical position.

| Class    | Subject profile          | P-Agent entailments      |
|----------|--------------------------|--------------------------|
| StimExp  | C + IE (stimulus/causer) | causation, indep.exist.  |
| ExpStim  | S + IE (experiencer)     | sentience, indep.exist.  |
| AgPat    | V + S + C + M + IE       | all five                 |
-/

namespace SolstadBott2022

open Semantics.Lexical.Verb.EntailmentProfile
open Core.Discourse.CoherenceRelation
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Verb Classes and IC Bias
-- ════════════════════════════════════════════════════

/-- Verb classes from the IC bias literature. -/
inductive VerbClass where
  | stimExp        -- StimExp: frighten, annoy, amuse — subject is stimulus
  | expStim        -- ExpStim: admire, like, fear — subject is experiencer
  | agentEvocator  -- AgEvoc: criticise, congratulate — subject acts on evocator
  | agentPat       -- AgPat: kick, chase, hit — subject is agent
  deriving DecidableEq, Repr

/-- Implicit causality bias direction. -/
inductive ICBias where
  | np1   -- Subject-biased (explanation targets subject referent)
  | np2   -- Object-biased (explanation targets object referent)
  deriving DecidableEq, Repr

/-- Predicted IC bias direction for each verb class.

    The IC bias tracks the STIMULUS argument, not the subject per se:
    - StimExp (stimulus = subject) → NP1 (explanation about subject)
    - ExpStim (stimulus = object) → NP2 (explanation about object)
    - AgentEvocator (evocator = object) → NP2
    - AgPat (agent = subject) → NP1 (default) -/
def VerbClass.predictedBias : VerbClass → ICBias
  | .stimExp       => .np1   -- stimulus is subject → NP1
  | .expStim       => .np2   -- stimulus is object → NP2
  | .agentEvocator => .np2   -- evocator is object → NP2
  | .agentPat      => .np1   -- agent is subject → NP1

-- ════════════════════════════════════════════════════
-- § 2. Exp 1: Coreference Biases (Table 1)
-- ════════════════════════════════════════════════════

/-- Connective conditions in @cite{solstad-bott-2022}.
    German connectives *weil* (because) and *sodass* (and so). -/
inductive ExpConnective where
  | weil      -- "because" → I-Caus (Explanation relation)
  | sodass    -- "and so" → I-Cons (Consequence relation)
  deriving DecidableEq, Repr

/-- Subject coreference proportion from Exp 1, Table 1 of @cite{solstad-bott-2022}.
    These are real data from 52 German participants with 20 STIM-EXP and
    20 EXP-STIM verbs (gefallen excluded). -/
structure CorefDatum where
  verbClass : VerbClass
  connective : ExpConnective
  subjectCorefPct : ℚ    -- Percentage of NP1 (subject) coreference
  deriving Repr

-- Exp 1, Table 1 (@cite{solstad-bott-2022}, p. 1322)
def exp1_stimExp_weil   : CorefDatum := ⟨.stimExp, .weil, 874/10⟩   -- 87.4%
def exp1_expStim_weil   : CorefDatum := ⟨.expStim, .weil, 40/10⟩    -- 4.0%
def exp1_stimExp_sodass : CorefDatum := ⟨.stimExp, .sodass, 48/10⟩  -- 4.8%
def exp1_expStim_sodass : CorefDatum := ⟨.expStim, .sodass, 779/10⟩ -- 77.9%

/-- StimExp and ExpStim have opposite predicted IC bias. -/
theorem stimExp_opposes_expStim :
    VerbClass.predictedBias .stimExp ≠
    VerbClass.predictedBias .expStim := by decide

/-- I-Caus (weil): StimExp has strong NP1 bias (87.4% > 50%). -/
theorem stimExp_weil_np1_bias :
    exp1_stimExp_weil.subjectCorefPct > 50 := by
  show 50 < (874 : ℚ)/10; norm_num

/-- I-Caus (weil): ExpStim has strong NP2 bias (4.0% < 50%). -/
theorem expStim_weil_np2_bias :
    exp1_expStim_weil.subjectCorefPct < 50 := by
  show (40 : ℚ)/10 < 50; norm_num

/-- I-Cons (sodass): Biases mirror I-Caus — StimExp → NP2, ExpStim → NP1.
    (@cite{solstad-bott-2022}, §2.3: "almost perfect negative correlation" r = −0.94) -/
theorem icons_mirrors_icaus :
    exp1_stimExp_sodass.subjectCorefPct < 50 ∧
    exp1_expStim_sodass.subjectCorefPct > 50 := by
  constructor
  · show (48 : ℚ)/10 < 50; norm_num
  · show 50 < (779 : ℚ)/10; norm_num

-- ════════════════════════════════════════════════════
-- § 3. Exp 3: Forced Coreference — Asymmetry Hypothesis
-- ════════════════════════════════════════════════════

/-- Coherence relation types produced in continuations. -/
inductive ContinuationType where
  | explanation    -- Backward-looking causal relation
  | consequence    -- Forward-looking result relation
  deriving DecidableEq, Repr

/-- Congruence: whether the forced coreference target matches the verb's
    predicted IC bias direction. -/
inductive Congruence where
  | congruent      -- Forced referent matches predicted bias
  | incongruent    -- Forced referent opposes predicted bias
  deriving DecidableEq, Repr

/-- Exp 3 data: proportion of explanations (vs consequences) under forced
    coreference. @cite{solstad-bott-2022} Table 3.

    The key finding: even when forced to refer to the non-biased argument
    (incongruent condition), participants STILL produce explanations rather
    than consequences. This supports the Asymmetry Hypothesis — I-Caus
    (explanation-seeking) is the default mechanism driven by verb semantics,
    while I-Cons only emerges when discourse structure demands it. -/
structure ForcedCorefDatum where
  verbClass : VerbClass
  congruence : Congruence
  explanationPct : ℚ      -- % of continuations that are explanations
  deriving Repr

-- Exp 3, Table 3 (@cite{solstad-bott-2022}, p. 1326)
def exp3_stimExp_congruent   : ForcedCorefDatum := ⟨.stimExp, .congruent, 879/10⟩    -- 87.9%
def exp3_stimExp_incongruent : ForcedCorefDatum := ⟨.stimExp, .incongruent, 876/10⟩  -- 87.6%
def exp3_expStim_congruent   : ForcedCorefDatum := ⟨.expStim, .congruent, 837/10⟩    -- 83.7%
def exp3_expStim_incongruent : ForcedCorefDatum := ⟨.expStim, .incongruent, 870/10⟩  -- 87.0%

/-- Asymmetry Hypothesis: explanations dominate regardless of congruence.
    Even in bias-incongruent conditions, explanation rate stays above 80%.
    This shows I-Caus (explanation) is the default mechanism. -/
theorem asymmetry_hypothesis_exp3 :
    exp3_stimExp_incongruent.explanationPct > 80 ∧
    exp3_expStim_incongruent.explanationPct > 80 := by
  constructor
  · show 80 < (876 : ℚ)/10; norm_num
  · show 80 < (870 : ℚ)/10; norm_num

/-- Congruence does NOT significantly affect explanation rate —
    incongruent and congruent conditions produce similar proportions.
    This is the core prediction of the Asymmetry Hypothesis: if I-Caus
    were simply the mirror of I-Cons, incongruent coreference should
    force consequence relations, but it doesn't. -/
theorem congruence_does_not_reduce_explanations :
    -- StimExp: 87.9% congruent vs 87.6% incongruent (virtually identical)
    exp3_stimExp_congruent.explanationPct - exp3_stimExp_incongruent.explanationPct < 1 ∧
    -- ExpStim: 83.7% congruent vs 87.0% incongruent (incongruent even higher!)
    exp3_expStim_incongruent.explanationPct ≥ exp3_expStim_congruent.explanationPct := by
  constructor
  · show (879 : ℚ)/10 - (876 : ℚ)/10 < 1; norm_num
  · show (837 : ℚ)/10 ≤ (870 : ℚ)/10; norm_num

-- ════════════════════════════════════════════════════
-- § 4. Exp 4: Explanation Types — Two-Mechanism Account
-- ════════════════════════════════════════════════════

/-- Subtypes of explanation continuations from Exp 4 annotation.
    @cite{solstad-bott-2022} distinguishes three explanation categories:
    - **specifying**: fills the verb's causal slot (Empty Slot Theory prediction)
    - **mentalBackground**: provides the experiencer's mental state
    - **nonmentalBackground**: provides non-mental context -/
inductive ExplanationSubtype where
  | specifying          -- Explanatory specification (fills causal slot)
  | mentalBackground    -- Mental state of experiencer
  | nonmentalBackground -- Non-mental background
  deriving DecidableEq, Repr

/-- Exp 4 explanation subtype frequencies. Table 4 of @cite{solstad-bott-2022}. -/
structure ExplanationTypeDatum where
  verbClass : VerbClass
  congruence : Congruence
  specifyingPct : ℚ          -- % explanatory specifications
  mentalBgPct : ℚ            -- % mental background
  nonmentalBgPct : ℚ         -- % non-mental background
  deriving Repr

-- Exp 4, Table 4 — explanation subtypes (@cite{solstad-bott-2022}, p. 1333)
-- Absolute frequencies (n): converted to approximate percentages
def exp4_stimExp_congruent_expl : ExplanationTypeDatum :=
  ⟨.stimExp, .congruent, 876/10, 22/10, 102/10⟩      -- 87.6% spec, 2.2% mental, 10.2% nonmental
def exp4_stimExp_incongruent_expl : ExplanationTypeDatum :=
  ⟨.stimExp, .incongruent, 10/10, 600/10, 390/10⟩    -- 1.0% spec, 60.0% mental, 39.0% nonmental
def exp4_expStim_congruent_expl : ExplanationTypeDatum :=
  ⟨.expStim, .congruent, 982/10, 14/10, 4/10⟩        -- 98.2% spec, 1.4% mental, 0.4% nonmental
def exp4_expStim_incongruent_expl : ExplanationTypeDatum :=
  ⟨.expStim, .incongruent, 85/10, 913/10, 2/10⟩      -- 8.5% spec, 91.3% mental, 0.2% nonmental

/-- Empty Slot Theory prediction: explanatory specifications dominate in
    congruent conditions (where the continuation fills the verb's causal slot). -/
theorem empty_slot_congruent_specifications :
    exp4_stimExp_congruent_expl.specifyingPct > 80 ∧
    exp4_expStim_congruent_expl.specifyingPct > 80 := by
  constructor
  · show 80 < (876 : ℚ)/10; norm_num
  · show 80 < (982 : ℚ)/10; norm_num

/-- Empty Slot Theory prediction: explanatory specifications nearly vanish
    in incongruent conditions (the "wrong" argument cannot fill the slot). -/
theorem empty_slot_incongruent_no_specifications :
    exp4_stimExp_incongruent_expl.specifyingPct < 5 ∧
    exp4_expStim_incongruent_expl.specifyingPct < 10 := by
  constructor
  · show (10 : ℚ)/10 < 5; norm_num
  · show (85 : ℚ)/10 < 10; norm_num

/-- Two-Mechanism Account: consequence specifications are never produced
    (0.4% STIM-EXP, 0.0% EXP-STIM in Table 4). The specification strategy
    is not available for consequences — only for explanations. This is because
    I-Cons derives from the Contiguity Principle (discourse-structural), not
    from an underspecified slot in verb meaning (verb-semantic).

    We encode this as: consequence-specification is not a viable strategy. -/
def consequenceSpecificationRate (vc : VerbClass) : ℚ :=
  match vc with
  | .stimExp => 4/10    -- 0.4% (Table 4)
  | .expStim => 0       -- 0.0% (Table 4)
  | _ => 0

theorem consequence_specification_negligible :
    consequenceSpecificationRate .stimExp < 1 ∧
    consequenceSpecificationRate .expStim < 1 := by
  constructor <;> norm_num [consequenceSpecificationRate]

-- ════════════════════════════════════════════════════
-- § 5. Entailment Profiles for Verb Classes
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
-- § 6. Profile Symmetry
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
-- § 7. Do-Test Behavior
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
-- § 8. Bridge to ThetaRole
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
-- § 9. IC Bias Prediction via Coherence Relations
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
-- § 10. Cross-Study Bridge: @cite{rosa-arnold-2017}
-- ════════════════════════════════════════════════════

open RosaArnold2017

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
    two phenomena, demonstrating that the coherence-role interaction is
    systematic rather than accidental:

    Explanation (because) → selects CAUSE → stimulus in psych verbs
    Occasion/Result       → selects ENDPOINT → goal in transfer verbs

    This complementarity is predicted by the semantics of the coherence
    relations: Explanation asks "why did this happen?" (→ cause), while
    Occasion/Result asks "what happened next?" (→ endpoint). -/
theorem coherence_selects_complementary_roles :
    -- Explanation selects causes (the IC mechanism)
    CoherenceRelation.explanation.selectsCause = true ∧
    -- Occasion/Result is the coherence class that amplifies goal bias
    occasionResult_interaction.significant = true ∧
    other_interaction.significant = false ∧
    -- These are genuinely different coherence classes
    CoherenceRelation.explanation.toClass ≠
    CoherenceRelation.occasion.toClass := by
  refine ⟨rfl, rfl, rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 11. Cross-Study Bridge: @cite{kehler-rohde-2013}
-- ════════════════════════════════════════════════════

open KehlerRohde2013

/-- @cite{kehler-rohde-2013}'s Table 2 establishes that Explanation
    coherence relations are Source-biased (80% Source for transfer
    verbs). This study's IC data instantiates the same mechanism for
    psych verbs: Explanation (triggered by "because") selects for
    causes, and IC bias tracks whichever argument carries the
    causation entailment — the stimulus. -/
theorem ic_instantiates_KR_explanation_bias :
    cr_explanation.cr.selectsCause = true ∧
    cr_explanation.sourceGivenCR > 50 ∧
    predictICBias stimExpSubjectProfile = .np1 ∧
    predictICBias expStimSubjectProfile = .np2 := by
  exact ⟨rfl, by native_decide, by native_decide, by native_decide⟩

/-- @cite{kehler-rohde-2013}'s key structural claim is that coherence
    relations and referential form contribute to DIFFERENT terms in
    Bayes' rule: P(referent) vs P(pronoun|referent). The IC data
    provides the strongest evidence for the P(referent) side:

    - K&R: P(referent) = Σ_CR P(CR) × P(referent | CR)
    - IC context: "because" sets P(Explanation) ≈ 1
    - Therefore: P(referent) ≈ P(referent | Explanation)
    - P(referent | Explanation) = whichever argument has causation -/
theorem because_collapses_KR_mixture :
    (Connective.toRelation .because) = .explanation ∧
    CoherenceRelation.explanation.selectsCause = true ∧
    predictICBias stimExpSubjectProfile = .np1 ∧
    predictICBias expStimSubjectProfile = .np2 := by
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

end SolstadBott2022
