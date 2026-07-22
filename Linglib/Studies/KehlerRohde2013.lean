import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Discourse.Coherence
import Linglib.Data.UD.Basic
import Linglib.Discourse.Centering.Pronominalization
import Linglib.Discourse.Centering.Instances.GrammaticalRole
import Linglib.Discourse.Accessibility

/-!
# Pronoun interpretation: coherence vs. centering [kehler-rohde-2013]

[kehler-rohde-2013] reconcile [hobbs-1979]'s coherence-driven account of pronoun
interpretation with the centering-driven account of [grosz-joshi-weinstein-1995]
through a Bayesian decomposition,
`P(referent | pronoun) ∝ P(pronoun | referent) × P(referent)`. The prior
`P(referent)` is a coherence-driven next-mention bias; the likelihood
`P(pronoun | referent)` is a centering-driven topichood (production) bias. The
two components are empirically dissociable across five passage-completion
experiments with transfer-of-possession and implicit-causality verbs.

## Main declarations

* `NextMentionModel`, `NextMentionModel.sourceBias`: the coherence-marginalized
  prior `P(Source) = Σ_CR P(CR) · P(Source | CR)` (the paper's Eq. (9)).
* `topichood`, `TopichoodLevel`: voice and surface position to topichood, the
  centering-driven likelihood term.
* `bayesianPrediction`: Bayesian inversion to `P(Subject | pronoun)` (Eq. (13)).
* `NextMentionModel.toBias`: coarsening of the prior to the two-point
  `Discourse.NextMentionBias`, with `expectancy_reversed_under_voice` refuting the
  expectancy hypothesis the substrate's `predictedForm` encodes.
* `cb_topichood_dissociation_under_voice`: Centering's backward-looking center is
  voice-blind where `topichood` is voice-sensitive.

## Implementation notes

Probabilities are exact rationals (`ℚ`) on a 0–100 percentage scale; empirical
values are quoted from the paper's Tables 1–10. `sourceBias` marginalizes over
`CoherenceRelation.all`, so adding a coherence relation forces the mixture to be
revisited (via `CoherenceRelation.mem_all`) rather than silently dropping it.

## References

[hobbs-1979] [kehler-2002] [davison-1984] [kameyama-1986] [grosz-joshi-weinstein-1995]
-/

namespace KehlerRohde2013

open Discourse.Coherence
open UD (Voice)

/-! ### Experimental design -/

/-- Prompt type in passage completion experiments. -/
inductive PromptType where
  | pronoun      -- "She ___"
  | noPronoun    -- "___" (free completion)
  deriving DecidableEq, Repr

/-- Instruction condition (transfer-of-possession experiments). -/
inductive InstructionCond where
  | whatNext   -- "What happened next?"
  | why        -- "Why?"
  deriving DecidableEq, Repr

/-! ### The Bayesian model -/

/-- The coherence-marginalized next-mention bias (the paper's Eq. (9)):
    `P(referent) = Σ_CR P(CR) × P(referent | CR)`, a mixture of CR-specific biases
    weighted by the prior over coherence relations — the coherence-driven prior.
    Probabilities are percentages (0–100). -/
structure NextMentionModel where
  /-- P(CR): prior probability of coherence relation (%) -/
  pCR : CoherenceRelation → ℚ
  /-- P(referent = Source | CR): Source bias given CR (%) -/
  pSourceGivenCR : CoherenceRelation → ℚ

/-- Topichood level, determined by grammatical construction. Passive subjects
    signal stronger topichood than active subjects, since a marked construction
    placing an entity in subject position is a stronger topic indicator
    ([davison-1984]). The likelihood `P(pronoun | referent)` tracks this level,
    not grammatical role per se. -/
inductive TopichoodLevel where
  | strong    -- subject of passive clause (marked promotion)
  | default_  -- subject of active clause
  | low       -- non-subject
  deriving DecidableEq, Repr

/-- Compute topichood from voice and surface position. -/
def topichood (voice : Voice) (isSubject : Bool) : TopichoodLevel :=
  match voice, isSubject with
  | _,     false => .low
  | .Pass, true  => .strong
  | _,     true  => .default_

/-! ### Aspect manipulation -/

/-- Table 1: Source interpretation rate by aspect. Imperfective focuses on the
    ongoing event (Source still central); perfective focuses on the end state
    (Goal = endpoint of transfer). -/
def sourceInterpPerfective : ℚ := 57
def sourceInterpImperfective : ℚ := 80

/-- Imperfective yields more Source interpretations than perfective. -/
theorem imperfective_more_source :
    sourceInterpImperfective > sourceInterpPerfective := by
  norm_num [sourceInterpImperfective, sourceInterpPerfective]

/-! ### Coherence relation analysis -/

/-- Coherence relation frequency and bias data from Table 2 (perfective
    condition, transfer-of-possession verbs). The paper's "Violated Expectation"
    is modelled as `CoherenceRelation.contrast`: it is a denial-of-expectation
    relation, which [umbach-2004] classes with contrast, though [kehler-2002]
    alternatively files it under cause-effect. No theorem here depends on its
    coherence class. -/
structure CRDatum where
  cr : CoherenceRelation
  freqPct : ℚ           -- frequency of occurrence (%)
  sourceGivenCR : ℚ     -- P(Source interpretation | CR) (%)
  deriving Repr

def crOccasion     : CRDatum := ⟨.occasion,      38, 18⟩
def crElaboration  : CRDatum := ⟨.elaboration,   28, 98⟩
def crExplanation  : CRDatum := ⟨.explanation,    18, 80⟩
def crViolatedExp  : CRDatum := ⟨.contrast,       8, 76⟩
def crResult       : CRDatum := ⟨.result,          6,  8⟩

/-- Occasion and Result are Goal-biased (Source < 50%). -/
theorem goal_biased_crs :
    crOccasion.sourceGivenCR < 50 ∧ crResult.sourceGivenCR < 50 := by
  norm_num [crOccasion, crResult]

/-- Elaboration, Explanation, and Violated Expectation are Source-biased. -/
theorem source_biased_crs :
    crElaboration.sourceGivenCR > 50 ∧
    crExplanation.sourceGivenCR > 50 ∧
    crViolatedExp.sourceGivenCR > 50 := by
  norm_num [crElaboration, crExplanation, crViolatedExp]

/-- The overall ~57/43 Source/Goal split masks strong CR-conditioned biases:
    Occasion is most common (.38) and Goal-biased (.18 Source); Elaboration is
    second (.28) and strongly Source-biased (.98). -/
theorem biases_masked_by_mixture :
    crOccasion.sourceGivenCR < 50 ∧ crElaboration.sourceGivenCR > 50 ∧
    crOccasion.freqPct > crElaboration.freqPct := by
  norm_num [crOccasion, crElaboration]

/-! ### Instruction manipulation: P(CR) shift -/

/-- Table 3: "What happened next?" yields Occasion-dominated completions; "Why?"
    yields Explanation-dominated ones. Instructions shift P(CR) without changing
    the stimuli. -/
def whatNextOccasionPct    : ℚ := 71
def whatNextExplanationPct : ℚ :=  1
def whyOccasionPct         : ℚ :=  1
def whyExplanationPct      : ℚ := 91

theorem instructions_shift_pCR :
    whatNextOccasionPct > whyOccasionPct ∧
    whyExplanationPct > whatNextExplanationPct := by
  norm_num [whatNextOccasionPct, whyOccasionPct, whyExplanationPct, whatNextExplanationPct]

/-- Table 5: Source interpretation by instruction condition (perfective).
    Shifting P(CR) shifts P(referent), as predicted by the mixture (Eq. (9)). -/
def whatNextSourcePct : ℚ := 34
def whySourcePct      : ℚ := 82

theorem instructions_shift_interpretation :
    whySourcePct > whatNextSourcePct := by
  norm_num [whySourcePct, whatNextSourcePct]

/-- The instruction effect is 48 pp on identical stimuli — no morphosyntactic
    heuristic can account for it. -/
theorem instruction_effect_magnitude :
    whySourcePct - whatNextSourcePct > 40 := by
  norm_num [whySourcePct, whatNextSourcePct]

/-! ### Bias stability: P(ref | CR) invariance -/

/-- Table 4: P(Source | CR) is stable across the original experiment and the
    instruction manipulation, supporting the structural claim that CR-conditioned
    biases are properties of the coherence relation itself, not the experimental
    context. -/
structure StabilityDatum where
  cr : CoherenceRelation
  originalPct : ℚ
  instructionPct : ℚ
  deriving Repr

def stabElaboration : StabilityDatum := ⟨.elaboration, 98, 100⟩
def stabExplanation : StabilityDatum := ⟨.explanation,  80,  82⟩
def stabOccasion    : StabilityDatum := ⟨.occasion,     18,  27⟩
def stabResult      : StabilityDatum := ⟨.result,        8,   9⟩

/-- Bias direction (above/below 50%) is preserved for all five CRs across
    conditions: P(CR) can shift independently of P(ref | CR). -/
theorem bias_direction_stable :
    (stabElaboration.originalPct > 50 ∧ stabElaboration.instructionPct > 50) ∧
    (stabExplanation.originalPct > 50 ∧ stabExplanation.instructionPct > 50) ∧
    (stabOccasion.originalPct < 50 ∧ stabOccasion.instructionPct < 50) ∧
    (stabResult.originalPct < 50 ∧ stabResult.instructionPct < 50) := by
  norm_num [stabElaboration, stabExplanation, stabOccasion, stabResult]

/-! ### Bidirectionality: pronoun → coherence -/

/-- Table 6: CR distribution by prompt type. The mere presence of an ambiguous
    pronoun shifts coherence expectations toward Source-biased relations. This
    bidirectionality — coreference affects coherence, not just vice versa — is
    predicted by Bayes (Eq. (12)) but not by Hobbs (pronouns are inert free
    variables) or Centering (does not model coherence). -/
structure PromptCRDatum where
  prompt : PromptType
  cr : CoherenceRelation
  freqPct : ℚ
  deriving Repr

def npElaboration  : PromptCRDatum := ⟨.noPronoun, .elaboration,  6⟩
def npExplanation  : PromptCRDatum := ⟨.noPronoun, .explanation, 20⟩
def npOccasion     : PromptCRDatum := ⟨.noPronoun, .occasion,    36⟩
def npResult       : PromptCRDatum := ⟨.noPronoun, .result,      13⟩

def ppElaboration  : PromptCRDatum := ⟨.pronoun, .elaboration, 20⟩
def ppExplanation  : PromptCRDatum := ⟨.pronoun, .explanation, 28⟩
def ppOccasion     : PromptCRDatum := ⟨.pronoun, .occasion,    28⟩
def ppResult       : PromptCRDatum := ⟨.pronoun, .result,       5⟩

/-- Pronoun prompt increases Source-biased CRs. -/
theorem pronoun_boosts_source_CRs :
    ppElaboration.freqPct > npElaboration.freqPct ∧
    ppExplanation.freqPct > npExplanation.freqPct := by
  norm_num [ppElaboration, npElaboration, ppExplanation, npExplanation]

/-- Pronoun prompt decreases Goal-biased CRs. -/
theorem pronoun_reduces_goal_CRs :
    ppOccasion.freqPct < npOccasion.freqPct ∧
    ppResult.freqPct < npResult.freqPct := by
  norm_num [ppOccasion, npOccasion, ppResult, npResult]

/-! ### Voice manipulation: implicit-causality verbs -/

-- Table 7: Proportion of next mentions to the causally-implicated referent.
-- Subject-biased IC verbs (e.g., "Amanda amazed Brittany"):
-- Active: causal referent (Amanda) = subject
-- Passive: causal referent (Amanda) = by-phrase (non-subject)

def nmActivePron     : ℚ := 77
def nmActiveNoPron   : ℚ := 59
def nmPassivePron    : ℚ := 42
def nmPassiveNoPron  : ℚ := 76

/-- Voice affects next-mention in the pronoun condition: active (.77) vs.
    passive (.42). Passivization moves the causally-implicated referent out of
    subject position — same proposition, different bias. -/
theorem voice_affects_nextMention :
    nmActivePron > nmPassivePron := by
  norm_num [nmActivePron, nmPassivePron]

/-- In the no-pronoun condition the pattern reverses: passive (.76) > active
    (.59). By-phrases are optional in English, so their inclusion signals the
    referent will be re-mentioned. -/
theorem noPronoun_pattern_reverses :
    nmPassiveNoPron > nmActiveNoPron := by
  norm_num [nmPassiveNoPron, nmActiveNoPron]

-- Table 8: Proportion of Explanation relations (pronoun condition)
def explActivePron  : ℚ := 75
def explPassivePron : ℚ := 52

/-- Voice affects coherence in the pronoun condition: active produces more
    Explanations than passive. Since the propositions are identical, this is
    mediated by the shift in pronominal reference — bidirectional
    coherence–coreference dependency. -/
theorem voice_affects_coherence :
    explActivePron > explPassivePron := by
  norm_num [explActivePron, explPassivePron]

-- Table 9: Pronominalization rates by voice × surface position
def pronActiveSubj     : ℚ := 62
def pronActiveNonSubj  : ℚ := 24
def pronPassiveSubj    : ℚ := 87
def pronPassiveNonSubj : ℚ := 23

/-- Passive subjects are pronominalized more than active subjects (87% vs. 62%).
    Both are subjects, so this is not explicable by grammatical role; it reflects
    the stronger topichood signal of the passive — the key evidence that
    `P(pronoun | referent)` tracks topichood, not subjecthood. -/
theorem passive_subj_more_pronominalized :
    pronPassiveSubj > pronActiveSubj := by
  norm_num [pronPassiveSubj, pronActiveSubj]

/-- Non-subject pronominalization is invariant across voice (24% vs. 23%): at the
    same (low) topichood level, the voice manipulation has no effect on
    pronominalization rate. This is the Independence Hypothesis —
    `P(pronoun | referent)` does not depend on coherence-driven factors. -/
theorem nonSubj_pron_invariant :
    pronActiveNonSubj - pronPassiveNonSubj ≤ 1 := by
  norm_num [pronActiveNonSubj, pronPassiveNonSubj]

/-- Subjects are pronominalized more than non-subjects in both voices — the
    centering-derived component. -/
theorem subject_advantage_both_voices :
    pronActiveSubj > pronActiveNonSubj ∧
    pronPassiveSubj > pronPassiveNonSubj := by
  norm_num [pronActiveSubj, pronActiveNonSubj, pronPassiveSubj, pronPassiveNonSubj]

/-- Topichood monotonically predicts pronominalization: strong (passive subject,
    87%) > default (active subject, 62%) > low (non-subject, ~24%). -/
theorem topichood_monotone :
    pronPassiveSubj > pronActiveSubj ∧
    pronActiveSubj > pronActiveNonSubj := by
  norm_num [pronPassiveSubj, pronActiveSubj, pronActiveNonSubj]

-- Table 10: Predicted vs. actual interpretation biases. The Bayesian model
-- estimates P(referent) from no-pronoun data and P(pronoun | referent) from
-- pronominalization rates, then predicts P(referent | pronoun) via Eq. (13).

def predictedActiveSubj  : ℚ := 81
def actualActiveSubj     : ℚ := 74
def predictedPassiveSubj : ℚ := 59
def actualPassiveSubj    : ℚ := 60

/-- Bayesian predictions are directionally correct: active > passive in both
    predicted and actual biases. -/
theorem bayesian_directionally_correct :
    predictedActiveSubj > predictedPassiveSubj ∧
    actualActiveSubj > actualPassiveSubj := by
  norm_num [predictedActiveSubj, predictedPassiveSubj, actualActiveSubj, actualPassiveSubj]

/-- The passive prediction is highly accurate (59% vs. 60%). -/
theorem passive_prediction_accurate :
    actualPassiveSubj - predictedPassiveSubj ≤ 1 := by
  norm_num [actualPassiveSubj, predictedPassiveSubj]

/-! ### Mixture derivation (Eq. (9)) -/

/-- The coherence-marginalized Source bias of a `NextMentionModel`. This is the
    paper's Eq. (9), `P(Source) = Σ_CR P(CR) × P(Source | CR)`, as a percentage —
    marginalizing over `CoherenceRelation.all`. -/
def NextMentionModel.sourceBias (m : NextMentionModel) : ℚ :=
  (CoherenceRelation.all.foldl (λ acc cr => acc + m.pCR cr * m.pSourceGivenCR cr) 0) / 100

/-- The two instruction-manipulation models share the same P(Source | CR) — the
    CR-conditioned biases from Table 4 (instruction column) — differing only in
    P(CR). -/
private def sharedBias : CoherenceRelation → ℚ
  | .occasion    => 27
  | .elaboration => 100
  | .explanation => 82
  | .contrast    => 74
  | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
  | .result      =>  9
  | .parallel    => 50
  -- SDRT additions, not in K&R 2013 coding scheme.
  | .background  =>  0
  | .consequence =>  0
  | .alternation =>  0

def whatNextModel : NextMentionModel where
  pCR := fun
    | .occasion    => 71
    | .explanation =>  1
    | .elaboration =>  5
    | .contrast    =>  8
    | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
    | .result      =>  5
    | .parallel    => 10
    -- SDRT additions, 0% weight in K&R 2013 mixture.
    | .background  =>  0
    | .consequence =>  0
    | .alternation =>  0
  pSourceGivenCR := sharedBias

def whyModel : NextMentionModel where
  pCR := fun
    | .occasion    =>  1
    | .explanation => 91
    | .elaboration =>  8
    | .contrast    =>  1
    | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
    | .result      =>  0
    | .parallel    =>  0
    -- SDRT additions, 0% weight in K&R 2013 mixture.
    | .background  =>  0
    | .consequence =>  0
    | .alternation =>  0
  pSourceGivenCR := sharedBias

/-- The two instruction models share their CR-conditioned biases: the instruction
    manipulation changes P(CR) while holding P(ref | CR) constant (Table 4). -/
theorem instruction_models_share_bias :
    whatNextModel.pSourceGivenCR = whyModel.pSourceGivenCR := rfl

/-- The "Why?" mixture exceeds the "What next?" mixture, derived from the model
    rather than read off Table 5: Explanation (Source-biased at 82%) dominates the
    "Why?" mixture at 91% P(CR). -/
theorem eq9_why_exceeds_whatNext :
    whyModel.sourceBias > whatNextModel.sourceBias := by
  simp only [NextMentionModel.sourceBias, whyModel, whatNextModel, sharedBias,
    CoherenceRelation.all, List.foldl_cons, List.foldl_nil]
  norm_num

/-- The computed mixtures track Table 5: "Why?" → ~84% Source, "What next?" →
    ~36% Source (vs. observed 82% and 34%), the small gap from integer rounding
    and the "Other" CR category. -/
theorem eq9_mixtures_approximate_table5 :
    whyModel.sourceBias > 80 ∧ whatNextModel.sourceBias < 40 := by
  refine ⟨?_, ?_⟩ <;>
    · simp only [NextMentionModel.sourceBias, whyModel, whatNextModel, sharedBias,
        CoherenceRelation.all, List.foldl_cons, List.foldl_nil]
      norm_num

/-! ### Bayesian inversion (Eq. (13)) -/

/-- P(Subject | pronoun) via Bayes' rule (Eq. (13)), from P(Subject
    next-mentioned) (no-pronoun data) and P(pronoun | position)
    (pronominalization rates). Result is a percentage. -/
def bayesianPrediction (pSubj pPronSubj pPronNonSubj : ℚ) : ℚ :=
  let num := pPronSubj * pSubj
  let den := pPronSubj * pSubj + pPronNonSubj * (100 - pSubj)
  num * 100 / den

/-- Active voice: from P(Subject) = 59% (Table 7), P(pronoun | Subject) = 62%,
    P(pronoun | NonSubject) = 24% (Table 9), Bayes' rule yields ≈ 78% (the paper
    reports 81% from unrounded data; the direction matches). -/
theorem eq13_active_prediction :
    bayesianPrediction nmActiveNoPron pronActiveSubj pronActiveNonSubj
    > 50 := by
  norm_num [bayesianPrediction, nmActiveNoPron, pronActiveSubj, pronActiveNonSubj]

/-- Passive voice: from P(Subject) = 100 − 76 = 24% (Table 7), P(pronoun |
    Subject) = 87%, P(pronoun | NonSubject) = 23% (Table 9), Bayes' rule yields
    ≈ 54%. -/
theorem eq13_passive_prediction :
    bayesianPrediction (100 - nmPassiveNoPron) pronPassiveSubj
      pronPassiveNonSubj > 50 := by
  norm_num [bayesianPrediction, nmPassiveNoPron, pronPassiveSubj, pronPassiveNonSubj]

/-- Bayes' rule derives active > passive for P(Subject | pronoun) even though
    passive subjects are pronominalized more (87% vs. 62%): the lower passive
    prior P(Subject) (24% vs. 59%) dominates, reversing the production bias. -/
theorem eq13_active_exceeds_passive :
    bayesianPrediction nmActiveNoPron pronActiveSubj pronActiveNonSubj >
    bayesianPrediction (100 - nmPassiveNoPron) pronPassiveSubj
      pronPassiveNonSubj := by
  norm_num [bayesianPrediction, nmActiveNoPron, nmPassiveNoPron,
    pronActiveSubj, pronActiveNonSubj, pronPassiveSubj, pronPassiveNonSubj]

/-! ### Expectancy coarsening -/

/-- Coarsen a next-mention rate (a percentage) to the two-point
    `Discourse.NextMentionBias` by thresholding at 50%. -/
def biasOfRate (p : ℚ) : Discourse.NextMentionBias :=
  if 50 < p then .high else .low

/-- The Bayesian prior coarsened to the two-point substrate bias:
    `Discourse.NextMentionBias` is the sign of `sourceBias − 50`. -/
def NextMentionModel.toBias (m : NextMentionModel) : Discourse.NextMentionBias :=
  biasOfRate m.sourceBias

/-- The "Why?" mixture coarsens to `.high` (Source-biased). -/
theorem whyModel_toBias : whyModel.toBias = .high := by
  simp only [NextMentionModel.toBias, biasOfRate, NextMentionModel.sourceBias,
    whyModel, sharedBias, CoherenceRelation.all, List.foldl_cons, List.foldl_nil]
  norm_num

/-- The "What next?" mixture coarsens to `.low` (Goal-biased). -/
theorem whatNextModel_toBias : whatNextModel.toBias = .low := by
  simp only [NextMentionModel.toBias, biasOfRate, NextMentionModel.sourceBias,
    whatNextModel, sharedBias, CoherenceRelation.all, List.foldl_cons, List.foldl_nil]
  norm_num

/-- **Expectancy refuted at the voice manipulation.** Thresholding the
    no-pronoun next-mention rates (Table 7, passive) gives the by-phrase
    referent a `.high` bias and the passive subject a `.low` bias, so the
    expectancy hypothesis — encoded in the substrate as
    `Discourse.NextMentionBias.predictedForm` — predicts the by-phrase
    referent surfaces in the *more reduced* form. The observed
    pronominalization rates (Table 9) run the other way: 23% for the
    by-phrase vs. 87% for the subject. Production tracks topichood
    (`topichood_monotone`), not next-mention bias. -/
theorem expectancy_reversed_under_voice :
    (biasOfRate nmPassiveNoPron).predictedForm.rank >
      (biasOfRate (100 - nmPassiveNoPron)).predictedForm.rank ∧
    pronPassiveNonSubj < pronPassiveSubj := by
  refine ⟨?_, by norm_num [pronPassiveNonSubj, pronPassiveSubj]⟩
  norm_num [biasOfRate, nmPassiveNoPron, Discourse.NextMentionBias.predictedForm,
    Discourse.AccessibilityLevel.rank]

/-! ### Coherence–referent bridge -/

/-- The two Goal-biased CRs (Occasion, Result) both focus on what happens *after*
    the prior event; for transfer verbs the endpoint is the Goal. -/
theorem goal_biased_crs_are_endpoint_focused :
    crOccasion.cr.toClass = .contiguity ∧
    crResult.cr.toClass = .causeEffect ∧
    crOccasion.sourceGivenCR < 50 ∧
    crResult.sourceGivenCR < 50 :=
  ⟨rfl, rfl, by norm_num [crOccasion], by norm_num [crResult]⟩

/-- Explanation is Source-biased and selects for causes (backward causal). For
    transfer verbs the Source is the cause; for IC verbs the stimulus is — the
    bridge to IC bias studies. -/
theorem explanation_source_and_backward :
    crExplanation.cr.selectsCause ∧
    crExplanation.sourceGivenCR > 50 := ⟨rfl, by norm_num [crExplanation]⟩

/-- The contiguity class does not uniformly predict bias: Occasion (18% Source)
    and Elaboration (98% Source) are both contiguity relations with opposite
    biases. Occasion focuses on the end state (Goal); Elaboration redescribes the
    same event (Source). Bias is set by the relation, not the class. -/
theorem contiguity_class_splits :
    crOccasion.cr.toClass = crElaboration.cr.toClass ∧
    crOccasion.sourceGivenCR < 50 ∧
    crElaboration.sourceGivenCR > 50 :=
  ⟨rfl, by norm_num [crOccasion], by norm_num [crElaboration]⟩

/-! ### Centering substrate connection

[kehler-rohde-2013] is the Bayesian–Centering reconciliation paper, so this
section grounds the file's `topichood`/`bayesianPrediction` apparatus in the
`Discourse/Centering/` substrate (`cb`, `cp`, `CbPronominalized`). Under the standard
grammatical-role Cf ranking (`SUBJECT > OBJECT > OTHER`, [kameyama-1986]), the CB
is invariant under voice — both `(Amanda, SUBJ) (Brittany, OBJ)` and
`(Amanda, SUBJ) (Brittany, OTHER-by-phrase)` make Amanda the most-preferred Cf —
yet `topichood` distinguishes them (passive subject `.strong`, active subject
`.default_`). The voice-induced pronominalization gradient (87% vs. 62%) lives in
the topichood signal, not the CB signal. -/

section CenteringBridge

open Discourse.Centering

/-- Two referents in the toy KR2013 example: Amanda (subject across voice
    manipulations) and Brittany (object/by-phrase). -/
def amanda : Nat := 1
def brittany : Nat := 2

/-- Prior "Amanda V'd Brittany": Amanda SUBJ, Brittany OBJ. Under Kameyama's role
    ranking the forward-looking centers are `[Amanda, Brittany]` with Amanda Cp. -/
def prevAmandaActive : Utterance Nat GrammaticalRole :=
  { realizations := [⟨amanda, .subject, false⟩, ⟨brittany, .object, false⟩] }

/-- Active continuation "She V'd her" — Amanda still SUBJ, both pronouns. -/
def curActive : Utterance Nat GrammaticalRole :=
  { realizations := [⟨amanda, .subject, true⟩, ⟨brittany, .object, true⟩] }

/-- Passive continuation "Amanda was V'd by Brittany" — Amanda promoted to SUBJ by
    the marked passive; Brittany now in the by-phrase (`OTHER`). The proposition is
    identical; only the construction differs. -/
def curPassive : Utterance Nat GrammaticalRole :=
  { realizations := [⟨amanda, .subject, true⟩, ⟨brittany, .other, false⟩] }

/-- Cp of the prior utterance is Amanda (SUBJ outranks OBJ). -/
theorem cp_prev_is_amanda :
    prevAmandaActive.cp = some amanda := by decide

/-- CB is invariant under voice: both continuations have CB = Amanda, since Amanda
    is in `prev.cf` and realized in both, and the grammatical-role ranker cannot
    see voice — both subjects rank equally as `.subject`. -/
theorem cb_invariant_under_voice :
    cb prevAmandaActive curActive = cb prevAmandaActive curPassive := by
  decide

/-- Both voice variants have CB = Amanda specifically. -/
theorem cb_is_amanda_in_both_voices :
    cb prevAmandaActive curActive = some amanda ∧
    cb prevAmandaActive curPassive = some amanda := by decide

/-- KR2013's topichood is voice-sensitive: the same subject-position Amanda is
    `.strong` under passive marking but `.default_` under active — the gradient
    driving the 87% vs. 62% pronominalization difference (Table 9). -/
theorem topichood_distinguishes_voice :
    topichood .Pass true ≠ topichood .Act true := by decide

/-- The dissociation: Centering's CB and KR2013's topichood diverge on the voice
    manipulation. CB is the same in both (Amanda); topichood differs (`.strong`
    vs. `.default_`). The 25-pp pronominalization gap (Table 9) lives in the
    topichood signal, not the CB signal — "P(pronoun | referent) tracks
    topichood, not subjecthood." -/
theorem cb_topichood_dissociation_under_voice :
    cb prevAmandaActive curActive = cb prevAmandaActive curPassive ∧
    topichood .Pass true ≠ topichood .Act true :=
  ⟨cb_invariant_under_voice, topichood_distinguishes_voice⟩

/-- Rule 1 (Gordon) is satisfied in both voice variants — both Amanda-realizations
    are pronominal — so the substrate Rule 1 constraint is voice-insensitive too.
    KR2013's contribution is the gradient it averages over: among Rule 1-satisfying
    utterances, passive-subject ones pronominalize 87% of the time vs. 62% for
    active (Table 9). -/
theorem rule1_gordon_satisfied_both_voices :
    CbPronominalized prevAmandaActive curActive ∧
    CbPronominalized prevAmandaActive curPassive := by decide

/-- Centering as the qualitative skeleton of KR2013's likelihood: where
    `CbPronominalized` says "the CB should be pronominalized" (yes/no), the likelihood
    `P(pronoun | referent)` says "at a rate proportional to topichood" (gradient).
    The 87% / 62% / ~24% rates (Table 9) monotonically track the
    `.strong` / `.default_` / `.low` levels (`topichood_monotone`). -/
theorem topichood_rates_monotone_in_table9 :
    pronPassiveSubj > pronActiveSubj ∧
    pronActiveSubj > pronActiveNonSubj := topichood_monotone

end CenteringBridge

end KehlerRohde2013
