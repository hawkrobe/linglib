import Linglib.Core.Discourse.Coherence
import Linglib.Core.Lexical.UD
import Linglib.Theories.Discourse.Centering.Rule1
import Linglib.Theories.Discourse.Centering.Instances.GrammaticalRole

/-!
# @cite{kehler-rohde-2013}
@cite{hobbs-1979} @cite{kehler-2002}

A Probabilistic Reconciliation of Coherence-Driven and Centering-Driven
Theories of Pronoun Interpretation. *Theoretical Linguistics* 39(1-2), 1–37.

## Core Argument

Two theories make seemingly irreconcilable claims about pronoun interpretation.
@cite{hobbs-1979}: it is a by-product of coherence establishment; grammatical
form is irrelevant. Centering (Grosz, Joshi & Weinstein 1995): it is driven by
information structure and grammatical roles; world knowledge is irrelevant.

The reconciliation is a Bayesian decomposition (eq. 13):

    P(referent | pronoun) ∝ P(pronoun | referent) × P(referent)

The two terms have different conditioning:

- **P(referent)**: coherence-driven next-mention bias, computed via eq. (9):
  `P(referent) = Σ_CR P(CR) × P(referent | CR)`
- **P(pronoun | referent)**: production/form bias, driven by topichood
  (centering's contribution)

Five experiments with transfer-of-possession verbs and IC verbs confirm
that these two components are empirically dissociable.

## Key Findings

| # | Finding | Section |
|---|---------|---------|
| 1 | Imperfective → more Source interpretations than perfective | §3 |
| 2 | Coherence relations strongly condition next-mention bias | §4 |
| 3 | Shifting P(CR) via instructions shifts interpretation | §5 |
| 4 | P(referent\|CR) stable across conditions | §6 |
| 5 | Pronoun prompt shifts CR distribution bidirectionally | §7 |
| 6 | Voice affects next-mention but not pronominalization per position | §8 |
| 7 | Passive subject → more pronominalization than active subject | §8 |
| 8 | Bayesian predictions match actual interpretation biases | §8 |
| 9 | Contiguity class splits: Occasion → Goal, Elaboration → Source | §9 |

## Independence Hypothesis

P(pronoun | referent) is conditioned by topichood/subjecthood, while
P(referent) is conditioned by coherence relations. These two components
are independent: coherence-driven semantic biases affect next-mention
but NOT pronominalization rate.
-/

set_option autoImplicit false

namespace KehlerRohde2013

open Core.Discourse.Coherence
open UD (Voice)

-- ════════════════════════════════════════════════════
-- § 1. Experimental Design
-- ════════════════════════════════════════════════════

/-- Prompt type in passage completion experiments. -/
inductive PromptType where
  | pronoun      -- "She ___"
  | noPronoun    -- "___" (free completion)
  deriving DecidableEq, Repr

/-- Instruction condition (transfer-of-possession exps). -/
inductive InstructionCond where
  | whatNext   -- "What happened next?"
  | why        -- "Why?"
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. The Bayesian Model
-- ════════════════════════════════════════════════════

/-- Eq. (9): coherence-marginalized next-mention bias.

    P(referent) = Σ_CR P(CR) × P(referent | CR)

    The prior probability of a referent being mentioned next is a mixture
    of CR-specific biases weighted by the prior over coherence relations.
    This is the coherence-driven "top-down" component. -/
structure NextMentionModel where
  /-- P(CR): prior probability of coherence relation (%) -/
  pCR : CoherenceRelation → Nat
  /-- P(referent = Source | CR): Source bias given CR (%) -/
  pSourceGivenCR : CoherenceRelation → Nat

/-- Topichood level, determined by grammatical construction.

    Passive subjects signal stronger topichood than active subjects:
    using a marked construction to place an entity in subject position
    is a stronger indicator that the speaker treats it as the sentence
    topic (@cite{davison-1984}). This is the centering-driven "bottom-up"
    component of the model.

    The P(pronoun | referent) term in eq. (13) tracks this level, not
    grammatical role per se. -/
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

-- ════════════════════════════════════════════════════
-- § 3. Aspect Manipulation (Table 1)
-- ════════════════════════════════════════════════════

/-- Table 1: Source interpretation rate by aspect.
    Imperfective focuses on ongoing event (Source still central);
    perfective focuses on end state (Goal = endpoint of transfer). -/
def sourceInterp_perfective : Nat := 57
def sourceInterp_imperfective : Nat := 80

/-- Imperfective yields more Source interpretations than perfective. -/
theorem imperfective_more_source :
    sourceInterp_imperfective > sourceInterp_perfective := by decide

-- ════════════════════════════════════════════════════
-- § 4. Coherence Relation Analysis (Table 2)
-- ════════════════════════════════════════════════════

/-- Coherence relation frequency and bias data from Table 2
    (perfective condition, transfer-of-possession verbs).
    "Violated Expectation" in the paper = `CoherenceRelation.contrast`. -/
structure CRDatum where
  cr : CoherenceRelation
  freqPct : Nat           -- frequency of occurrence (%)
  sourceGivenCR : Nat     -- P(Source interpretation | CR) (%)
  deriving Repr

def cr_occasion     : CRDatum := ⟨.occasion,      38, 18⟩
def cr_elaboration  : CRDatum := ⟨.elaboration,   28, 98⟩
def cr_explanation  : CRDatum := ⟨.explanation,    18, 80⟩
def cr_violatedExp  : CRDatum := ⟨.contrast,       8, 76⟩
def cr_result       : CRDatum := ⟨.result,          6,  8⟩

/-- Occasion and Result are Goal-biased (Source < 50%). -/
theorem goal_biased_crs :
    cr_occasion.sourceGivenCR < 50 ∧ cr_result.sourceGivenCR < 50 := by
  exact ⟨by decide, by decide⟩

/-- Elaboration, Explanation, and Violated Expectation are Source-biased. -/
theorem source_biased_crs :
    cr_elaboration.sourceGivenCR > 50 ∧
    cr_explanation.sourceGivenCR > 50 ∧
    cr_violatedExp.sourceGivenCR > 50 := by
  exact ⟨by decide, by decide, by decide⟩

/-- The overall ~57/43 Source/Goal split masks strong CR-conditioned
    biases. Occasion is most common (.38) and Goal-biased (.18 Source);
    Elaboration is second (.28) and strongly Source-biased (.98). -/
theorem biases_masked_by_mixture :
    cr_occasion.sourceGivenCR < 50 ∧ cr_elaboration.sourceGivenCR > 50 ∧
    cr_occasion.freqPct > cr_elaboration.freqPct := by
  exact ⟨by decide, by decide, by decide⟩

/-- Instantiate the perfective-condition next-mention model with
    Table 2 data. Downstream study files can reference these CR biases. -/
def perfective_model : NextMentionModel where
  pCR := fun
    | .occasion    => 38
    | .elaboration => 28
    | .explanation => 18
    | .contrast    =>  8
    | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
    | .result      =>  6
    | .parallel    =>  2
  pSourceGivenCR := fun
    | .occasion    => 18
    | .elaboration => 98
    | .explanation => 80
    | .contrast    => 76
    | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
    | .result      =>  8
    | .parallel    => 50

-- ════════════════════════════════════════════════════
-- § 5. Instruction Manipulation: P(CR) Shift (Tables 3, 5)
-- ════════════════════════════════════════════════════

/-- Table 3: "What happened next?" → Occasion-dominated;
    "Why?" → Explanation-dominated. Instructions shift P(CR) without
    changing the stimuli. -/
def whatNext_occasion_pct    : Nat := 71
def whatNext_explanation_pct : Nat :=  1
def why_occasion_pct         : Nat :=  1
def why_explanation_pct      : Nat := 91

theorem instructions_shift_pCR :
    whatNext_occasion_pct > why_occasion_pct ∧
    why_explanation_pct > whatNext_explanation_pct := by
  exact ⟨by decide, by decide⟩

/-- Table 5: Source interpretation by instruction condition (perfective).
    Shifting P(CR) shifts P(referent), as predicted by eq. (9). -/
def whatNext_sourcePct : Nat := 34
def why_sourcePct      : Nat := 82

theorem instructions_shift_interpretation :
    why_sourcePct > whatNext_sourcePct := by decide

/-- The instruction effect is 48 pp on identical stimuli.
    No morphosyntactic heuristic can account for this. -/
theorem instruction_effect_magnitude :
    why_sourcePct - whatNext_sourcePct > 40 := by decide

-- ════════════════════════════════════════════════════
-- § 6. Bias Stability: P(ref|CR) Invariance (Table 4)
-- ════════════════════════════════════════════════════

/-- Table 4: P(Source | CR) is stable across the original experiment
    and the instruction manipulation, supporting the structural claim
    that CR-conditioned biases are properties of the coherence relation
    itself, not the experimental context. -/
structure StabilityDatum where
  cr : CoherenceRelation
  originalPct : Nat
  instructionPct : Nat
  deriving Repr

def stab_elaboration : StabilityDatum := ⟨.elaboration, 98, 100⟩
def stab_explanation : StabilityDatum := ⟨.explanation,  80,  82⟩
def stab_violatedExp : StabilityDatum := ⟨.contrast,     76,  74⟩
def stab_occasion    : StabilityDatum := ⟨.occasion,     18,  27⟩
def stab_result      : StabilityDatum := ⟨.result,        8,   9⟩

/-- Bias direction (above/below 50%) is preserved for all five CRs
    across conditions. P(CR) can shift independently of P(ref|CR). -/
theorem bias_direction_stable :
    (stab_elaboration.originalPct > 50 ∧ stab_elaboration.instructionPct > 50) ∧
    (stab_explanation.originalPct > 50 ∧ stab_explanation.instructionPct > 50) ∧
    (stab_occasion.originalPct < 50 ∧ stab_occasion.instructionPct < 50) ∧
    (stab_result.originalPct < 50 ∧ stab_result.instructionPct < 50) := by
  refine ⟨⟨by decide, by decide⟩,
          ⟨by decide, by decide⟩,
          ⟨by decide, by decide⟩,
          ⟨by decide, by decide⟩⟩

-- ════════════════════════════════════════════════════
-- § 7. Bidirectionality: Pronoun → Coherence (Table 6)
-- ════════════════════════════════════════════════════

/-- Table 6: CR distribution by prompt type. The mere presence of an
    ambiguous pronoun shifts coherence expectations toward Source-biased
    relations. This bidirectionality — coreference affects coherence,
    not just vice versa — is predicted by Bayes (eq. 12) but not by
    Hobbs (pronouns are inert free variables) or Centering (does not
    model coherence). -/
structure PromptCRDatum where
  prompt : PromptType
  cr : CoherenceRelation
  freqPct : Nat
  deriving Repr

def np_elaboration  : PromptCRDatum := ⟨.noPronoun, .elaboration,  6⟩
def np_explanation  : PromptCRDatum := ⟨.noPronoun, .explanation, 20⟩
def np_occasion     : PromptCRDatum := ⟨.noPronoun, .occasion,    36⟩
def np_result       : PromptCRDatum := ⟨.noPronoun, .result,      13⟩
def np_violatedExp  : PromptCRDatum := ⟨.noPronoun, .contrast,    18⟩

def pp_elaboration  : PromptCRDatum := ⟨.pronoun, .elaboration, 20⟩
def pp_explanation  : PromptCRDatum := ⟨.pronoun, .explanation, 28⟩
def pp_occasion     : PromptCRDatum := ⟨.pronoun, .occasion,    28⟩
def pp_result       : PromptCRDatum := ⟨.pronoun, .result,       5⟩
def pp_violatedExp  : PromptCRDatum := ⟨.pronoun, .contrast,    14⟩

/-- Pronoun prompt increases Source-biased CRs. -/
theorem pronoun_boosts_source_CRs :
    pp_elaboration.freqPct > np_elaboration.freqPct ∧
    pp_explanation.freqPct > np_explanation.freqPct := by
  exact ⟨by decide, by decide⟩

/-- Pronoun prompt decreases Goal-biased CRs. -/
theorem pronoun_reduces_goal_CRs :
    pp_occasion.freqPct < np_occasion.freqPct ∧
    pp_result.freqPct < np_result.freqPct := by
  exact ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Voice Manipulation: IC Verbs (Tables 7–10)
-- ════════════════════════════════════════════════════

-- Table 7: Proportion of next mentions to the causally-implicated
-- referent. Subject-biased IC verbs (e.g., "Amanda amazed Brittany"):
-- Active: causal referent (Amanda) = subject
-- Passive: causal referent (Amanda) = by-phrase (non-subject)

def nm_active_pron     : Nat := 77
def nm_active_noPron   : Nat := 59
def nm_passive_pron    : Nat := 42
def nm_passive_noPron  : Nat := 76

/-- Voice affects next-mention in pronoun condition: active (.77) vs
    passive (.42). Passivization moves the causally-implicated referent
    out of subject position — same proposition, different bias. -/
theorem voice_affects_nextMention :
    nm_active_pron > nm_passive_pron := by decide

/-- In the no-pronoun condition the pattern reverses: passive (.76) >
    active (.59). By-phrases are optional in English, so their inclusion
    signals the referent will be re-mentioned. -/
theorem noPronoun_pattern_reverses :
    nm_passive_noPron > nm_active_noPron := by decide

-- Table 8: Proportion of Explanation relations
def expl_active_pron     : Nat := 75
def expl_active_noPron   : Nat := 60
def expl_passive_pron    : Nat := 52
def expl_passive_noPron  : Nat := 72

/-- Voice affects coherence in pronoun condition: active produces more
    Explanations than passive. Since propositions are identical, this is
    mediated by the shift in pronominal reference — demonstrating
    bidirectional coherence–coreference dependency. -/
theorem voice_affects_coherence :
    expl_active_pron > expl_passive_pron := by decide

-- Table 9: Pronominalization rates by voice × surface position
def pron_active_subj     : Nat := 62
def pron_active_nonSubj  : Nat := 24
def pron_passive_subj    : Nat := 87
def pron_passive_nonSubj : Nat := 23

/-- Central topichood prediction: passive subjects are pronominalized
    more than active subjects (87% vs 62%).

    This is NOT explicable by grammatical role alone — both are subjects.
    It reflects the stronger topichood signal of the passive: using a
    marked syntactic form to place an entity in subject position is a
    stronger indicator of topic status. This is the key evidence that
    P(pronoun | referent) tracks TOPICHOOD, not subjecthood. -/
theorem passive_subj_more_pronominalized :
    pron_passive_subj > pron_active_subj := by decide

/-- Non-subject pronominalization is invariant across voice (24% vs 23%).
    At the same topichood level (low), the voice manipulation — which
    changes coherence expectations dramatically — has no effect on
    pronominalization rate. This is the Independence Hypothesis in action:
    P(pronoun | referent) does not depend on coherence-driven factors. -/
theorem nonSubj_pron_invariant :
    pron_active_nonSubj - pron_passive_nonSubj ≤ 1 := by decide

/-- Subjects are pronominalized more than non-subjects in both voices.
    This subject advantage is the centering-derived component. -/
theorem subject_advantage_both_voices :
    pron_active_subj > pron_active_nonSubj ∧
    pron_passive_subj > pron_passive_nonSubj := by
  exact ⟨by decide, by decide⟩

/-- Topichood monotonically predicts pronominalization:
    strong (passive subject, 87%) > default (active subject, 62%)
    > low (non-subject, ~24%). -/
theorem topichood_monotone :
    pron_passive_subj > pron_active_subj ∧
    pron_active_subj > pron_active_nonSubj := by
  exact ⟨by decide, by decide⟩

-- Table 10: Predicted vs actual interpretation biases.
-- The Bayesian model estimates P(referent) from no-pronoun data and
-- P(pronoun|referent) from pronominalization rates, then predicts
-- P(referent|pronoun) via eq. (13).

def predicted_active_subj  : Nat := 81
def actual_active_subj     : Nat := 74
def predicted_passive_subj : Nat := 59
def actual_passive_subj    : Nat := 60

/-- Bayesian predictions are directionally correct:
    active > passive in both predicted and actual biases. -/
theorem bayesian_directionally_correct :
    predicted_active_subj > predicted_passive_subj ∧
    actual_active_subj > actual_passive_subj := by
  exact ⟨by decide, by decide⟩

/-- The passive prediction is highly accurate (59% vs 60%). -/
theorem passive_prediction_accurate :
    actual_passive_subj - predicted_passive_subj ≤ 1 := by decide

-- ════════════════════════════════════════════════════
-- § 9. Eq. (9): Mixture Derivation
-- ════════════════════════════════════════════════════

/-- Compute the coherence-marginalized Source bias from a NextMentionModel.
    This IS equation (9): P(Source) = Σ_CR P(CR) × P(Source | CR).
    Result is in basis points (×10000); divide by 100 for percentage. -/
def NextMentionModel.sourceBasisPts (m : NextMentionModel) : Nat :=
  let crs : List CoherenceRelation :=
    [.occasion, .elaboration, .explanation, .contrast, .correction, .result, .parallel]
  crs.foldl (λ acc cr => acc + m.pCR cr * m.pSourceGivenCR cr) 0

/-- The instruction manipulation models from Tables 3–4.
    Both share the SAME P(Source|CR) — the CR-conditioned biases from
    Table 4 (instruction column). They differ ONLY in P(CR). -/
private def sharedBias : CoherenceRelation → Nat
  | .occasion    => 27
  | .elaboration => 100
  | .explanation => 82
  | .contrast    => 74
  | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
  | .result      =>  9
  | .parallel    => 50

def whatNext_model : NextMentionModel where
  pCR := fun
    | .occasion    => 71
    | .explanation =>  1
    | .elaboration =>  5
    | .contrast    =>  8
    | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
    | .result      =>  5
    | .parallel    => 10
  pSourceGivenCR := sharedBias

def why_model : NextMentionModel where
  pCR := fun
    | .occasion    =>  1
    | .explanation => 91
    | .elaboration =>  8
    | .contrast    =>  1
    | .correction  =>  0  -- not in K&R 2013 coding scheme; 0% weight in mixture
    | .result      =>  0
    | .parallel    =>  0
  pSourceGivenCR := sharedBias

/-- **Structural invariant**: the two instruction models share the same
    CR-conditioned biases. The instruction manipulation changes P(CR)
    while holding P(ref|CR) constant. This is the structural content
    of Table 4. -/
theorem instruction_models_share_bias :
    whatNext_model.pSourceGivenCR = why_model.pSourceGivenCR := rfl

/-- **Eq. (9) derivation**: the "Why?" mixture exceeds the "What next?"
    mixture. This is DERIVED from the model, not read off Table 5.
    The proof computes:
      Why:       1×27 + 91×82 + 8×100 + 1×74 + 0×9 + 0×50 = 8363
      What next: 71×27 + 1×82 + 5×100 + 8×74 + 5×9 + 10×50 = 3636
    and verifies 8363 > 3636. The direction follows from Explanation
    (Source-biased at 82%) dominating the Why mixture at 91%. -/
theorem eq9_why_exceeds_whatNext :
    why_model.sourceBasisPts > whatNext_model.sourceBasisPts := by
  decide

/-- The computed mixtures are consistent with Table 5: Why → ~84%
    Source, What-next → ~36% Source (vs observed 82% and 34%). The
    small discrepancy is from integer rounding and the "Other" CR
    category. -/
theorem eq9_mixtures_approximate_table5 :
    why_model.sourceBasisPts / 100 > 80 ∧
    whatNext_model.sourceBasisPts / 100 < 40 := by
  decide

-- ════════════════════════════════════════════════════
-- § 10. Eq. (13): Bayesian Inversion
-- ════════════════════════════════════════════════════

/-- Compute P(Subject | pronoun) via Bayes' rule (eq. 13).
    Takes P(Subject next-mentioned) from no-pronoun data and
    P(pronoun | position) from pronominalization rates.
    Result is a percentage (0–100). -/
def bayesianPrediction (pSubj pPronSubj pPronNonSubj : Nat) : Nat :=
  let num := pPronSubj * pSubj
  let den := pPronSubj * pSubj + pPronNonSubj * (100 - pSubj)
  if den = 0 then 0 else num * 100 / den

/-- **Eq. (13) derivation**: active voice. From:
    - P(Subject) = 59% (Table 7, no-pronoun, causal ref = subject)
    - P(pronoun | Subject) = 62% (Table 9)
    - P(pronoun | NonSubject) = 24% (Table 9)
    Bayes' rule yields: 62×59 / (62×59 + 24×41) = 3658/4642 ≈ 78%.
    The paper reports 81% (from unrounded data); the direction matches. -/
theorem eq13_active_prediction :
    bayesianPrediction nm_active_noPron pron_active_subj pron_active_nonSubj
    > 50 := by decide

/-- **Eq. (13) derivation**: passive voice. From:
    - P(Subject) = 100 - 76 = 24% (Table 7: 76% mention causal ref,
      who is the NON-subject in passive)
    - P(pronoun | Subject) = 87% (Table 9)
    - P(pronoun | NonSubject) = 23% (Table 9)
    Bayes' rule yields: 87×24 / (87×24 + 23×76) = 2088/3836 ≈ 54%. -/
theorem eq13_passive_prediction :
    bayesianPrediction (100 - nm_passive_noPron) pron_passive_subj
      pron_passive_nonSubj > 50 := by decide

/-- **Central Bayesian prediction**: Bayes' rule correctly derives that
    active > passive for P(Subject | pronoun), even though passive
    subjects are more likely to be pronominalized (87% vs 62%).
    The prior P(Subject) is much lower in passive (24% vs 59%),
    and this dominates. Production bias alone would predict passive >
    active; the Bayesian model correctly reverses this. -/
theorem eq13_active_exceeds_passive :
    bayesianPrediction nm_active_noPron pron_active_subj pron_active_nonSubj >
    bayesianPrediction (100 - nm_passive_noPron) pron_passive_subj
      pron_passive_nonSubj := by
  decide

-- ════════════════════════════════════════════════════
-- § 11. Coherence–Referent Bridge
-- ════════════════════════════════════════════════════

/-- The two Goal-biased CRs (Occasion, Result) both focus on what
    happens AFTER the prior event. For transfer verbs, the endpoint
    is the Goal. -/
theorem goal_biased_crs_are_endpoint_focused :
    cr_occasion.cr.toClass = .contiguity ∧
    cr_result.cr.toClass = .causeEffect ∧
    cr_occasion.sourceGivenCR < 50 ∧
    cr_result.sourceGivenCR < 50 := by
  exact ⟨rfl, rfl, by decide, by decide⟩

/-- Explanation is Source-biased and selects for causes (backward causal).
    For transfer verbs, the Source/initiator is the cause. For IC verbs,
    the stimulus is the cause — this is the bridge to IC bias studies. -/
theorem explanation_source_and_backward :
    cr_explanation.cr.selectsCause = true ∧
    cr_explanation.sourceGivenCR > 50 := ⟨rfl, by decide⟩

/-- Key insight: the contiguity class does NOT uniformly predict bias.
    Occasion (18% Source) and Elaboration (98% Source) are both contiguity
    relations but have opposite biases. Occasion focuses on the END STATE
    (Goal); Elaboration redescribes the SAME EVENT (Source/initiator).
    The bias is determined by the specific relation, not the class. -/
theorem contiguity_class_splits :
    cr_occasion.cr.toClass = cr_elaboration.cr.toClass ∧
    cr_occasion.sourceGivenCR < 50 ∧
    cr_elaboration.sourceGivenCR > 50 := by
  exact ⟨rfl, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 12. Centering Substrate Connection
-- ════════════════════════════════════════════════════

/-! ## Centering's CB and KR2013's topichood are not the same signal.

    K&R 2013 IS the Bayesian-Centering reconciliation paper. To make
    that explicit at the type level, this section grounds the file's
    `topichood`/`bayesianPrediction` apparatus in the
    `Theories/Discourse/Centering/` substrate (`cb`, `cp`, `Rule1Gordon`),
    showing precisely *what Centering does and does not capture* from
    KR2013's empirical landscape.

    The key dissociation (KR2013 §8, Table 9): under the standard
    grammatical-role Cf ranking (`SUBJECT > OBJECT > OTHER`,
    @cite{kameyama-1986}), the CB is **invariant under voice
    manipulation** — both `(Amanda, SUBJ) (Brittany, OBJ)` and
    `(Amanda, SUBJ) (Brittany, OTHER-by-phrase)` make Amanda the
    most-preferred Cf. But KR2013's `topichood` distinguishes the
    two cases: passive subject is `.strong`, active subject is
    `.default_`. This is the formal content of "P(pronoun | referent)
    tracks topichood, not subjecthood" (§8 p. 25).

    The cross-paper claim landed here: **Centering's CB selection is a
    necessary input to KR2013's production model but is not sufficient
    to predict pronominalization rate**. The voice-induced gradient
    that KR2013 measure (87% vs 62%) lives in the topichood signal,
    not in the CB signal.

    **Empirical complement** (post-2013 follow-up): the substrate-level
    dissociation theorem `cb_topichood_dissociation_under_voice` below
    is the structural reason why
    `RosaArnold2017.independence_violated_bridges_to_KR`
    (`Phenomena/Reference/Studies/RosaArnold2017.lean`) finds K&R's
    Independence Hypothesis empirically *violatable*: because
    `cb` cannot detect the voice manipulation, any pronominalization
    asymmetry between active and passive subjects must be carried by a
    signal external to Centering's `cb`/`cp` — Rosa & Arnold's
    experiment provides one such asymmetry as a corpus measurement,
    while §12 here exhibits the substrate-level mechanism. -/

section CenteringBridge

open Discourse.Centering

/-- Two referents in our toy KR2013 example: Amanda (subject across
    voice manipulations) and Brittany (object/by-phrase). -/
def amanda : Nat := 1
def brittany : Nat := 2

/-- Prior utterance "Amanda V'd Brittany": Amanda is SUBJ, Brittany is
    OBJ. Forward-looking centers under Kameyama's role ranking are
    `[Amanda, Brittany]` with Amanda as Cp. -/
def prev_AmandaActive : Utterance Nat GrammaticalRole :=
  { realizations := [⟨amanda, .subject, false⟩, ⟨brittany, .object, false⟩] }

/-- Active continuation "She V'd her" — Amanda still SUBJ, both pronouns. -/
def cur_active : Utterance Nat GrammaticalRole :=
  { realizations := [⟨amanda, .subject, true⟩, ⟨brittany, .object, true⟩] }

/-- Passive continuation "Amanda was V'd by Brittany" — Amanda promoted to
    SUBJ via the marked passive construction; Brittany now in by-phrase
    (`OTHER`). The proposition is identical; only the construction differs. -/
def cur_passive : Utterance Nat GrammaticalRole :=
  { realizations := [⟨amanda, .subject, true⟩, ⟨brittany, .other, false⟩] }

/-- Cp of the prior utterance is Amanda (SUBJ outranks OBJ). -/
theorem cp_prev_is_amanda :
    prev_AmandaActive.cp = some amanda := by decide

/-- **CB is invariant under voice manipulation.** Both the active and
    passive continuations have CB = Amanda, because Amanda is in
    `prev.cf` and is realized in both. The grammatical-role ranker
    cannot see voice — both subjects rank equally as `.subject`. -/
theorem cb_invariant_under_voice :
    cb prev_AmandaActive cur_active = cb prev_AmandaActive cur_passive := by
  decide

/-- Both voice variants have CB = Amanda specifically. -/
theorem cb_is_amanda_in_both_voices :
    cb prev_AmandaActive cur_active = some amanda ∧
    cb prev_AmandaActive cur_passive = some amanda := by
  exact ⟨by decide, by decide⟩

/-- **KR2013's topichood IS voice-sensitive.** The same subject-position
    Amanda gets `.strong` topichood under passive marking but only
    `.default_` under active. This is the gradient that drives the
    87% vs 62% pronominalization rate difference (Table 9). -/
theorem topichood_distinguishes_voice :
    topichood .Pass true ≠ topichood .Act true := by decide

/-- **The dissociation theorem**: Centering's CB and KR2013's topichood
    diverge on the voice manipulation. CB is the same in both cases
    (Amanda); topichood differs (`.strong` vs `.default_`). The 25-pp
    pronominalization gap KR2013 measure (Table 9) lives in the
    topichood signal, not the CB signal — exactly KR2013 §8's
    "P(pronoun | referent) tracks topichood, not subjecthood." -/
theorem cb_topichood_dissociation_under_voice :
    cb prev_AmandaActive cur_active = cb prev_AmandaActive cur_passive ∧
    topichood .Pass true ≠ topichood .Act true :=
  ⟨cb_invariant_under_voice, topichood_distinguishes_voice⟩

/-- **Rule 1 (Gordon) is satisfied in both voice variants** because both
    Amanda-realizations are pronominal. The substrate-level Rule 1
    constraint is voice-insensitive too — it only fires on whether the
    CB *is* a pronoun, not on what construction realized it.

    KR2013's contribution is precisely to expose the gradient that
    Rule 1's Bool-valued check averages over: among the utterances
    that satisfy Rule 1 (Gordon), passive-subject ones use a pronoun
    87% of the time while active-subject ones do so only 62% of the
    time (Table 9). Rule 1 captures the qualitative pattern; the
    Bayesian likelihood `P(pronoun | referent)` captures the
    voice-conditioned production rate. -/
theorem rule1_gordon_satisfied_both_voices :
    Rule1Gordon prev_AmandaActive cur_active ∧
    Rule1Gordon prev_AmandaActive cur_passive := by
  exact ⟨by decide, by decide⟩

/-- **Centering as the qualitative skeleton of KR2013's likelihood.**
    Where Centering's `Rule1Gordon` says "the CB should be
    pronominalized" (Bool), KR2013's likelihood `P(pronoun | referent)`
    says "the CB is pronominalized at a rate proportional to its
    topichood" (gradient). The Centering substrate provides the
    *which referent is the topic* part; KR2013 provide the *how
    strongly* part.

    Numerically: the 87% / 62% / ~24% pronominalization rates from
    Table 9 monotonically track the `.strong` / `.default_` / `.low`
    levels assigned by `topichood`. -/
theorem topichood_rates_monotone_in_table9 :
    pron_passive_subj > pron_active_subj ∧       -- .strong > .default_ : 87 > 62
    pron_active_subj > pron_active_nonSubj := by  -- .default_ > .low   : 62 > 24
  exact ⟨by decide, by decide⟩

end CenteringBridge

end KehlerRohde2013
