import Linglib.Theories.Semantics.Questions.DeclarativeQuestions
import Linglib.Fragments.Swedish.QuestionParticles
import Linglib.Fragments.German.QuestionParticles
import Linglib.Fragments.German.PolarityMarking

/-!
# Seeliger & Repp (2018)
@cite{seeliger-repp-2018}

Biased declarative questions in Swedish and German: Negation meets
modal particles (*väl* and *doch wohl*).

## Key Contributions

1. Distinguishes **declarative questions** (DQs) from **rejecting questions**
   (RQs) — both have declarative syntax but differ in bias profile
2. Applies @cite{sudo-2013}'s two-dimensional bias scheme (evidential ×
   epistemic) to classify four question types: PDQ, NDQ, PRQ, NRQ
3. Shows that the negation in negative RQs is **non-propositional** — it
   denotes the illocutionary modifier FALSUM, not propositional negation
4. Proposes REJECTQ as the illocutionary operator for RQs

## Cross-Linguistic Findings

**German**: RQs obligatorily contain *doch wohl* — the combination is
non-compositional. *doch wohl* enters syntactic Agree with REJECTQ at
ForceP. Without *doch wohl*, a German declarative cannot be a RQ.

**Swedish**: RQs are marked by fronted negation, the modal particle *väl*,
or both. Unlike German, Swedish has multiple formal strategies for marking
RQs, and no single marker is obligatory (though some morpho-syntactic cue
is required). *väl* in positive declaratives creates PDQs; combined with
negation, it creates NRQs.

## Experimental Evidence

@cite{seeliger-repp-2018} SS 5.4: acceptability judgment study (24 native
Swedish speakers) testing negative declaratives with fronted vs. low
negation, with and without *väl*, in NRQ contexts. Results:
- Main effect of MODAL PARTICLE: *väl* raises acceptability
- Interaction: *väl* effect only reliable with low negation (fronted
  negation already highly acceptable without *väl*)
- Supports the claim that fronted negation + *väl* marks NRQs

## This Module

This study file connects:
- The bias profile typology (`DeclarativeQuestions.lean`)
- Swedish *väl* (`Fragments.Swedish.QuestionParticles`)
- German *doch wohl* (`Fragments.German.QuestionParticles`)
- German polarity-reversal *doch* (`Fragments.German.PolarityMarking`)

We verify that the Fragment entries' bias requirements are consistent
with the bias profiles of the question types they mark, and that
RQ profiles derive from the REJECTQ operator.
-/

namespace Phenomena.Questions.Studies.SeeligerRepp2018

open Semantics.Questions.DeclarativeQuestions
open Fragments.Swedish.QuestionParticles
open Fragments.German.QuestionParticles
open Fragments.German.PolarityMarking (dochPreUtterance)

-- ============================================================================
-- S 1: Swedish val marks DQs, not assertions
-- ============================================================================

/-- Swedish *väl* is question-inducing — declaratives with *väl* are
    questions, not assertions (@cite{seeliger-repp-2018} SS 5.2). -/
theorem val_creates_questions :
    Fragments.Swedish.QuestionParticles.val.questionInducing = true ∧
    Fragments.Swedish.QuestionParticles.val.declOk = false := ⟨rfl, rfl⟩

/-- Swedish *väl* requires evidential bias — it is felicitous only in
    contexts with contextual evidence for the proposition, matching the
    evidential bias of PDQs and NRQs. -/
theorem val_requires_evidence :
    Fragments.Swedish.QuestionParticles.val.requiresEvidentialBias = true := rfl

/-- Swedish *väl* signals epistemic uncertainty — the speaker suspects
    p is true but is not certain. This corresponds to the [-positive]
    epistemic bias of PDQs (speaker did not already assume p). -/
theorem val_signals_uncertainty :
    Fragments.Swedish.QuestionParticles.val.signalsEpistemicUncertainty = true := rfl

-- ============================================================================
-- S 2: German doch wohl marks RQs via REJECTQ
-- ============================================================================

/-- German *doch wohl* requires both bias dimensions to be active,
    consistent with the fact that RQs have both evidential and epistemic
    presuppositions in the REJECTQ definition (eq. 40). Both presuppositions
    must be satisfied for REJECTQ to be felicitous. -/
theorem dochWohl_matches_rejectQ :
    Fragments.German.QuestionParticles.dochWohl.requiresEvidentialBias = true ∧
    Fragments.German.QuestionParticles.dochWohl.requiresEpistemicBias = true := ⟨rfl, rfl⟩

/-- *doch wohl* is not usable in assertions — it marks questions. -/
theorem dochWohl_not_assertion :
    Fragments.German.QuestionParticles.dochWohl.declOk = false := rfl

/-- *doch wohl* requires both bias dimensions to be "plus" (active bias),
    matching the derived RQ property that RQ epistemic bias is always active.
    This connects the Fragment entry to the theory-level theorem
    `rq_epistemic_is_plus`. -/
theorem dochWohl_both_biases_active :
    dochWohl.requiresEvidentialBias = true ∧
    dochWohl.requiresEpistemicBias = true ∧
    DeclQuestionType.PRQ.biasProfile.epistemic.isPlus = true ∧
    DeclQuestionType.NRQ.biasProfile.epistemic.isPlus = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- S 3: Cross-linguistic comparison
-- ============================================================================

/-- Both Swedish *väl* and German *doch wohl* require evidential bias.
    This reflects the shared property that both languages require
    contextual evidence for DQs/RQs. -/
theorem both_require_evidential :
    Fragments.Swedish.QuestionParticles.val.requiresEvidentialBias =
    Fragments.German.QuestionParticles.dochWohl.requiresEvidentialBias := rfl

/-- German *doch wohl* additionally requires epistemic bias, while
    Swedish *väl* signals epistemic *uncertainty* — a weaker condition.
    This corresponds to the difference between RQs (epistemic commitment)
    and DQs (epistemic non-commitment): *doch wohl* marks RQs (plus
    epistemic), *väl* marks DQs (minus epistemic). -/
theorem german_stricter_epistemic :
    Fragments.German.QuestionParticles.dochWohl.requiresEpistemicBias = true ∧
    Fragments.Swedish.QuestionParticles.val.signalsEpistemicUncertainty = true := ⟨rfl, rfl⟩

/-- German *denn* (flavoring particle) differs from *doch wohl* (RQ marker):
    *denn* highlights contextual evidence without requiring epistemic
    commitment. *doch wohl* requires both. -/
theorem denn_vs_dochWohl :
    Fragments.German.QuestionParticles.denn.requiresEpistemicBias = false ∧
    Fragments.German.QuestionParticles.dochWohl.requiresEpistemicBias = true := ⟨rfl, rfl⟩

-- ============================================================================
-- S 4: RQ profiles derived from REJECTQ
-- ============================================================================

/-- PRQ bias profile is derived from VERUM via REJECTQ — not independently
    stipulated. This is a key architectural property: the bias profile
    follows from the IM choice in eq. 40. -/
theorem prq_from_verum :
    DeclQuestionType.PRQ.biasProfile = rejectQBiasProfile .verum := rfl

/-- NRQ bias profile is derived from FALSUM via REJECTQ. -/
theorem nrq_from_falsum :
    DeclQuestionType.NRQ.biasProfile = rejectQBiasProfile .falsum := rfl

/-- The defining property of RQs: evidential and epistemic biases are
    for *opposite* polarities. The speaker sees evidence against what
    s/he previously assumed — hence "rejecting." This follows from
    VERUM and FALSUM producing opposite bias directions. -/
theorem rq_opposite_polarities :
    -- PRQ (VERUM): evidence for not-p, assumed p
    (DeclQuestionType.PRQ.biasProfile.evidential = .plusNeg ∧
     DeclQuestionType.PRQ.biasProfile.epistemic = .plusPos) ∧
    -- NRQ (FALSUM): evidence for p, assumed not-p
    (DeclQuestionType.NRQ.biasProfile.evidential = .plusPos ∧
     DeclQuestionType.NRQ.biasProfile.epistemic = .plusNeg) := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- NRQ ⊂ PDQ: wherever a NRQ can be used, a PDQ could also be used
    (both require +positive evidential bias), but NRQs are more restricted
    (they additionally require the speaker to have assumed ¬p).
    @cite{seeliger-repp-2018}: "a NRQ is used in a subset of the
    situations where a PDQ can be used." -/
theorem nrq_subset_of_pdq :
    DeclQuestionType.PDQ.biasProfile.evidential =
    DeclQuestionType.NRQ.biasProfile.evidential ∧
    DeclQuestionType.PDQ.biasProfile.epistemic ≠
    DeclQuestionType.NRQ.biasProfile.epistemic := ⟨rfl, by decide⟩

/-- PRQ ⊂ NDQ: both require +negative evidential bias, but PRQs
    additionally require the speaker to have assumed p. -/
theorem prq_subset_of_ndq :
    DeclQuestionType.NDQ.biasProfile.evidential =
    DeclQuestionType.PRQ.biasProfile.evidential ∧
    DeclQuestionType.NDQ.biasProfile.epistemic ≠
    DeclQuestionType.PRQ.biasProfile.epistemic := ⟨rfl, by decide⟩

-- ============================================================================
-- S 5: Non-compositional doch wohl and the dual role of *doch*
-- ============================================================================

/-- *doch wohl* is a two-particle complex with conventionalized meaning.
    @cite{seeliger-repp-2018} SS 4.2: the combination does not receive
    a compositional interpretation. If it were compositional, *doch wohl*
    should have a reading combining conflict (doch) + reportativity (wohl),
    but this reading is unavailable in RQs. -/
theorem dochWohl_is_complex :
    Fragments.German.QuestionParticles.dochWohl.form = "doch wohl" := rfl

/-- The *doch* in *doch wohl* has a different meaning from polarity-
    reversal *doch* (as in `Fragments.German.PolarityMarking.dochPreUtterance`).
    In RQs, *doch* has a "conflict" meaning — it signals surprise or
    realization — rather than the "reminding" function of assertive *doch*. -/
theorem dochWohl_is_question_marker :
    Fragments.German.QuestionParticles.dochWohl.declOk = false := rfl

/-- German *doch* is formally ambiguous between two distinct roles:
    1. **Polarity-reversal *doch***: pre-utterance correction particle
       that contradicts a negative antecedent (@cite{holmberg-2016})
    2. **RQ-marking *doch***: part of the *doch wohl* complex that
       enters Agree with REJECTQ at ForceP (@cite{seeliger-repp-2018})

    The two share the surface form "doch" but differ in:
    - Syntactic position: polarity *doch* is pre-utterance;
      RQ *doch wohl* is in the middle field
    - Function: polarity *doch* reverses polarity;
      RQ *doch* signals conflict between evidence and prior belief
    - Obligatoriness: polarity *doch* is optional (Verum focus available);
      RQ *doch wohl* is obligatory for German RQs -/
theorem doch_dual_role :
    -- The polarity *doch* is a correction particle (not sentence-internal)
    dochPreUtterance.strategy = .polarityReversal ∧
    dochPreUtterance.correctionOk = true ∧
    dochPreUtterance.sentenceInternal = false ∧
    -- The RQ *doch wohl* is a question marker (not usable in assertions)
    dochWohl.declOk = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- S 6: Bridge to Romero's bias framework
-- ============================================================================

/-- NRQ evidential bias maps to Romero's "evidence for p" — the same
    contextual evidence configuration that licenses HiNQs in
    @cite{romero-2024}. -/
theorem nrq_evidential_maps_to_forP :
    evidentialToContextualEvidence DeclQuestionType.NRQ.biasProfile.evidential =
    some .forP := rfl

/-- RQ bias values all have Romero counterparts (they are all "plus" values);
    DQ epistemic "minus" values do not — this is precisely where @cite{sudo-2013}'s
    system (as extended by @cite{seeliger-repp-2018}) goes beyond @cite{romero-2024}. -/
theorem rq_vs_dq_romero_coverage :
    (evidentialToContextualEvidence DeclQuestionType.PRQ.biasProfile.evidential).isSome = true ∧
    (epistemicToOriginalBias DeclQuestionType.PRQ.biasProfile.epistemic).isSome = true ∧
    (epistemicToOriginalBias DeclQuestionType.PDQ.biasProfile.epistemic).isNone = true := ⟨rfl, rfl, rfl⟩

end Phenomena.Questions.Studies.SeeligerRepp2018
