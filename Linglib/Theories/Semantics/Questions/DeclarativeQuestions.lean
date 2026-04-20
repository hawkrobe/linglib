import Linglib.Theories.Semantics.Modality.BiasedPQ
import Linglib.Core.Polarity

/-!
# Biased Declarative Questions
@cite{seeliger-repp-2018} @cite{sudo-2013}

Typology of declarative questions (DQs) and rejecting questions (RQs),
following @cite{seeliger-repp-2018}'s analysis of Swedish and German.

## Bias Profiles (@cite{sudo-2013})

Every declarative question type carries a *bias profile*: a pair of
evidential and epistemic bias values. Evidential bias concerns contextual
evidence — what the context makes salient. Epistemic bias concerns the
speaker's prior assumptions — what s/he assumed before asking.

@cite{sudo-2013} proposes three "plus" values for bias: [+positive]
(bias for p), [+negative] (bias for not-p), and [neutral] (no bias).
Evidential bias can also take "minus" values (incompatibility): [-positive]
and [-negative]. @cite{seeliger-repp-2018} extend this by allowing minus
values for epistemic bias as well, to capture that DQ speakers merely
*didn't assume* the proposition (rather than assuming the opposite).

## Four Question Types (@cite{seeliger-repp-2018}, Table 1)

| Type | Denotes | Evidential | Epistemic | Example |
|------|---------|-----------|-----------|---------|
| PDQ  | p       | +positive | -positive | Peter is coming? |
| NDQ  | not-p   | +negative | -negative | Peter isn't coming? |
| PRQ  | p       | +negative | +positive | Surely Peter is coming? |
| NRQ  | not-p   | +positive | +negative | Surely Peter isn't coming? |

DQs and RQs differ in that RQs are "more biased": the speaker had a
specific prior assumption (epistemic bias is [+positive] or [+negative]),
and the contextual evidence *conflicts* with that assumption.

## REJECTQ Operator (@cite{seeliger-repp-2018} SS 6.2, eq. 40)

REJECTQ takes a proposition q and an illocutionary modifier IM
(either FALSUM or VERUM):

  ⟦REJECTQ⟧ = λqλIM: [IM(¬q)]^evid & [IM(q)]^epist. {IM(q), ¬IM(q)}

The two presuppositions (underlined in the paper):
1. **Evidential**: [IM(¬q)]^evid — on an evidential basis, there is
   IM-determined commitment to ¬q
2. **Epistemic**: [IM(q)]^epist — on an epistemic basis, there is
   IM-determined commitment to q

The at-issue content forms a question: {IM(q), ¬IM(q)}.

FALSUM = zero commitment (negation is non-propositional; speaker is
not committed to q). Used in NRQs.
VERUM = full commitment (speaker is sure q should be in CG).
Used in PRQs. In PRQs, Swedish *visst*/*nog* or an evidential version
of VERUM signals direct contextual evidence.

## Cross-Module Connections

- `Semantics.Modality.BiasedPQ`: Romero's PQ bias framework (VERUM, FALSUM,
  OriginalBias, ContextualEvidence)
- `Semantics.Questions.VerumFocus`: detailed VERUM semantics with modal frames
- `Core.Discourse.SpeechActs`: Searle's speech act taxonomy
- `Semantics.Questions.AnsweringSystems`: polar answer typology
-/

namespace Semantics.Questions.DeclarativeQuestions

-- ============================================================================
-- S 1: Bias Values (@cite{sudo-2013}, extended by @cite{seeliger-repp-2018})
-- ============================================================================

/-- Bias value for a single dimension (evidential or epistemic).

    @cite{sudo-2013}'s system distinguishes "plus" values (positive bias
    for p or not-p), "neutral" (no bias), and "minus" values (incompatibility
    with a given bias direction).

    @cite{sudo-2013} originally restricted minus values to evidential bias.
    @cite{seeliger-repp-2018} extend the system by allowing minus values
    for epistemic bias as well — needed to capture the DQ pattern where
    the speaker merely *didn't assume* the proposition ([-positive]) rather
    than actively assuming the opposite ([+negative]). -/
inductive BiasValue where
  /-- [+positive]: bias for p -/
  | plusPos
  /-- [+negative]: bias for not-p -/
  | plusNeg
  /-- [neutral]: no bias -/
  | neutral
  /-- [-positive]: incompatible with bias for p -/
  | minusPos
  /-- [-negative]: incompatible with bias for not-p -/
  | minusNeg
  deriving DecidableEq, Repr

/-- A bias profile bundles evidential and epistemic bias values. -/
structure BiasProfile where
  /-- Evidential bias: what the contextual evidence supports -/
  evidential : BiasValue
  /-- Epistemic bias: what the speaker previously assumed -/
  epistemic : BiasValue
  deriving DecidableEq, Repr

/-- Whether a bias value is a "plus" value (active bias) or not.
    RQs require plus values in both dimensions; DQs have a minus
    value in the epistemic dimension. -/
def BiasValue.IsPlus (b : BiasValue) : Prop :=
  b = .plusPos ∨ b = .plusNeg

instance : DecidablePred BiasValue.IsPlus :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Whether a bias value targets p (positive polarity) or not-p. -/
def BiasValue.targetsPositive : BiasValue → Option Bool
  | .plusPos  => some true
  | .plusNeg  => some false
  | .minusPos => some true   -- incompatibility also has a target
  | .minusNeg => some false
  | .neutral  => none

-- ============================================================================
-- S 2: Declarative Question Types (@cite{seeliger-repp-2018}, Table 1)
-- ============================================================================

/-- The four types of questions with declarative syntax. -/
inductive DeclQuestionType where
  /-- Positive declarative question: "Peter is coming?" -/
  | PDQ
  /-- Negative declarative question: "Peter isn't coming?" -/
  | NDQ
  /-- Positive rejecting question: "Surely Peter is coming?" -/
  | PRQ
  /-- Negative rejecting question: "Surely Peter isn't coming?" -/
  | NRQ
  deriving DecidableEq, Repr

/-- The two classes: declarative questions vs. rejecting questions.

    DQs are less biased (speaker is "prejudiced" but not committed);
    RQs are more biased (speaker had a specific prior assumption that
    conflicts with contextual evidence). -/
inductive DeclQuestionClass where
  /-- Simple declarative question — speaker seeks confirmation -/
  | declarative
  /-- Rejecting question — speaker rejects what s/he sees -/
  | rejecting
  deriving DecidableEq, Repr

/-- Classify each type into its class. -/
def DeclQuestionType.questionClass : DeclQuestionType → DeclQuestionClass
  | .PDQ => .declarative
  | .NDQ => .declarative
  | .PRQ => .rejecting
  | .NRQ => .rejecting

/-- What a declarative of this type denotes (positive = p, negative = not-p). -/
def DeclQuestionType.declPolarity : DeclQuestionType → Core.Polarity
  | .PDQ => .positive
  | .NDQ => .negative
  | .PRQ => .positive
  | .NRQ => .negative

-- ============================================================================
-- S 3: Illocutionary Modifier (@cite{seeliger-repp-2018} SS 6.2)
-- ============================================================================

/-- The illocutionary modifier (IM) that occupies the ForceP specifier
    position in rejecting questions.

    @cite{seeliger-repp-2018} SS 6.2: FALSUM and VERUM are epistemic
    speech-act level operators. Their structural position is:

      [ForceP FALSUM/VERUM [Force' REJECTQ [TP ...]]]

    FALSUM signals zero commitment to the proposition (the speaker is
    essentially not committed to adding q to the CG). Used in NRQs.
    VERUM signals full commitment (the speaker is sure q should be in
    the CG). Used in PRQs. In PRQs, Swedish *visst*/*nog* or an
    evidential version of VERUM may appear.

    These correspond to the operators defined in
    `Semantics.Modality.BiasedPQ` (`verum`, `mkFalsum`). -/
inductive IllocutionaryModifier where
  /-- FALSUM: zero commitment to q (non-propositional negation).
      @cite{repp-2013}: speaker is not committed to q at issue. -/
  | falsum
  /-- VERUM: full commitment to q (q should be in the CG).
      @cite{romero-han-2004}: for-sure-CG that q should be added. -/
  | verum
  deriving DecidableEq, Repr

-- ============================================================================
-- S 4: REJECTQ Operator (eq. 40)
-- ============================================================================

/-- REJECTQ — the illocutionary operator for rejecting questions.

    @cite{seeliger-repp-2018} eq. 40:
      ⟦REJECTQ⟧ = λqλIM: [IM(¬q)]^evid & [IM(q)]^epist. {IM(q), ¬IM(q)}

    REJECTQ takes a proposition q and an illocutionary modifier IM.
    In German, IM is determined by syntactic Agree with *doch wohl*.
    In Swedish, it is determined by the presence of FALSUM (fronted
    negation) or VERUM (modal particles like *visst*/*nog*). -/
structure RejectQ where
  /-- The illocutionary modifier (FALSUM or VERUM) -/
  modifier : IllocutionaryModifier
  /-- Evidential presupposition: [IM(¬q)]^evid — on an evidential basis,
      the IM-determined degree of commitment to ¬q holds. -/
  evidentialPresupposition : Bool
  /-- Epistemic presupposition: [IM(q)]^epist — on an epistemic basis,
      the IM-determined degree of commitment to q holds. -/
  epistemicPresupposition : Bool
  deriving DecidableEq, Repr

/-- Construct a well-formed REJECTQ with both presuppositions satisfied. -/
def mkRejectQ (im : IllocutionaryModifier) : RejectQ :=
  { modifier := im
  , evidentialPresupposition := true
  , epistemicPresupposition := true }

-- ============================================================================
-- S 5: Deriving RQ Bias Profiles from REJECTQ
-- ============================================================================

/-- Derive the evidential bias from the IM choice in REJECTQ.

    The evidential presupposition is [IM(¬q)]^evid:
    - IM = VERUM: evidence strongly supports ¬q → evidential [+negative]
      (VERUM(¬q) = full commitment to ¬q on evidential basis)
    - IM = FALSUM: evidence yields zero commitment to ¬q → evidential [+positive]
      (FALSUM(¬q) = not committed to ¬q → by contrast, evidence for q) -/
def IllocutionaryModifier.evidentialBias : IllocutionaryModifier → BiasValue
  | .verum  => .plusNeg  -- strong evidence for ¬q
  | .falsum => .plusPos  -- evidence supports q (not ¬q)

/-- Derive the epistemic bias from the IM choice in REJECTQ.

    The epistemic presupposition is [IM(q)]^epist:
    - IM = VERUM: speaker is epistemically sure q should be in CG
      → epistemic [+positive] (speaker assumed q)
    - IM = FALSUM: speaker has zero epistemic commitment to q
      → epistemic [+negative] (by pragmatic strengthening in the
      RQ context, zero commitment to q implies belief in ¬q) -/
def IllocutionaryModifier.epistemicBias : IllocutionaryModifier → BiasValue
  | .verum  => .plusPos  -- speaker assumed q
  | .falsum => .plusNeg  -- speaker assumed ¬q

/-- The bias profile derived from REJECTQ's presuppositions. -/
def rejectQBiasProfile (im : IllocutionaryModifier) : BiasProfile :=
  { evidential := im.evidentialBias
  , epistemic := im.epistemicBias }

-- ============================================================================
-- S 6: Bias Profiles for All Types (@cite{seeliger-repp-2018}, Table 1)
-- ============================================================================

/-- DQ bias profiles are observational — DQs are not marked by REJECTQ,
    so their profiles don't derive from the IM parameter. Instead, DQs
    require contextual evidence matching the declarative polarity, and
    the speaker must not have already assumed the declarative's content.

    @cite{seeliger-repp-2018}: "DQs pattern with each other" (p. 136). -/
def dqBiasProfile (pol : Core.Polarity) : BiasProfile :=
  match pol with
  | .positive => { evidential := .plusPos, epistemic := .minusPos }
  | .negative => { evidential := .plusNeg, epistemic := .minusNeg }

/-- The bias profile for each declarative question type.

    DQ profiles are from `dqBiasProfile` (evidence-based);
    RQ profiles are from `rejectQBiasProfile` (REJECTQ-derived). -/
def DeclQuestionType.biasProfile : DeclQuestionType → BiasProfile
  | .PDQ => dqBiasProfile .positive
  | .NDQ => dqBiasProfile .negative
  | .PRQ => rejectQBiasProfile .verum
  | .NRQ => rejectQBiasProfile .falsum

-- ============================================================================
-- S 7: Verification Theorems
-- ============================================================================

-- Per-type bias profile verification (Table 1)
theorem pdq_profile : DeclQuestionType.PDQ.biasProfile =
    { evidential := .plusPos, epistemic := .minusPos } := rfl
theorem ndq_profile : DeclQuestionType.NDQ.biasProfile =
    { evidential := .plusNeg, epistemic := .minusNeg } := rfl
theorem prq_profile : DeclQuestionType.PRQ.biasProfile =
    { evidential := .plusNeg, epistemic := .plusPos } := rfl
theorem nrq_profile : DeclQuestionType.NRQ.biasProfile =
    { evidential := .plusPos, epistemic := .plusNeg } := rfl

-- Class membership
theorem pdq_is_declarative : DeclQuestionType.PDQ.questionClass = .declarative := rfl
theorem ndq_is_declarative : DeclQuestionType.NDQ.questionClass = .declarative := rfl
theorem prq_is_rejecting : DeclQuestionType.PRQ.questionClass = .rejecting := rfl
theorem nrq_is_rejecting : DeclQuestionType.NRQ.questionClass = .rejecting := rfl

-- Declarative polarity
theorem pdq_positive : DeclQuestionType.PDQ.declPolarity = .positive := rfl
theorem ndq_negative : DeclQuestionType.NDQ.declPolarity = .negative := rfl
theorem prq_positive : DeclQuestionType.PRQ.declPolarity = .positive := rfl
theorem nrq_negative : DeclQuestionType.NRQ.declPolarity = .negative := rfl

/-- DQs and RQs are distinct classes. -/
theorem dq_rq_different_classes :
    DeclQuestionType.PDQ.questionClass ≠ DeclQuestionType.PRQ.questionClass := by decide

/-- RQ bias profiles are fully derived from the IM choice —
    they come out of `rejectQBiasProfile`, not independent stipulation. -/
theorem prq_derived_from_verum :
    DeclQuestionType.PRQ.biasProfile = rejectQBiasProfile .verum := rfl

theorem nrq_derived_from_falsum :
    DeclQuestionType.NRQ.biasProfile = rejectQBiasProfile .falsum := rfl

/-- RQs have conflicting biases: evidential and epistemic target
    opposite polarities. This is what makes them "rejecting" — the
    speaker sees evidence against what s/he believed.

    Follows from the REJECTQ structure: IM(¬q) and IM(q) target
    opposite polarities by construction. -/
theorem rq_biases_conflict :
    (DeclQuestionType.PRQ.biasProfile.evidential = .plusNeg ∧
     DeclQuestionType.PRQ.biasProfile.epistemic = .plusPos) ∧
    (DeclQuestionType.NRQ.biasProfile.evidential = .plusPos ∧
     DeclQuestionType.NRQ.biasProfile.epistemic = .plusNeg) := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- DQs have compatible biases: evidential matches declarative polarity,
    epistemic is merely "minus" (speaker didn't assume, rather than
    actively assuming the opposite). -/
theorem dq_biases_compatible :
    (DeclQuestionType.PDQ.biasProfile.evidential = .plusPos ∧
     DeclQuestionType.PDQ.biasProfile.epistemic = .minusPos) ∧
    (DeclQuestionType.NDQ.biasProfile.evidential = .plusNeg ∧
     DeclQuestionType.NDQ.biasProfile.epistemic = .minusNeg) := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- RQ epistemic bias is always "plus" (active commitment);
    DQ epistemic bias is always "minus" (non-commitment).
    This is the defining difference between the two classes. -/
theorem rq_epistemic_is_plus :
    DeclQuestionType.PRQ.biasProfile.epistemic.IsPlus ∧
    DeclQuestionType.NRQ.biasProfile.epistemic.IsPlus := ⟨by decide, by decide⟩

theorem dq_epistemic_is_not_plus :
    ¬ DeclQuestionType.PDQ.biasProfile.epistemic.IsPlus ∧
    ¬ DeclQuestionType.NDQ.biasProfile.epistemic.IsPlus := ⟨by decide, by decide⟩

/-- NRQ is a subset of PDQ contexts: both require +positive evidential
    bias, but NRQs additionally require the speaker to have assumed ¬p
    (@cite{seeliger-repp-2018} p. 138: "a NRQ is used in a subset of
    the situations where a PDQ can be used"). -/
theorem nrq_subset_of_pdq :
    DeclQuestionType.PDQ.biasProfile.evidential =
    DeclQuestionType.NRQ.biasProfile.evidential ∧
    DeclQuestionType.PDQ.biasProfile.epistemic ≠
    DeclQuestionType.NRQ.biasProfile.epistemic := ⟨rfl, by decide⟩

/-- PRQ is a subset of NDQ contexts: both require +negative evidential
    bias, but PRQs additionally require the speaker to have assumed p. -/
theorem prq_subset_of_ndq :
    DeclQuestionType.NDQ.biasProfile.evidential =
    DeclQuestionType.PRQ.biasProfile.evidential ∧
    DeclQuestionType.NDQ.biasProfile.epistemic ≠
    DeclQuestionType.PRQ.biasProfile.epistemic := ⟨rfl, by decide⟩

-- ============================================================================
-- S 8: REJECTQ Verification
-- ============================================================================

theorem rejectQ_verum_evidential :
    (mkRejectQ .verum).evidentialPresupposition = true := rfl
theorem rejectQ_verum_epistemic :
    (mkRejectQ .verum).epistemicPresupposition = true := rfl
theorem rejectQ_falsum_modifier :
    (mkRejectQ .falsum).modifier = .falsum := rfl

/-- VERUM and FALSUM produce opposite evidential biases — they
    interpret the evidence in opposite directions. -/
theorem verum_falsum_opposite_evidential :
    IllocutionaryModifier.verum.evidentialBias ≠
    IllocutionaryModifier.falsum.evidentialBias := by decide

/-- VERUM and FALSUM produce opposite epistemic biases. -/
theorem verum_falsum_opposite_epistemic :
    IllocutionaryModifier.verum.epistemicBias ≠
    IllocutionaryModifier.falsum.epistemicBias := by decide

-- ============================================================================
-- S 9: Bridge to BiasedPQ (@cite{romero-2024})
-- ============================================================================

/-- Map Sudo's evidential bias values to Romero's contextual evidence.

    The [+positive]/[+negative] values map directly. [neutral] maps to
    neutral. The "minus" values have no direct Romero counterpart — they
    encode incompatibility constraints rather than positive evidence. -/
def evidentialToContextualEvidence : BiasValue → Option Modality.BiasedPQ.ContextualEvidence
  | .plusPos  => some .forP
  | .plusNeg  => some .againstP
  | .neutral  => some .neutral
  | .minusPos => none  -- no Romero counterpart
  | .minusNeg => none

/-- Map Sudo's epistemic bias values to Romero's original speaker bias.

    [+positive] maps to forP (speaker expected p). [+negative] maps to
    againstP. [neutral] maps to neutral. The "minus" values are not
    directly representable in Romero's three-valued system. -/
def epistemicToOriginalBias : BiasValue → Option Modality.BiasedPQ.OriginalBias
  | .plusPos  => some .forP
  | .plusNeg  => some .againstP
  | .neutral  => some .neutral
  | .minusPos => none  -- Seeliger & Repp extension, no Romero counterpart
  | .minusNeg => none

/-- NRQ evidential bias maps to Romero's "evidence for p" — the same
    contextual evidence configuration that licenses HiNQs. -/
theorem nrq_evidential_maps_to_forP :
    evidentialToContextualEvidence DeclQuestionType.NRQ.biasProfile.evidential =
    some .forP := rfl

/-- NRQ epistemic bias maps to Romero's "original bias against p". -/
theorem nrq_epistemic_maps_to_againstP :
    epistemicToOriginalBias DeclQuestionType.NRQ.biasProfile.epistemic =
    some .againstP := rfl

/-- PRQ epistemic bias maps to Romero's "original bias for p". -/
theorem prq_epistemic_maps_to_forP :
    epistemicToOriginalBias DeclQuestionType.PRQ.biasProfile.epistemic =
    some .forP := rfl

/-- All RQ bias values have Romero counterparts (they are all "plus"
    values). DQ epistemic "minus" values do not — this is precisely
    where Sudo's system extends Romero's. -/
theorem rq_values_have_romero_counterparts :
    (evidentialToContextualEvidence DeclQuestionType.PRQ.biasProfile.evidential).isSome = true ∧
    (epistemicToOriginalBias DeclQuestionType.PRQ.biasProfile.epistemic).isSome = true ∧
    (evidentialToContextualEvidence DeclQuestionType.NRQ.biasProfile.evidential).isSome = true ∧
    (epistemicToOriginalBias DeclQuestionType.NRQ.biasProfile.epistemic).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dq_epistemic_lacks_romero_counterpart :
    (epistemicToOriginalBias DeclQuestionType.PDQ.biasProfile.epistemic).isNone = true ∧
    (epistemicToOriginalBias DeclQuestionType.NDQ.biasProfile.epistemic).isNone = true :=
  ⟨rfl, rfl⟩

end Semantics.Questions.DeclarativeQuestions
