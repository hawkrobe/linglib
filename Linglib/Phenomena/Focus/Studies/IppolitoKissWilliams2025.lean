import Linglib.Theories.Semantics.Lexical.Particle.DiscourseOnly
import Linglib.Theories.Pragmatics.DecisionTheoretic.But
import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Linglib.Phenomena.Focus.DiscourseOnly

/-!
# Discourse *only*
@cite{ippolito-kiss-williams-2025} @cite{merin-1999}

## Part I: End-to-End Derivation Chains

Concrete instantiations of the discourse *only* theory (@cite{ippolito-kiss-williams-2025} Def. 16)
that derive the acceptability of specific cross-linguistic examples.

### Architecture

The discourse *only* theory (in `Lexical/Particle/DiscourseOnly.lean`) defines
`isDefined` and `ciContent` as computable `Bool` functions over abstract types.
This file instantiates those functions with a concrete 8-world model of the
house-buying scenario used throughout IKW §7, then proves that the theory's
predictions match the empirical data in `Phenomena/Focus/DiscourseOnly.lean`.

### The House Model

8 worlds varying on three binary properties: beautiful, expensive, renovated.
The QUD "Should we buy the house?" is answered affirmatively only when the house
is beautiful, affordable, AND renovated (w₀). This ensures:
- "beautiful" supports buying (P(buy|beautiful) > P(buy))
- "expensive" anti-supports buying (P(buy|expensive) = 0)
- "renovated" is relevant to buying (P(buy|renovated) > P(buy))

### Derivation Chains

Each derivation theorem proves:
1. `isDefined` = true (the presupposition is satisfied)
2. `ciContent` = true (the CI holds: S supports α but S' doesn't)
3. These match the datum's `felicitous = true`

For interrogative S' examples (30a, 31a, etc.), the derivation shows that
the speaker's uncertainty about the answer blocks `fullSupport` for S' on
all QUD answers, trivially satisfying the CI's condition (ii).

## Part II: DTS Connection

Connects the CI of discourse *only* to
@cite{merin-1999}'s Decision-Theoretic Semantics, specifically the notion of
unexpectedness from the analysis of *but*.

### Key Connection

Both *but* and discourse *only* express a form of evidential contrast:

- *but*: A is positively relevant and B is negatively relevant to H
  → B is unexpected given A (Theorem 8)
- discourse *only*: S supports α but S' does not support α
  → S' undermines the evidential direction

### The *but*/*only* Asymmetry (@cite{ippolito-kiss-williams-2025} §6)

*but* requires `negRelevant` (BF < 1): the second clause must actively
provide counter-evidence. Discourse *only* only requires `¬probSupports`:
the second clause merely fails to support the direction. Since
`negRelevant → ¬probSupports` (anti-support implies non-support), *but*'s
condition is strictly stronger. This means every *but* context could license
discourse *only*, but not vice versa.
-/

namespace Phenomena.Focus.Studies.IppolitoKissWilliams2025

-- ============================================================================
-- Part I: End-to-End Derivation Chains
-- ============================================================================

open Discourse
open Semantics.Questions.ProbabilisticAnswerhood
open Semantics.Questions.Support
open Semantics.Lexical.Particle.DiscourseOnly
open Phenomena.Focus.DiscourseOnly

-- ============================================================================
-- § 1: World Type and Propositions
-- ============================================================================

/-- 8-world model for the house-buying scenario.

Encoding: w = 4b + 2e + r where
- b ∈ {0,1}: beauty (0 = beautiful)
- e ∈ {0,1}: expense (0 = affordable)
- r ∈ {0,1}: renovation (0 = renovated)

| World | Beautiful | Expensive | Renovated | Buy? |
|-------|-----------|-----------|-----------|------|
| w₀    | ✓         |           | ✓         | ✓    |
| w₁    | ✓         |           |           |      |
| w₂    | ✓         | ✓         | ✓         |      |
| w₃    | ✓         | ✓         |           |      |
| w₄    |           |           | ✓         |      |
| w₅    |           |           |           |      |
| w₆    |           | ✓         | ✓         |      |
| w₇    |           | ✓         |           |      |
-/
abbrev W := Fin 8

/-- The house is beautiful (w₀–w₃). -/
def beautiful : W → Bool := fun w => w.val < 4

/-- The house is expensive (w₂, w₃, w₆, w₇). -/
def expensive : W → Bool := fun w => (w.val / 2) % 2 == 1

/-- The house has been renovated (w₀, w₂, w₄, w₆). -/
def renovated : W → Bool := fun w => w.val % 2 == 0

/-- Should we buy the house? Only if beautiful, affordable, and renovated (w₀). -/
def buy : W → Bool := fun w => w.val == 0

/-- Uniform prior: P(w) = 1/8 for each world. -/
def prior : Prior W where
  mass := fun _ => 1 / 8
  mass_nonneg := by intro _; norm_num
  mass_sum_one := by native_decide

/-- All worlds for doxastic subset checks. -/
def worlds : List W := List.finRange 8

-- ============================================================================
-- § 2: QUD and Denotations
-- ============================================================================

/-- QUD: "Should we buy the house?" — binary issue. -/
def qud : Issue W := Issue.polar buy

/-- Declarative S: "The house is beautiful" — one alternative. -/
def sBeautiful : Issue W := ⟨[beautiful]⟩

/-- Declarative S': "It's (very) expensive" — one alternative. -/
def s'Expensive : Issue W := ⟨[expensive]⟩

/-- Polar Q S': "Has it been renovated?" — two alternatives. -/
def s'RenovatedQ : Issue W := Issue.polar renovated

-- ============================================================================
-- § 3: Doxastic States
-- ============================================================================

/-- Speaker who asserts "beautiful" and "expensive": believes both.
DOX_sp = {w₂, w₃} (beautiful ∧ expensive). -/
def doxBE : InfoState W := fun w => beautiful w && expensive w

/-- Speaker who asserts "beautiful" but asks about renovation: believes
beautiful, uncertain about expense and renovation.
DOX_sp = {w₀, w₁, w₂, w₃} (beautiful). -/
def doxB : InfoState W := fun w => beautiful w

-- ============================================================================
-- § 4: Contexts
-- ============================================================================

/-- Context for core examples: S = "beautiful", S' = "expensive".
No prior partial answers — fresh discourse.

Subquestions per IKW §5.1: "Answering this question requires answering
its plausible subquestions, such as *Is the house beautiful?
Is the house expensive?*" We also include renovation since it
appears in the polar Q examples. -/
def coreCtx : Context W :=
  { qud := qud
  , prior := prior
  , dox := doxBE
  , worlds := worlds
  , partialAnswers := []
  , subquestions := [Issue.polar beautiful, Issue.polar expensive,
                     Issue.polar renovated] }

/-- Context for clause-type examples: S = "beautiful", S' = interrogative.
Speaker believes S but doesn't know the answer to S'. Same subquestions
as core context — the QUD structure doesn't change with clause type. -/
def clauseTypeCtx : Context W :=
  { qud := qud
  , prior := prior
  , dox := doxB
  , worlds := worlds
  , partialAnswers := []
  , subquestions := [Issue.polar beautiful, Issue.polar expensive,
                     Issue.polar renovated] }

-- ============================================================================
-- § 5: Sentences
-- ============================================================================

/-- "The house is beautiful, only it's expensive" (core declarative-declarative). -/
def declSentence : Sentence W :=
  { sDen := sBeautiful
  , s'Den := s'Expensive }

/-- "The house is beautiful, only has it been renovated?" (polar Q as S'). -/
def polarQSentence : Sentence W :=
  { sDen := sBeautiful
  , s'Den := s'RenovatedQ }

-- ============================================================================
-- § 6: Core Derivation: Declarative S + Declarative S'
-- ============================================================================

section CoreDerivation

/-- The presupposition is satisfied: S' is relevant and S supports an answer. -/
theorem core_isDefined : declSentence.isDefined coreCtx = true := by native_decide

/-- The CI holds: ∃α (= buy) s.t. all partial answers support α (vacuous),
S supports α, and S' does not support α. -/
theorem core_ciContent : declSentence.ciContent coreCtx = true := by native_decide

/-- The at-issue content is non-trivial: there exist worlds where both
S and S' hold (e.g., w₂: beautiful ∧ expensive). -/
theorem core_atIssue_nonempty :
    declSentence.atIssueContent (2 : W) = true := by native_decide

/-- S and S' disagree w.r.t. the QUD: S supports "buy" but S' supports
"don't buy", and they don't agree on any single answer. -/
theorem core_disagree : declSentence.disagree coreCtx = true := by native_decide

/-- Per-datum connection: the theory predicts felicitous for the core examples.

Each core example (Italian 29a, Russian 29b, Hungarian 29c, Mandarin 29d,
English 2) instantiates this same semantic scenario. -/
theorem core_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    italian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem russian_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    russian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem hungarian_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    hungarian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem mandarin_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    mandarin_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem english_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    english_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

end CoreDerivation

-- ============================================================================
-- § 7: Clause-Type Derivation: Declarative S + Polar Q S'
-- ============================================================================

section PolarQDerivation

/-- The presupposition is satisfied even with interrogative S': the polar Q
"has it been renovated?" has alternatives [renovated, ¬renovated], and
knowing whether the house is renovated is relevant to buying. -/
theorem polarQ_isDefined : polarQSentence.isDefined clauseTypeCtx = true := by
  native_decide

/-- The CI holds: the speaker believes the house is beautiful, so S supports
"buy". But the speaker doesn't know the answer to "has it been renovated?",
so the doxastic condition of fullSupport fails for S' on every QUD answer.
S' trivially fails to support the buying direction. -/
theorem polarQ_ciContent : polarQSentence.ciContent clauseTypeCtx = true := by
  native_decide

/-- Per-datum: predicts felicitous for all polar Q S' examples.

Russian 30a, Hungarian 31a, and Mandarin 32a all instantiate this scenario. -/
theorem russian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx = true ∧
    polarQSentence.ciContent clauseTypeCtx = true ∧
    russian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem hungarian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx = true ∧
    polarQSentence.ciContent clauseTypeCtx = true ∧
    hungarian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem mandarin_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx = true ∧
    polarQSentence.ciContent clauseTypeCtx = true ∧
    mandarin_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

end PolarQDerivation

-- ============================================================================
-- § 8: Abstract Theorem: Any Interrogative S' Where Speaker Doesn't Know Answer
-- ============================================================================

/-- For any context where S supports some QUD answer and S' is an interrogative
whose answer the speaker doesn't know, the CI's condition (ii) is satisfied:
S' trivially fails to support any answer because fullSupport requires the
doxastic condition (DOX_sp ⊆ q), which fails when the speaker doesn't
believe any alternative of S'.

This generalizes the polar Q derivation to all interrogative S' examples
(30a-d, 31a-d, 32a-d): the specific content of the question doesn't matter
for the CI — only that the speaker doesn't know the answer. -/
theorem interrogative_s'_ci_satisfied {W' : Type*} [Fintype W']
    (sent : Sentence W') (ctx : Context W')
    -- S supports some answer
    (hSsupports : ctx.qud.alternatives.any (fun α =>
      fullSupport ctx.dox sent.sDen ctx.prior α ctx.worlds) = true)
    -- Speaker doesn't believe any alternative of S'
    (hNoBelief : ∀ q, q ∈ sent.s'Den.alternatives →
      Discourse.supports ctx.dox q ctx.worlds = false)
    -- No prior partial answers that fail to support (vacuous when empty)
    (hPartial : ctx.partialAnswers = []) :
    sent.ciContent ctx = true := by
  unfold Sentence.ciContent
  rw [List.any_eq_true] at hSsupports ⊢
  obtain ⟨α, hMem, hSupp⟩ := hSsupports
  refine ⟨α, hMem, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', hPartial, List.all_nil,
    true_and]
  constructor
  · exact hSupp
  · exact fullSupport_fails_unbelieved ctx.dox sent.s'Den ctx.prior α
      ctx.worlds hNoBelief

-- ============================================================================
-- Part II: DTS Connection
-- ============================================================================

open Core.Proposition
open Theories.DTS
open Theories.DTS.But

-- ============================================================================
-- § 9: Binary Issue Conversion
-- ============================================================================

/-- Convert a DTS dichotomic issue {H, ¬H} to an inquisitive `Issue`.

A DTS `Issue W` is a single topic H (with ¬H implicit). The corresponding
inquisitive issue has two alternatives: H and ¬H. -/
def dtsToInquisitive {W : Type*} (topic : BProp W) : Discourse.Issue W :=
  Discourse.Issue.polar topic

/-- The DTS issue and inquisitive issue have matching alternatives. -/
theorem dtsToInquisitive_alternatives {W : Type*} (topic : BProp W) :
    (dtsToInquisitive topic).alternatives = [topic, λ w => !topic w] := rfl

-- ============================================================================
-- § 10: Witness Structure
-- ============================================================================

/-- A witness for the discourse *only* → DTS unexpectedness connection.

Bundles a DTS context, a discourse *only* configuration (as raw propositions
for the binary case), and evidence that S is positively relevant to the
topic H. Unlike the *but* witness, this does NOT require S' to be negatively
relevant — discourse *only* only requires S' to fail to support, which is
strictly weaker than negative relevance. -/
structure DTSDiscourseOnlyWitness (W : Type*) [Fintype W] where
  /-- The DTS context (dichotomic issue H + prior) -/
  dtsCtx : DTSContext W
  /-- Left clausal argument S (as a proposition for the binary case) -/
  s : W → Bool
  /-- Right clausal argument S' (as a proposition for the binary case) -/
  s' : W → Bool
  /-- S is positively relevant to H -/
  sPosRelevant : posRelevant dtsCtx s

-- ============================================================================
-- § 11: Bridge Theorems
-- ============================================================================

-- Helper lemmas bridging probOfProp (ProbabilisticAnswerhood) and
-- condProb/probSum (DTS). Both compute ∑ w, if f w then prior w else 0
-- but are separate definitions in different modules.

/-- Bridge: DTS `condProb` expressed in terms of `probOfProp`. -/
private lemma condProb_eq_probOfProp {W : Type*} [Fintype W]
    (prior : Prior W) (e h : W → Bool) (hh : probOfProp prior h ≠ 0) :
    condProb prior.mass e h =
    probOfProp prior (λ w => e w && h w) / probOfProp prior h := by
  unfold condProb
  simp only [show probSum prior.mass h = probOfProp prior h from rfl, hh, ↓reduceIte,
    show probSum prior.mass (Decidable.pand W e h) = probOfProp prior (λ w => e w && h w) from rfl]

/-- Partition: P(E) = P(E∧H) + P(E∧¬H). -/
private lemma probOfProp_partition {W : Type*} [Fintype W]
    (prior : Prior W) (e h : W → Bool) :
    probOfProp prior e =
    probOfProp prior (λ w => e w && h w) +
    probOfProp prior (λ w => e w && !h w) :=
  prior.probOf_partition e h

/-- Total partition: P(⊤) = P(H) + P(¬H). -/
private lemma probOfProp_total_partition {W : Type*} [Fintype W]
    (prior : Prior W) (h : W → Bool) :
    probOfProp prior (λ _ => true) =
    probOfProp prior h + probOfProp prior (λ w => !h w) := by
  have := prior.probOf_partition (λ _ => true) h
  simp only [Bool.true_and] at this; exact this

/-- Non-negativity of probOfProp under non-negative prior. -/
private lemma probOfProp_nonneg' {W : Type*} [Fintype W]
    (prior : Prior W) (_hP : ∀ w, prior w ≥ 0) (f : W → Bool) :
    probOfProp prior f ≥ 0 :=
  prior.probOf_nonneg f

/-- For binary issues, probabilistic `probSupports` (P(H|S) > P(H)) implies
DTS `posRelevant` (BF_H(S) > 1).

Both capture the same intuition — S provides evidence for H — but via
different formalizations: `probSupports` uses the absolute probability boost,
while `posRelevant` uses the Bayes factor ratio.

The bridge is Bayes' theorem: P(H|S) > P(H) ↔ P(S∧H) > P(H)·P(S) (multiply
by P(S) > 0) ↔ P(S∧H)·(1−P(H)) > P(H)·P(S∧¬H) (partition P(S), expand)
↔ P(S∧H)·P(¬H) > P(H)·P(S∧¬H) (normalization: P(¬H) = 1−P(H))
↔ P(S|H) > P(S|¬H) (divide by P(H)P(¬H)) ↔ BF > 1. -/
theorem probSupports_implies_posRelevant_binary {W : Type*} [Fintype W]
    (prior : Prior W) (topic : BProp W) (evidence : W → Bool)
    (hH_pos : probOfProp prior topic > 0)
    (hNH_pos : probOfProp prior (λ w => !topic w) > 0)
    (hS_pos : probOfProp prior evidence > 0)
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probOfProp prior (fun _ => true) = 1) :
    probSupports prior evidence topic = true →
    posRelevant ⟨⟨topic⟩, prior.mass⟩ evidence := by
  intro hSupp
  simp only [probSupports, isPositiveEvidence, evidentialBoost, decide_eq_true_eq] at hSupp
  rw [show conditionalProb prior evidence topic =
        probOfProp prior (fun w => evidence w && topic w) / probOfProp prior evidence from
    Core.FinitePMF.condProb_of_pos prior evidence topic hS_pos] at hSupp
  set pH := probOfProp prior topic
  set pNH := probOfProp prior (λ w => !(topic w))
  set pE := probOfProp prior evidence
  set pEH := probOfProp prior (λ w => evidence w && topic w)
  set pENH := probOfProp prior (λ w => evidence w && !(topic w))
  have hPartE : pE = pEH + pENH := probOfProp_partition prior evidence topic
  have hNormPH : pH + pNH = 1 := by linarith [probOfProp_total_partition prior topic]
  have hpEH_gt : pEH > pH * pE := by
    have h1 : pH < pEH / pE := by linarith
    rw [lt_div_iff₀ hS_pos] at h1; linarith
  have hCross : pEH * pNH > pH * pENH := by
    have h_expand : pH * pE = pH * pEH + pH * pENH := by rw [hPartE]; ring
    have h_sub : pEH - pH * pEH > pH * pENH := by linarith [hpEH_gt, h_expand]
    have h_prod : pEH * pNH = pEH - pEH * pH := by
      rw [show pNH = 1 - pH from by linarith]; ring
    linarith
  have hpEH_pos : pEH > 0 := by nlinarith [mul_nonneg (le_of_lt hH_pos) (le_of_lt hS_pos)]
  have hpENH_nonneg : pENH ≥ 0 := probOfProp_nonneg' prior hNonneg _
  have hCondH : condProb prior.mass evidence topic = pEH / pH :=
    condProb_eq_probOfProp prior evidence topic (ne_of_gt hH_pos)
  have hCondNH : condProb prior.mass evidence (Decidable.pnot W topic) = pENH / pNH :=
    condProb_eq_probOfProp prior evidence (λ w => !(topic w)) (ne_of_gt hNH_pos)
  show bayesFactor ⟨⟨topic⟩, prior.mass⟩ evidence > 1
  simp only [bayesFactor, hCondH, hCondNH]
  by_cases hENH : pENH = 0
  · simp [hENH, show pEH / pH > 0 from div_pos hpEH_pos hH_pos]
  · have hpENH_pos : pENH > 0 := lt_of_le_of_ne hpENH_nonneg (Ne.symm hENH)
    have hCondNH_pos : pENH / pNH > 0 := div_pos hpENH_pos hNH_pos
    simp only [ne_of_gt hCondNH_pos, ↓reduceIte]
    rw [gt_iff_lt, one_lt_div hCondNH_pos, div_lt_div_iff₀ hNH_pos hH_pos]
    linarith [hCross]

/-- Negative relevance (DTS) implies non-support (probabilistic).

If S' is negatively relevant to H (BF < 1, i.e., P(S'|H) < P(S'|¬H)),
then S' does not probabilistically support H. This is the formal content
of IKW's observation that *but*'s condition on the second clause is strictly
stronger than discourse *only*'s.

By contrapositive: if `probSupports` were true, Bayes' theorem would give
`posRelevant` (BF > 1), contradicting `negRelevant` (BF < 1). -/
theorem negRelevant_implies_not_probSupports {W : Type*} [Fintype W]
    (prior : Prior W) (topic : BProp W) (evidence : W → Bool)
    (hH_pos : probOfProp prior topic > 0)
    (hNH_pos : probOfProp prior (λ w => !topic w) > 0)
    (hS_pos : probOfProp prior evidence > 0)
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probOfProp prior (fun _ => true) = 1)
    (hNeg : negRelevant ⟨⟨topic⟩, prior.mass⟩ evidence) :
    probSupports prior evidence topic = false := by
  by_contra hContra
  push_neg at hContra
  have hTrue : probSupports prior evidence topic = true :=
    Bool.eq_iff_iff.mpr (by simp [hContra])
  have hPos := probSupports_implies_posRelevant_binary prior topic evidence
    hH_pos hNH_pos hS_pos hNonneg hNorm hTrue
  simp only [posRelevant, negRelevant] at hPos hNeg
  linarith

/-- Every *but* context can license discourse *only*.

When S is posRelevant and S' is negRelevant (the *but* condition), S'
also fails to probabilistically support H (the *only* condition). This
formalizes @cite{ippolito-kiss-williams-2025} §6's claim that discourse *only* is strictly weaker
than *but*. -/
theorem but_sufficient_for_only {W : Type*} [Fintype W]
    (prior : Prior W) (topic : BProp W)
    (s s' : W → Bool)
    (hH_pos : probOfProp prior topic > 0)
    (hNH_pos : probOfProp prior (λ w => !topic w) > 0)
    (_hS_pos : probOfProp prior s > 0)
    (hS'_pos : probOfProp prior s' > 0)
    (_hSpos : posRelevant ⟨⟨topic⟩, prior.mass⟩ s)
    (hS'neg : negRelevant ⟨⟨topic⟩, prior.mass⟩ s')
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probOfProp prior (fun _ => true) = 1) :
    probSupports prior s' topic = false :=
  negRelevant_implies_not_probSupports prior topic s' hH_pos hNH_pos hS'_pos
    hNonneg hNorm hS'neg

/-- Discourse *only*'s CI implies unexpectedness when the QUD is binary,
S' is negatively relevant, and CIP holds.

When S is posRelevant and S' is negRelevant (the stronger *but* condition),
Merin's Theorem 8 gives P(S'|S) < P(S'): S' is unexpected given S.

Note: this theorem uses the stronger *but* condition (negRelevant) rather than
the weaker discourse *only* condition (¬probSupports). Unexpectedness in
Merin's sense requires active counter-relevance, not just failure to support.
This means unexpectedness is a consequence when discourse *only* sentences
happen to meet the stronger *but* threshold. -/
theorem discOnly_implies_unexpectedness_under_but {W : Type*} [Fintype W]
    (w : DTSDiscourseOnlyWitness W)
    (hS'neg : negRelevant w.dtsCtx w.s')
    (hPrior : ∀ x, w.dtsCtx.prior x ≥ 0)
    (hNorm : probSum w.dtsCtx.prior (Decidable.top W) = 1)
    (hS_pos : 0 < probSum w.dtsCtx.prior w.s)
    (hH_pos : 0 < probSum w.dtsCtx.prior w.dtsCtx.issue.topic)
    (hNH_pos : 0 < probSum w.dtsCtx.prior (Decidable.pnot W w.dtsCtx.issue.topic))
    (hCIP : CIP w.dtsCtx w.s w.s') :
    condProb w.dtsCtx.prior w.s' w.s <
    margProb w.dtsCtx.prior w.s' := by
  exact cip_contrariness_implies_unexpectedness w.dtsCtx w.s w.s'
    hPrior hNorm hCIP (.inl ⟨w.sPosRelevant, hS'neg⟩) hS_pos hH_pos hNH_pos

end Phenomena.Focus.Studies.IppolitoKissWilliams2025
