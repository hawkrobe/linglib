import Linglib.Theories.Pragmatics.Particles.DiscourseOnly
import Linglib.Theories.Pragmatics.DecisionTheoretic.But
import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Linglib.Phenomena.Focus.DiscourseOnly
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Discourse *only*
@cite{ippolito-kiss-williams-2025} @cite{merin-1999}

## Part I: End-to-End Derivation Chains

Concrete instantiations of the discourse *only* theory (@cite{ippolito-kiss-williams-2025} Def. 16)
that derive the acceptability of specific cross-linguistic examples.

### Architecture

The discourse *only* theory (in `Theories/Pragmatics/Particles/DiscourseOnly.lean`)
defines `isDefined`, `ciContent`, `agree`, `disagree` as `noncomputable Prop`
predicates over `Core.Issue` denotations and `Set W` doxastic states. This
file instantiates those predicates with a concrete 8-world model of the
house-buying scenario (@cite{ippolito-kiss-williams-2025} §7) and proves the
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
1. `isDefined` holds (the presupposition is satisfied)
2. `ciContent` holds (the CI: S supports α but S' doesn't)
3. These match the datum's `felicitous = true`

For interrogative S' examples (30a, 31a, etc.), the derivation shows that
the speaker's uncertainty about the answer blocks `fullSupportS` for S' on
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

namespace IppolitoKissWilliams2025

-- ============================================================================
-- Part I: End-to-End Derivation Chains
-- ============================================================================

open Semantics.Questions.ProbabilisticAnswerhood
open Semantics.Questions.Support
open Pragmatics.Particles.DiscourseOnly
open Phenomena.Focus.DiscourseOnly
open DTS

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
def beautiful : Set W := {w | w.val < 4}

instance : DecidablePred (· ∈ beautiful) := fun w => Nat.decLt w.val 4

/-- The house is expensive (w₂, w₃, w₆, w₇). -/
def expensive : Set W := {w | (w.val / 2) % 2 = 1}

instance : DecidablePred (· ∈ expensive) := fun w => Nat.decEq _ _

/-- The house has been renovated (w₀, w₂, w₄, w₆). -/
def renovated : Set W := {w | w.val % 2 = 0}

instance : DecidablePred (· ∈ renovated) := fun w => Nat.decEq _ _

/-- Should we buy the house? Only if beautiful, affordable, and renovated (w₀). -/
def buy : Set W := {w | w.val = 0}

instance : DecidablePred (· ∈ buy) := fun w => Nat.decEq _ _

/-- Uniform prior: P(w) = 1/8 for each world. -/
def prior : Prior W where
  mass := fun _ => 1 / 8
  mass_nonneg := by intro _; norm_num
  mass_sum_one := by native_decide

-- ============================================================================
-- § 2: QUD and Denotations
-- ============================================================================

/-- QUD: "Should we buy the house?" — binary issue. -/
def qud : Core.Issue W := Core.Issue.polar buy

/-- Declarative S: "The house is beautiful" — one alternative. -/
def sBeautiful : Core.Issue W := Core.Issue.polar beautiful

/-- Declarative S': "It's (very) expensive" — one alternative. -/
def s'Expensive : Core.Issue W := Core.Issue.polar expensive

/-- Polar Q S': "Has it been renovated?" — two alternatives. -/
def s'RenovatedQ : Core.Issue W := Core.Issue.polar renovated

-- ============================================================================
-- § 3: Doxastic States
-- ============================================================================

/-- Speaker who asserts "beautiful" and "expensive": believes both.
DOX_sp = {w₂, w₃} (beautiful ∧ expensive). -/
def doxBE : Set W := beautiful ∩ expensive

/-- Speaker who asserts "beautiful" but asks about renovation: believes
beautiful, uncertain about expense and renovation.
DOX_sp = {w₀, w₁, w₂, w₃} (beautiful). -/
def doxB : Set W := beautiful

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
  , partialAnswers := []
  , subquestions := [Core.Issue.polar beautiful, Core.Issue.polar expensive,
                     Core.Issue.polar renovated] }

/-- Context for clause-type examples: S = "beautiful", S' = interrogative.
Speaker believes S but doesn't know the answer to S'. Same subquestions
as core context — the QUD structure doesn't change with clause type. -/
def clauseTypeCtx : Context W :=
  { qud := qud
  , prior := prior
  , dox := doxB
  , partialAnswers := []
  , subquestions := [Core.Issue.polar beautiful, Core.Issue.polar expensive,
                     Core.Issue.polar renovated] }

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

/-- The presupposition is satisfied: S' is relevant and S supports an answer.

TODO: Structured proof that constructs witnesses for each conjunct.
The Set/Prop API replaces the old `native_decide` over `Bool isDefined`. -/
theorem core_isDefined : declSentence.isDefined coreCtx := by sorry

/-- The CI holds: ∃α (= buy) s.t. all partial answers support α (vacuous),
S supports α, and S' does not support α. -/
theorem core_ciContent : declSentence.ciContent coreCtx := by sorry

/-- The at-issue content is non-trivial: there exist worlds where both
S and S' hold (e.g., w₂: beautiful ∧ expensive). -/
theorem core_atIssue_nonempty :
    (2 : W) ∈ declSentence.atIssueContent := by
  -- atIssueContent = sBeautiful.info ∩ s'Expensive.info; both polar info = univ
  unfold Sentence.atIssueContent declSentence sBeautiful s'Expensive
  simp [Core.Issue.info_polar]

/-- S and S' disagree w.r.t. the QUD: S supports "buy" but S' supports
"don't buy", and they don't agree on any single answer. -/
theorem core_disagree : declSentence.disagree coreCtx := by sorry

/-- Per-datum connection: the theory predicts felicitous for the core examples.

Each core example (Italian 29a, Russian 29b, Hungarian 29c, Mandarin 29d,
English 2) instantiates this same semantic scenario. -/
theorem core_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    italian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem russian_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    russian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem hungarian_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    hungarian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem mandarin_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    mandarin_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem english_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    english_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

end CoreDerivation

-- ============================================================================
-- § 7: Clause-Type Derivation: Declarative S + Polar Q S'
-- ============================================================================

section PolarQDerivation

/-- The presupposition is satisfied even with interrogative S': the polar Q
"has it been renovated?" has alternatives [renovated, ¬renovated], and
knowing whether the house is renovated is relevant to buying. -/
theorem polarQ_isDefined : polarQSentence.isDefined clauseTypeCtx := by sorry

/-- The CI holds: the speaker believes the house is beautiful, so S supports
"buy". But the speaker doesn't know the answer to "has it been renovated?",
so the doxastic condition of fullSupportS fails for S' on every QUD answer.
S' trivially fails to support the buying direction. -/
theorem polarQ_ciContent : polarQSentence.ciContent clauseTypeCtx := by sorry

/-- Per-datum: predicts felicitous for all polar Q S' examples.

Russian 30a, Hungarian 31a, and Mandarin 32a all instantiate this scenario. -/
theorem russian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx ∧
    polarQSentence.ciContent clauseTypeCtx ∧
    russian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem hungarian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx ∧
    polarQSentence.ciContent clauseTypeCtx ∧
    hungarian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem mandarin_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx ∧
    polarQSentence.ciContent clauseTypeCtx ∧
    mandarin_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

end PolarQDerivation

-- ============================================================================
-- § 8: Abstract Theorem: Any Interrogative S' Where Speaker Doesn't Know Answer
-- ============================================================================

/-- For any context where S supports some QUD answer and S' is an interrogative
whose answer the speaker doesn't know, the CI's condition (ii) is satisfied:
S' trivially fails to support any answer because `fullSupportS` requires the
doxastic condition (`dox ⊆ q`), which fails when the speaker doesn't
believe any alternative of S'.

This generalizes the polar Q derivation to all interrogative S' examples
(30a-d, 31a-d, 32a-d): the specific content of the question doesn't matter
for the CI — only that the speaker doesn't know the answer. -/
theorem interrogative_s'_ci_satisfied {W' : Type*} [Fintype W']
    (sent : Sentence W') (ctx : Context W')
    -- S supports some answer
    (hSsupports : ∃ α ∈ Core.Issue.alt ctx.qud,
      fullSupportS ctx.dox sent.sDen ctx.prior α)
    -- Speaker doesn't believe any alternative of S'
    (hNoBelief : ∀ q ∈ Core.Issue.alt sent.s'Den, ¬ (ctx.dox ⊆ q))
    -- No prior partial answers (vacuous condition (i))
    (hPartial : ctx.partialAnswers = []) :
    sent.ciContent ctx := by
  obtain ⟨α, hMem, hSupp⟩ := hSsupports
  refine ⟨α, hMem, ?_, hSupp, ?_⟩
  · intro p hp
    rw [hPartial] at hp
    simp at hp
  · exact fullSupport_fails_unbelievedS ctx.dox sent.s'Den ctx.prior α hNoBelief

-- ============================================================================
-- Part II: DTS Connection
-- ============================================================================

open DTS
open DTS.But

-- ============================================================================
-- § 9: Witness Structure
-- ============================================================================

/-- A witness for the discourse *only* → DTS unexpectedness connection.

Bundles a DTS context together with two clausal arguments `s` and `s'`
(as `W → Prop`) and the evidence that `s` is positively relevant to the
topic H. Unlike the *but* witness, this does NOT require `s'` to be
negatively relevant — discourse *only* only requires `s'` to fail to
support, which is strictly weaker than negative relevance. -/
structure DTSDiscourseOnlyWitness (W : Type*) [Fintype W] where
  /-- The DTS context (dichotomic issue H + prior) -/
  dtsCtx : DTSContext W
  /-- Left clausal argument S -/
  s : Set W
  /-- Decidability of `s` (lifted to a typeclass instance below). -/
  sDec : DecidablePred (· ∈ s)
  /-- Right clausal argument S' -/
  s' : Set W
  /-- Decidability of `s'` (lifted to a typeclass instance below). -/
  s'Dec : DecidablePred (· ∈ s')
  /-- S is positively relevant to H -/
  sPosRelevant : posRelevant dtsCtx s

attribute [instance] DTSDiscourseOnlyWitness.sDec DTSDiscourseOnlyWitness.s'Dec

-- ============================================================================
-- § 10: Bridge Theorems
-- ============================================================================

/-- Probabilistic support (the absolute boost view) implies DTS positive
relevance (the Bayes factor view) for binary issues.

If `P(H|S) > P(H)` then `BF_H(S) > 1`. Both formalize the intuition that
S provides evidence for H; this theorem establishes the direction needed
for IKW's analysis.

The bridge is Bayes' theorem: P(H|S) > P(H) ↔ P(S∧H) > P(H)·P(S) (multiply
by P(S) > 0) ↔ P(S∧H)·(1−P(H)) > P(H)·P(S∧¬H) (partition P(S), expand)
↔ P(S∧H)·P(¬H) > P(H)·P(S∧¬H) (normalization: P(¬H) = 1−P(H))
↔ P(S|H) > P(S|¬H) (divide by P(H)P(¬H)) ↔ BF > 1.

The full proof requires partition / total-mass lemmas for `probSum` over
`Set.inter` / `Set.compl`. The legacy Bool-version proof used
the parallel `probOfProp` API in
`Semantics.Questions.ProbabilisticAnswerhood`; on the Prop side those
bridge lemmas need to be re-proved against `DTS.probSum`. Deferred. -/
theorem probSupports_implies_posRelevant_binary {W : Type*} [Fintype W]
    (prior : W → ℚ) (topic : Set W) [DecidablePred (· ∈ topic)]
    (evidence : Set W) [DecidablePred (· ∈ evidence)]
    (_hH_pos : probSum prior topic > 0)
    (_hNH_pos : probSum prior (topicᶜ) > 0)
    (_hS_pos : probSum prior evidence > 0)
    (_hNonneg : ∀ w, prior w ≥ 0)
    (_hNorm : probSum prior (Set.univ : Set W) = 1)
    (_hSupp : condProb prior evidence topic > margProb prior evidence) :
    posRelevant ⟨topic, inferInstance, prior⟩ evidence := by
  -- TODO: Bayes-theorem chase from `condProb prior evidence topic >
  -- margProb prior evidence` to `bayesFactor ⟨topic, _, prior⟩ evidence > 1`.
  -- Needs `probSum` partition lemmas (P(E) = P(E∧H) + P(E∧¬H)) and
  -- the total-mass identity (P(H) + P(¬H) = 1) re-proved for the Prop
  -- API. The Bool version of this proof has been removed.
  sorry

/-- Negative relevance (DTS) implies non-support (probabilistic).

If `S'` is negatively relevant to H (BF < 1, i.e., P(S'|H) < P(S'|¬H)),
then `S'` does not probabilistically support H — i.e.,
`P(H|S') ≤ P(H)`. This is the formal content of IKW's observation that
*but*'s condition on the second clause is strictly stronger than
discourse *only*'s.

By contrapositive: if `S'` did probabilistically support H, the previous
theorem would give `posRelevant` (BF > 1), contradicting `negRelevant`
(BF < 1). -/
theorem negRelevant_implies_not_probSupports {W : Type*} [Fintype W]
    (prior : W → ℚ) (topic : Set W) [DecidablePred (· ∈ topic)]
    (evidence : Set W) [DecidablePred (· ∈ evidence)]
    (hH_pos : probSum prior topic > 0)
    (hNH_pos : probSum prior (topicᶜ) > 0)
    (hS_pos : probSum prior evidence > 0)
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probSum prior (Set.univ : Set W) = 1)
    (hNeg : negRelevant ⟨topic, inferInstance, prior⟩ evidence) :
    ¬ (condProb prior evidence topic > margProb prior evidence) := by
  intro hSupp
  have hPos := probSupports_implies_posRelevant_binary prior topic evidence
    hH_pos hNH_pos hS_pos hNonneg hNorm hSupp
  simp only [posRelevant, negRelevant] at hPos hNeg
  linarith

/-- Every *but* context can license discourse *only*.

When `s` is posRelevant and `s'` is negRelevant (the *but* condition),
`s'` also fails to probabilistically support H (the *only* condition).
This formalizes @cite{ippolito-kiss-williams-2025} §6's claim that
discourse *only* is strictly weaker than *but*. -/
theorem but_sufficient_for_only {W : Type*} [Fintype W]
    (prior : W → ℚ) (topic : Set W) [DecidablePred (· ∈ topic)]
    (s s' : Set W) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ s')]
    (hH_pos : probSum prior topic > 0)
    (hNH_pos : probSum prior (topicᶜ) > 0)
    (_hS_pos : probSum prior s > 0)
    (hS'_pos : probSum prior s' > 0)
    (_hSpos : posRelevant ⟨topic, inferInstance, prior⟩ s)
    (hS'neg : negRelevant ⟨topic, inferInstance, prior⟩ s')
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probSum prior (Set.univ : Set W) = 1) :
    ¬ (condProb prior s' topic > margProb prior s') :=
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
    (hNorm : probSum w.dtsCtx.prior (Set.univ : Set W) = 1)
    (hS_pos : 0 < probSum w.dtsCtx.prior w.s)
    (hH_pos : 0 < probSum w.dtsCtx.prior w.dtsCtx.topic)
    (hNH_pos : 0 < probSum w.dtsCtx.prior (w.dtsCtx.topicᶜ))
    (hCIP : CIP w.dtsCtx w.s w.s') :
    condProb w.dtsCtx.prior w.s' w.s <
    margProb w.dtsCtx.prior w.s' :=
  cip_contrariness_implies_unexpectedness w.dtsCtx w.s w.s'
    hPrior hNorm hCIP (.inl ⟨w.sPosRelevant, hS'neg⟩) hS_pos hH_pos hNH_pos

end IppolitoKissWilliams2025
