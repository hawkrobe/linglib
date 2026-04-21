import Linglib.Theories.Semantics.Questions.Answerhood.Support
import Linglib.Core.Question.Relevance

/-!
# Discourse *only* @cite{ippolito-kiss-williams-2025}
@cite{potts-2005} @cite{roberts-2012} @cite{thomas-2026}

Semantics of discourse *only*: a connective that takes two clausal arguments
S and S' and contributes a conventional implicature (CI) that S' fails to
support the evidential direction established by prior partial answers to the QUD.

## The Puzzle

Cross-linguistically, some languages have a discourse particle glossed as
"only" that conjoins two clauses while signaling that the second undermines
the evidential trajectory of the first:

- Italian: *solo che* ("La casa è bella, solo che è costosissima")
- Russian: *tol'ko* ("Квартира большая, только кухня маленькая")
- Hungarian: *csak* ("A ház szép, csak drága")
- Mandarin: *zhǐshì* ("房子很好, 只是太贵了")

## Definition 16

⟦S [only S']⟧^c is defined only if S and S' are relevant to QUD in c and
∃α ∈ QUD s.t. S supports α. If defined:
- At-issue: highlighted content of S intersected with that of S'
  (every world where both S and S' are informatively true)
- CI: ∃α ∈ QUD s.t. (i) every true partial answer p ∉ QUD supports α,
  and (ii) S' does not support α

## Key Predictions

- **Interrogative left-arg restriction** (§5.2): Canonical info-seeking questions
  cannot be the left argument because the speaker doesn't believe any answer,
  so DOX_sp ⊆ q fails for all q, and SUPPORT fails. This falls out from
  `fullSupport_fails_unbelievedS` in Support.lean — no stipulation needed.
- **Biased/rhetorical questions CAN be left args** (§5.2, exx. 20–21): These
  questions have a believed answer (DOX_sp ⊆ q for some q), so the doxastic
  condition is satisfied.
- **Comparison with *but*** (§6): Both express contrast, but *only*'s right
  argument only needs to fail to support (¬SUPPORT), not actively counter-support
  (negRelevant). This makes *only* strictly weaker than *but*.

## Mathlib-pure formulation

This file uses `Core.Question` (Set-based) for inquisitive denotations,
`Set W` for doxastic states and answers, and `Prop` predicates throughout.
The DOX-subset check is native `Set.Subset`. Universal quantification over
prior partial answers is a clean `∀ p ∈ partialAnswers, ...`.
-/

namespace Pragmatics.Particles.DiscourseOnly

open Semantics.Questions.ProbabilisticAnswerhood
open Semantics.Questions.Support

-- Context

/-- Discourse context for evaluating discourse *only* (mathlib-pure).

Includes the QUD as a `Core.Question`, a prior distribution, the speaker's
doxastic state as a `Set W`, and a record of true partial answers
established in prior discourse.

The doxastic state is what makes the interrogative restriction fall out
naturally: canonical info-seeking questions fail the doxastic condition
of SUPPORT (the speaker doesn't believe any answer). -/
structure Context (W : Type*) [Fintype W] where
  /-- The QUD as an inquisitive issue -/
  qud : Core.Question W
  /-- Prior probability distribution -/
  prior : Prior W
  /-- Speaker's doxastic state DOX_sp -/
  dox : Set W
  /-- True partial answers to the QUD established in prior discourse.

  @cite{ippolito-kiss-williams-2025} Def. 16 CI condition (i) quantifies universally over ALL true
  partial answers p ∉ QUD: each must support the same α. We track these
  explicitly so the CI can check the universal condition. -/
  partialAnswers : List (Set W)
  /-- Subquestions of the QUD established by the discourse context.

  @cite{roberts-2012} Def. 8–9: q is a subquestion of Q iff answering Q
  (contextually) entails a complete answer to q. @cite{ippolito-kiss-williams-2025} §5.1:
  "Answering this question requires answering its plausible subquestions,
  such as *Is the house beautiful? Is the house expensive?*"

  These are provided by the discourse context, not computed: the contextual
  entailment relation depends on common ground assumptions (e.g., beauty
  is a criterion for buying). -/
  subquestions : List (Core.Question W)

-- Sentence

/-- A discourse *only* sentence with two clausal arguments.

`sDen` is the inquisitive denotation of the left argument S,
`s'Den` is the inquisitive denotation of the right argument S'.

For declaratives, each `Question` has a single nontrivial alternative (the
propositional content). For questions, each `Question` has multiple
alternatives. The denotation type is uniform — what varies is whether
the doxastic condition of SUPPORT can be satisfied. -/
structure Sentence (W : Type*) where
  /-- Inquisitive denotation of the left argument S -/
  sDen : Core.Question W
  /-- Inquisitive denotation of the right argument S' -/
  s'Den : Core.Question W

namespace Sentence

variable {W : Type*} [Fintype W]

/-- At-issue content of "S only S'" (Set form).

@cite{ippolito-kiss-williams-2025} Def. 16: the at-issue content is the
pair ⟨⟦S⟧, ⟦S'⟧⟩. For declarative arguments, we model this as the
intersection of the informational content of each denotation: every
world where both S and S' are informatively true. -/
def atIssueContent (d : Sentence W) : Set W :=
  d.sDen.info ∩ d.s'Den.info

open Classical in
/-- Presupposition / definedness condition for discourse *only* (Prop form).

@cite{ippolito-kiss-williams-2025} Def. 16: ⟦S [only S']⟧ is defined only if S and S' are
"relevant" to the QUD and ∃α ∈ QUD s.t. S supports α.

Three conditions:

1. **S is structurally relevant**: some alternative of S partially answers
   the QUD or a subquestion of the QUD (via `Core.Question.moveRelevant`).

2. **S' is structurally relevant**: same check for the right argument.

3. **S supports some answer α** via `fullSupportS` (doxastic + probabilistic).
   This is where the interrogative left-argument restriction falls out: the
   doxastic condition (Def. 13) blocks info-seeking questions from supporting
   any answer. -/
noncomputable def isDefined (d : Sentence W) (ctx : Context W) : Prop :=
  Core.Question.moveRelevant d.sDen ctx.qud ctx.subquestions ∧
  Core.Question.moveRelevant d.s'Den ctx.qud ctx.subquestions ∧
  ∃ α ∈ Core.Question.alt ctx.qud, fullSupportS ctx.dox d.sDen ctx.prior α

open Classical in
/-- CI content of discourse *only* (Prop form).

@cite{ippolito-kiss-williams-2025} Def. 16 CI: ∃α ∈ QUD s.t.
(i) ∀p ∈ partialAnswers, p supports α (all prior discourse points toward α)
(ii) S' does not SUPPORT α (the right argument fails to support that direction)

Condition (i) captures the universal quantification over true partial answers.
When partialAnswers is empty, condition (i) is vacuously true, which is correct:
the CI only requires that no prior evidence contradicts the direction.

The "S supports α" condition is included explicitly here as part of
establishing the direction. -/
noncomputable def ciContent (d : Sentence W) (ctx : Context W) : Prop :=
  ∃ α ∈ Core.Question.alt ctx.qud,
    -- (i) All true partial answers support α (probabilistically; speaker has
    -- already committed to believing them, so doxastic condition is trivial).
    (∀ p ∈ ctx.partialAnswers, isPositiveEvidenceS p α ctx.prior) ∧
    -- S itself supports α (part of establishing the direction)
    fullSupportS ctx.dox d.sDen ctx.prior α ∧
    -- (ii) S' does NOT support α
    ¬ fullSupportS ctx.dox d.s'Den ctx.prior α

open Classical in
/-- Agreement: S and S' agree w.r.t. the QUD iff there is an α ∈ QUD s.t.
both S and S' fully support α.

@cite{ippolito-kiss-williams-2025} Def. 14a. -/
noncomputable def agree (d : Sentence W) (ctx : Context W) : Prop :=
  ∃ α ∈ Core.Question.alt ctx.qud,
    fullSupportS ctx.dox d.sDen ctx.prior α ∧
    fullSupportS ctx.dox d.s'Den ctx.prior α

open Classical in
/-- Disagreement: S and S' disagree w.r.t. the QUD iff they each support
some answer but do not agree on any single answer.

@cite{ippolito-kiss-williams-2025} Def. 14b. -/
noncomputable def disagree (d : Sentence W) (ctx : Context W) : Prop :=
  (∃ α ∈ Core.Question.alt ctx.qud, fullSupportS ctx.dox d.sDen ctx.prior α) ∧
  (∃ α ∈ Core.Question.alt ctx.qud, fullSupportS ctx.dox d.s'Den ctx.prior α) ∧
  ¬ d.agree ctx

end Sentence

-- Theorems

/-- At-issue content is intersection of informational content. -/
theorem atIssue_is_intersection {W : Type*} [Fintype W] (d : Sentence W) :
    d.atIssueContent = d.sDen.info ∩ d.s'Den.info := rfl

/-- Interrogative left argument is blocked by the doxastic condition.

When the speaker doesn't believe any alternative of S (DOX_sp ⊄ q for all
q ∈ alt(⟦S⟧)), `fullSupportS` fails for every answer.

This derives the restriction from the architecture of SUPPORT rather than
stipulating it as a clause-type filter. Biased/rhetorical questions, where
the speaker DOES believe an answer, correctly pass this check. -/
theorem interrogative_blocks_support {W : Type*} [Fintype W]
    (dox : Set W) (sentDen : Core.Question W) (prior : Prior W)
    (answer : Set W)
    (hNoBelief : ∀ q ∈ Core.Question.alt sentDen, ¬ (dox ⊆ q)) :
    ¬ fullSupportS dox sentDen prior answer :=
  fullSupport_fails_unbelievedS dox sentDen prior answer hNoBelief

/-- Interrogative prejacents trivially satisfy the CI's condition (ii):
when S' is an info-seeking question whose speaker doesn't believe any
answer, `fullSupportS` fails for S' on every α, so `¬ fullSupportS ... =
True`. This captures IKW §5.2's observation that S' can be interrogative. -/
theorem interrogative_prejacent_satisfies_ci_condition {W : Type*} [Fintype W]
    (dox : Set W) (s'Den : Core.Question W) (prior : Prior W)
    (α : Set W)
    (hNoBelief : ∀ q ∈ Core.Question.alt s'Den, ¬ (dox ⊆ q)) :
    ¬ fullSupportS dox s'Den prior α :=
  fullSupport_fails_unbelievedS dox s'Den prior α hNoBelief

/-- Weak non-agreement: when S' can't support any answer, S and S' neither
agree nor disagree — they "merely don't agree" (@cite{ippolito-kiss-williams-2025} p. 227).

When S' is an info-seeking question, `fullSupportS` fails for S' on every α
(doxastic failure). So `agree` is false (no joint support possible) AND
`disagree` is false (disagree requires S' to support *some* answer).
The result is non-agreement without disagreement — a weaker relation than
the active clash seen with declarative S'.

Example (IKW ex. 18): "The house is beautiful, only can we afford it?"
→ S supports "buy the house", S' doesn't support anything
→ Not agreement, not disagreement: just weak non-agreement -/
theorem weak_non_agreement {W : Type*} [Fintype W]
    (d : Sentence W) (ctx : Context W)
    (hS'noSupport : ∀ α ∈ Core.Question.alt ctx.qud,
      ¬ fullSupportS ctx.dox d.s'Den ctx.prior α) :
    ¬ d.agree ctx ∧ ¬ d.disagree ctx := by
  refine ⟨?_, ?_⟩
  · -- ¬ agree: S' can't support any α, so no joint support
    rintro ⟨α, hMem, _, hS'⟩
    exact hS'noSupport α hMem hS'
  · -- ¬ disagree: S' can't support any α, so second conjunct fails
    rintro ⟨_, ⟨α, hMem, hS'⟩, _⟩
    exact hS'noSupport α hMem hS'

/-- Disagreement implies CI content when partial answers are empty.

If S and S' disagree (each supports some answer but don't agree on any
single answer) and there are no prior partial answers, then the CI is
automatically satisfied.

Proof: `disagree` gives us (1) ∃α: fullSupportS S α, (2) ∃β: fullSupportS S' β,
(3) ¬agree = for all γ, ¬(fullSupportS S γ ∧ fullSupportS S' γ). Taking α from
(1), fullSupportS S α holds. By (3), ¬fullSupportS S' α. With empty partial
answers, condition (i) is vacuous. So α witnesses the CI.

This captures the paper's core insight: when S and S' evidentially clash
(disagree), the CI is inherently satisfied. -/
theorem disagree_implies_ciContent_empty_partial {W : Type*} [Fintype W]
    (d : Sentence W) (ctx : Context W)
    (hDisagree : d.disagree ctx)
    (hPartial : ctx.partialAnswers = []) :
    d.ciContent ctx := by
  obtain ⟨⟨α, hMem, hSupp⟩, _, hNotAgree⟩ := hDisagree
  refine ⟨α, hMem, ?_, hSupp, ?_⟩
  · intro p hp
    rw [hPartial] at hp
    simp at hp
  · -- From ¬agree: no α has both S and S' supporting it; in particular this α.
    intro hS'
    exact hNotAgree ⟨α, hMem, hSupp, hS'⟩

end Pragmatics.Particles.DiscourseOnly
