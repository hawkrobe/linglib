import Linglib.Theories.Semantics.Questions.Support
import Linglib.Theories.Semantics.Lexical.Expressives.Basic

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
- At-issue: ⟨⟦S⟧^c, ⟦S'⟧^c⟩ (pair of denotations; for declaratives, modeled
  as conjunction of highlighted content)
- CI: ∃α ∈ QUD s.t. (i) every true partial answer p ∉ QUD supports α,
  and (ii) S' does not support α

## Key Predictions

- **Interrogative left-arg restriction** (§5.2): Canonical info-seeking questions
  cannot be the left argument because the speaker doesn't believe any answer,
  so DOX_sp ⊆ q fails for all q, and SUPPORT fails. This falls out from
  `fullSupport_fails_unbelieved` in Support.lean — no stipulation needed.
- **Biased/rhetorical questions CAN be left args** (§5.2, exx. 20–21): These
  questions have a believed answer (DOX_sp ⊆ q for some q), so the doxastic
  condition is satisfied.
- **Comparison with *but*** (§6): Both express contrast, but *only*'s right
  argument only needs to fail to support (¬SUPPORT), not actively counter-support
  (negRelevant). This makes *only* strictly weaker than *but*.

-/

namespace Semantics.Lexical.Particle.DiscourseOnly

open Discourse
open Semantics.Questions.ProbabilisticAnswerhood
open Semantics.Questions.Support
open Semantics.Lexical.Expressives

-- Context

/-- Discourse context for evaluating discourse *only*.

Includes the QUD, a prior distribution, the speaker's doxastic state, and
a record of true partial answers to the QUD established in prior discourse.

The doxastic state is what makes the interrogative restriction fall out
naturally: canonical info-seeking questions fail the doxastic condition
of SUPPORT (the speaker doesn't believe any answer). -/
structure Context (W : Type*) [Fintype W] where
  /-- The QUD as an inquisitive issue -/
  qud : Issue W
  /-- Prior probability distribution -/
  prior : Prior W
  /-- Speaker's doxastic state DOX_sp -/
  dox : InfoState W
  /-- Worlds for evaluating doxastic subset checks -/
  worlds : List W
  /-- True partial answers to the QUD established in prior discourse.

  @cite{ippolito-kiss-williams-2025} Def. 16 CI condition (i) quantifies universally over ALL true
  partial answers p ∉ QUD: each must support the same α. We track these
  explicitly so the CI can check the universal condition. -/
  partialAnswers : List (W → Bool)
  /-- Subquestions of the QUD established by the discourse context.

  @cite{roberts-2012} Def. 8–9: q is a subquestion of Q iff answering Q
  (contextually) entails a complete answer to q. @cite{ippolito-kiss-williams-2025} §5.1:
  "Answering this question requires answering its plausible subquestions,
  such as *Is the house beautiful? Is the house expensive?*"

  These are provided by the discourse context, not computed: the contextual
  entailment relation depends on common ground assumptions (e.g., beauty
  is a criterion for buying). -/
  subquestions : List (Issue W)

-- Sentence

/-- A discourse *only* sentence with two clausal arguments.

`sDen` is the inquisitive denotation of the left argument S,
`s'Den` is the inquisitive denotation of the right argument S'.

For declaratives, each `Issue` has a single alternative (the propositional
content). For questions, each `Issue` has multiple alternatives. The
denotation type is uniform — what varies is whether the doxastic condition
of SUPPORT can be satisfied. -/
structure Sentence (W : Type*) where
  /-- Inquisitive denotation of the left argument S -/
  sDen : Issue W
  /-- Inquisitive denotation of the right argument S' -/
  s'Den : Issue W

namespace Sentence

variable {W : Type*} [Fintype W]

/-- At-issue content of "S only S'".

@cite{ippolito-kiss-williams-2025} Def. 16: the at-issue content is the pair ⟨⟦S⟧, ⟦S'⟧⟩.
For declarative arguments, we model this as conjunction of the highlighted
(informational) content of each denotation: every world where both S and S'
are informatively true. -/
def atIssueContent (d : Sentence W) : W → Bool :=
  λ w => d.sDen.highlighted w && d.s'Den.highlighted w

/-- Presupposition / definedness condition for discourse *only*.

@cite{ippolito-kiss-williams-2025} Def. 16: ⟦S [only S']⟧ is defined only if S and S' are
"relevant" to the QUD and ∃α ∈ QUD s.t. S supports α.

Relevance is structural, following @cite{roberts-2012} Def. 15 and IKW
assumption iii (p. 225): "S is relevant to QUD if S is either a
subquestion of QUD or an answer to a subquestion q of QUD."

We decompose the presupposition into three conditions:

1. **S is structurally relevant**: some alternative of S partially answers
   the QUD or a subquestion of the QUD (via `Discourse.moveRelevant`).

2. **S' is structurally relevant**: same check for the right argument.

3. **S supports some answer α** via `fullSupport` (doxastic + probabilistic).
   This is where the interrogative left-argument restriction falls out: the
   doxastic condition (Def. 13) blocks info-seeking questions from supporting
   any answer. -/
def isDefined (d : Sentence W) (ctx : Context W) : Bool :=
  -- S is relevant to the QUD (Roberts 2012 Def. 15 / IKW assumption iii)
  moveRelevant d.sDen ctx.qud ctx.subquestions ctx.worlds &&
  -- S' is relevant to the QUD
  moveRelevant d.s'Den ctx.qud ctx.subquestions ctx.worlds &&
  -- ∃α ∈ QUD s.t. S supports α (IKW Def. 16)
  ctx.qud.alternatives.any λ α =>
    fullSupport ctx.dox d.sDen ctx.prior α ctx.worlds

/-- CI content of discourse *only*.

@cite{ippolito-kiss-williams-2025} Def. 16 CI: ∃α ∈ QUD s.t.
(i) ∀p ∈ partialAnswers, p supports α (all prior discourse points toward α)
(ii) S' does not SUPPORT α (the right argument fails to support that direction)

Condition (i) captures the universal quantification over true partial answers.
When partialAnswers is empty, condition (i) is vacuously true, which is correct:
the CI only requires that no prior evidence contradicts the direction.

The "S supports α" condition is implicit in `isDefined` — if the CI is being
evaluated, S already established the direction. -/
def ciContent (d : Sentence W) (ctx : Context W) : Bool :=
  ctx.qud.alternatives.any λ α =>
    -- (i) All true partial answers support α.
    -- We use `probSupports` (probabilistic only) rather than `fullSupport` here
    -- because partial answers are propositions already established in discourse —
    -- the speaker has committed to believing them, so the doxastic condition
    -- (DOX_sp ⊆ q) is trivially satisfied for any established partial answer.
    ctx.partialAnswers.all (λ p => probSupports ctx.prior p α) &&
    -- S itself supports α (part of establishing the direction)
    fullSupport ctx.dox d.sDen ctx.prior α ctx.worlds &&
    -- (ii) S' does NOT support α
    !fullSupport ctx.dox d.s'Den ctx.prior α ctx.worlds

/-- Full two-dimensional meaning of "S only S'".

Combines at-issue content (conjunction of highlighted content) with CI content
(S' fails to support an answer that S and prior discourse support). Uses
@cite{potts-2005}'s `TwoDimProp` to keep the dimensions independent. -/
def meaning (d : Sentence W) (ctx : Context W) : TwoDimProp W :=
  { atIssue := d.atIssueContent
  , ci := λ _ => d.ciContent ctx }

/-- Agreement: S and S' agree w.r.t. the QUD iff there is a proposition
α ∈ QUD s.t. both S and S' fully support α.

@cite{ippolito-kiss-williams-2025} Def. 14a. -/
def agree (d : Sentence W) (ctx : Context W) : Bool :=
  ctx.qud.alternatives.any λ α =>
    fullSupport ctx.dox d.sDen ctx.prior α ctx.worlds &&
    fullSupport ctx.dox d.s'Den ctx.prior α ctx.worlds

/-- Disagreement: S and S' disagree w.r.t. the QUD iff they each support
some answer but do not agree on any single answer.

@cite{ippolito-kiss-williams-2025} Def. 14b. -/
def disagree (d : Sentence W) (ctx : Context W) : Bool :=
  (ctx.qud.alternatives.any λ α =>
    fullSupport ctx.dox d.sDen ctx.prior α ctx.worlds) &&
  (ctx.qud.alternatives.any λ α =>
    fullSupport ctx.dox d.s'Den ctx.prior α ctx.worlds) &&
  !d.agree ctx

end Sentence

-- Theorems

/-- At-issue content is conjunction of highlighted content. -/
theorem atIssue_is_conjunction {W : Type*} (d : Sentence W) :
    d.atIssueContent = λ w => d.sDen.highlighted w && d.s'Den.highlighted w := rfl

/-- CI projects through negation (inherited from TwoDimProp).

Negating "S only S'" negates the at-issue conjunction but the CI
(S' fails to support the direction) still holds. -/
theorem ci_projects_neg {W : Type*} [Fintype W]
    (d : Sentence W) (ctx : Context W) :
    (TwoDimProp.neg (d.meaning ctx)).ci = (d.meaning ctx).ci := rfl

/-- Interrogative left argument is blocked by the doxastic condition.

When the speaker doesn't believe any alternative of S (DOX_sp ⊄ q for all
q ∈ ⟦S⟧), SUPPORT fails for every answer r. This blocks `isDefined`,
because no α ∈ QUD can be supported.

This derives the restriction from the architecture of SUPPORT rather than
stipulating it as a clause-type filter. Biased/rhetorical questions, where
the speaker DOES believe an answer, correctly pass this check. -/
theorem interrogative_blocks_support {W : Type*} [Fintype W]
    (dox : InfoState W) (sentDen : Issue W) (prior : Prior W)
    (answer : W → Bool) (worlds : List W)
    (hNoBelief : ∀ q, q ∈ sentDen.alternatives →
      Discourse.supports dox q worlds = false) :
    fullSupport dox sentDen prior answer worlds = false :=
  fullSupport_fails_unbelieved dox sentDen prior answer worlds hNoBelief

/-- Interrogative prejacents trivially satisfy the CI's condition (ii).

When S' is an info-seeking question whose speaker doesn't believe any answer,
fullSupport fails for S', so ¬fullSupport ctx.dox d.s'Den... = true. The
prejacent "automatically" fails to support any direction, which is why
interrogative prejacents are typically fine cross-linguistically.

This captures IKW §5.2's observation that S' can be interrogative. -/
theorem interrogative_prejacent_satisfies_ci_condition {W : Type*} [Fintype W]
    (dox : InfoState W) (s'Den : Issue W) (prior : Prior W)
    (α : W → Bool) (worlds : List W)
    (hNoBelief : ∀ q, q ∈ s'Den.alternatives →
      Discourse.supports dox q worlds = false) :
    !fullSupport dox s'Den prior α worlds = true := by
  rw [fullSupport_fails_unbelieved dox s'Den prior α worlds hNoBelief]
  rfl

/-- Weak non-agreement: when S' can't support any answer, S and S' neither
agree nor disagree — they "merely don't agree" (IKW 2025 p. 227).

This captures a key prediction about interrogative prejacents. When S' is
an info-seeking question, fullSupport fails for S' on every α (doxastic
failure). So `agree` = false (S' can't jointly support any α with S) AND
`disagree` = false (disagree requires S' to support *some* answer, which
it can't). The result is non-agreement without disagreement — a weaker
relation than the active clash seen with declarative S'.

Example (IKW ex. 18): "The house is beautiful, only can we afford it?"
→ S supports "buy the house", S' doesn't support anything
→ Not agreement, not disagreement: just weak non-agreement -/
theorem weak_non_agreement {W : Type*} [Fintype W]
    (d : Sentence W) (ctx : Context W)
    (hS'noSupport : ∀ α, α ∈ ctx.qud.alternatives →
      fullSupport ctx.dox d.s'Den ctx.prior α ctx.worlds = false) :
    d.agree ctx = false ∧ d.disagree ctx = false := by
  constructor
  · -- agree = false: S' can't support any α, so no joint support
    unfold Sentence.agree
    rw [List.any_eq_false]
    intro α hMem
    rw [hS'noSupport α hMem]
    simp
  · -- disagree = false: S' can't support any α, so second conjunct fails
    unfold Sentence.disagree
    have hNoS' : (ctx.qud.alternatives.any λ α =>
        fullSupport ctx.dox d.s'Den ctx.prior α ctx.worlds) = false := by
      rw [List.any_eq_false]
      intro α hMem
      rw [hS'noSupport α hMem]
      simp
    rw [hNoS']
    simp

/-- Disagreement implies CI content when partial answers are empty.

If S and S' disagree (each supports some answer but don't agree on any
single answer) and there are no prior partial answers, then the CI is
automatically satisfied.

Proof: `disagree = true` gives us (1) ∃α: fullSupport S α = true,
(2) ∃β: fullSupport S' β = true, (3) ¬agree = for all γ,
¬(fullSupport S γ ∧ fullSupport S' γ). Taking α from (1), fullSupport S α
is true. By (3), fullSupport S' α must be false. With empty partial answers,
condition (i) is vacuous. So α witnesses the CI.

This captures the paper's core insight: when S and S' evidentially clash
(disagree), the CI is inherently satisfied. -/
theorem disagree_implies_ciContent_empty_partial {W : Type*} [Fintype W]
    (d : Sentence W) (ctx : Context W)
    (hDisagree : d.disagree ctx = true)
    (hPartial : ctx.partialAnswers = []) :
    d.ciContent ctx = true := by
  unfold Sentence.disagree at hDisagree
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hDisagree
  obtain ⟨⟨hSsupports, _⟩, hNotAgree⟩ := hDisagree
  unfold Sentence.ciContent
  rw [List.any_eq_true] at hSsupports ⊢
  obtain ⟨α, hMem, hSupp⟩ := hSsupports
  refine ⟨α, hMem, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', hPartial, List.all_nil, true_and]
  refine ⟨hSupp, ?_⟩
  -- From ¬agree: for all α, ¬(fullSupport S α ∧ fullSupport S' α)
  unfold Sentence.agree at hNotAgree
  rw [List.any_eq_false] at hNotAgree
  have h := hNotAgree α hMem
  simp only [Bool.and_eq_true] at h
  -- h : ¬(fullSupport S α = true ∧ fullSupport S' α = true)
  -- hSupp : fullSupport S α = true
  -- Goal : fullSupport S' α = false
  cases hS' : fullSupport ctx.dox d.s'Den ctx.prior α ctx.worlds
  · rfl
  · exfalso; exact h ⟨hSupp, hS'⟩

end Semantics.Lexical.Particle.DiscourseOnly
