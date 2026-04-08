import Linglib.Core.Discourse.QUD
import Linglib.Core.Discourse.AtIssueness
import Linglib.Core.Partition
import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin

/-!
# @cite{roberts-2012} — Information Structure in Discourse

Roberts (1996/2012) "Information structure in discourse: Towards an integrated
formal theory of pragmatics" (Semantics & Pragmatics 5(6): 1–69).

## Core Contributions Formalized

1. **QUD stack** — discourse state is an ordered stack of accepted, unanswered
   questions (`QUDStack`), not a single QUD.
2. **Strategy of inquiry** — recursive question decomposition (`Strategy`):
   answering all subquestions answers the parent.
3. **Negative partial answerhood** — a proposition partially answers a question
   by ruling out an alternative, not just confirming one (`partiallyAnswers`).
4. **Q-A congruence** — the focus alternatives of an answer equal the QUD
   alternatives (grounded by the Rooth–Hamblin type identity).
5. **Issue → QUD bridge** — `Issue.toQUD` converts between the two question
   representations, connecting to gradient at-issueness (`atIssuenessFromQUD`).

## D₀ Worked Example (Roberts §1.2)

The Big Question: "What did each person eat?"

- 4 Boolean dimensions: Hannah-beans, Hannah-tofu, Roger-beans, Roger-tofu
- 16 possible worlds
- 7 questions forming a strategy tree

```
         q₁ (What did everyone eat?)
        /                            \
    q_a (What did Hannah eat?)    q_b (What did Roger eat?)
    /        \                    /        \
q_ai (H beans?) q_aii (H tofu?) q_bi (R beans?) q_bii (R tofu?)
```
-/

namespace Phenomena.Focus.Studies.Roberts2012

open Discourse

-- ════════════════════════════════════════════════════
-- § D₀ World Space
-- ════════════════════════════════════════════════════

/-- A world in the D₀ scenario: 4 independent Boolean facts. -/
structure D0World where
  hb : Bool   -- Hannah ate beans
  ht : Bool   -- Hannah ate tofu
  rb : Bool   -- Roger ate beans
  rt : Bool   -- Roger ate tofu
  deriving DecidableEq, BEq, Repr

private def bools : List Bool := [false, true]

/-- All 16 possible worlds. -/
def allWorlds : List D0World :=
  bools.flatMap λ hb => bools.flatMap λ ht =>
  bools.flatMap λ rb => bools.map λ rt => ⟨hb, ht, rb, rt⟩

theorem allWorlds_length : allWorlds.length = 16 := by native_decide

-- ════════════════════════════════════════════════════
-- § Atomic Propositions
-- ════════════════════════════════════════════════════

/-- Hannah ate the beans. -/
def hannahBeans : D0World → Bool := D0World.hb
/-- Hannah ate the tofu. -/
def hannahTofu : D0World → Bool := D0World.ht
/-- Roger ate the beans. -/
def rogerBeans : D0World → Bool := D0World.rb
/-- Roger ate the tofu. -/
def rogerTofu : D0World → Bool := D0World.rt

-- ════════════════════════════════════════════════════
-- § Questions as Issues (derived from Issue constructors)
-- ════════════════════════════════════════════════════

/-- "Did Hannah eat the beans?" — derived from `Issue.polar`. -/
def q_ai : Issue D0World := Issue.polar hannahBeans

/-- "Did Hannah eat the tofu?" -/
def q_aii : Issue D0World := Issue.polar hannahTofu

/-- "Did Roger eat the beans?" -/
def q_bi : Issue D0World := Issue.polar rogerBeans

/-- "Did Roger eat the tofu?" -/
def q_bii : Issue D0World := Issue.polar rogerTofu

/-- "What did Hannah eat?" — partitioned by ⟨hb, ht⟩ values.
    4 alternatives: beans-only, tofu-only, both, neither. -/
def q_a : Issue D0World := ⟨[
  fun w => w.hb && !w.ht,    -- beans only
  fun w => !w.hb && w.ht,    -- tofu only
  fun w => w.hb && w.ht,     -- both
  fun w => !w.hb && !w.ht    -- neither
]⟩

/-- "What did Roger eat?" — partitioned by ⟨rb, rt⟩ values. -/
def q_b : Issue D0World := ⟨[
  fun w => w.rb && !w.rt,
  fun w => !w.rb && w.rt,
  fun w => w.rb && w.rt,
  fun w => !w.rb && !w.rt
]⟩

/-- Count how many alternatives in an issue are true at world w. -/
private def countTrue (q : Issue D0World) (w : D0World) : Nat :=
  q.alternatives.foldl (fun n alt => if alt w then n + 1 else n) 0

/-- q_a is a genuine partition: every world satisfies exactly one alternative. -/
theorem qa_partition : allWorlds.all (fun w => countTrue q_a w == 1) = true := by native_decide

/-- q_b is a genuine partition: every world satisfies exactly one alternative. -/
theorem qb_partition : allWorlds.all (fun w => countTrue q_b w == 1) = true := by native_decide

/-- "What did everyone eat?" — the Big Question.
    Derived compositionally as the intersection of q_a and q_b:
    knowing what everyone ate = knowing what Hannah ate AND what Roger ate. -/
def q_1 : Issue D0World := q_a.inter q_b allWorlds

-- ════════════════════════════════════════════════════
-- § Question Entailment (@cite{roberts-2012} Def. 8)
-- ════════════════════════════════════════════════════

/-- The Big Question entails "What did Hannah eat?" -/
theorem q1_entails_qa : questionEntails q_1 q_a allWorlds = true := by native_decide

/-- The Big Question entails "What did Roger eat?" -/
theorem q1_entails_qb : questionEntails q_1 q_b allWorlds = true := by native_decide

/-- "What did Hannah eat?" entails "Did Hannah eat the beans?" -/
theorem qa_entails_qai : questionEntails q_a q_ai allWorlds = true := by native_decide

/-- "What did Hannah eat?" entails "Did Hannah eat the tofu?" -/
theorem qa_entails_qaii : questionEntails q_a q_aii allWorlds = true := by native_decide

/-- "What did Roger eat?" entails "Did Roger eat the beans?" -/
theorem qb_entails_qbi : questionEntails q_b q_bi allWorlds = true := by native_decide

/-- "What did Roger eat?" entails "Did Roger eat the tofu?" -/
theorem qb_entails_qbii : questionEntails q_b q_bii allWorlds = true := by native_decide

-- Entailment is asymmetric: subquestions do NOT entail their parents.

/-- q_a does NOT entail q_1: knowing what Hannah ate doesn't tell you
    what everyone ate. -/
theorem qa_not_entails_q1 : questionEntails q_a q_1 allWorlds = false := by native_decide

/-- q_ai does NOT entail q_a: knowing whether Hannah ate beans doesn't
    tell you what Hannah ate overall. -/
theorem qai_not_entails_qa : questionEntails q_ai q_a allWorlds = false := by native_decide

-- ════════════════════════════════════════════════════
-- § Subquestions (@cite{roberts-2012} Def. 8–9)
-- ════════════════════════════════════════════════════

/-- q_a is a subquestion of q_1. -/
theorem qa_sub_q1 : isSubquestion q_a q_1 allWorlds = true := q1_entails_qa

/-- q_b is a subquestion of q_1. -/
theorem qb_sub_q1 : isSubquestion q_b q_1 allWorlds = true := q1_entails_qb

-- ════════════════════════════════════════════════════
-- § Strategy of Inquiry (@cite{roberts-2012} Def. 12)
-- ════════════════════════════════════════════════════

/-- Roberts' strategy for the D₀ scenario:
    Answer q_1 by answering q_a and q_b;
    answer q_a by answering q_ai and q_aii;
    answer q_b by answering q_bi and q_bii. -/
def strat_1 : Strategy D0World :=
  .branch q_1 [
    .branch q_a [.leaf q_ai, .leaf q_aii],
    .branch q_b [.leaf q_bi, .leaf q_bii]
  ]

/-- The strategy has 7 questions total. -/
theorem strat_1_count : strat_1.allQuestions.length = 7 := by native_decide

/-- The root of the strategy is complete: answering "What did Hannah eat?"
    and "What did Roger eat?" answers "What did everyone eat?" -/
theorem strat_1_root_complete : strat_1.isComplete allWorlds = true := by native_decide

/-- The q_a sub-strategy is complete: answering the two polar questions
    about Hannah answers "What did Hannah eat?" -/
theorem strat_1_qa_complete :
    (Strategy.branch q_a [.leaf q_ai, .leaf q_aii]).isComplete allWorlds = true := by
  native_decide

/-- The q_b sub-strategy is complete. -/
theorem strat_1_qb_complete :
    (Strategy.branch q_b [.leaf q_bi, .leaf q_bii]).isComplete allWorlds = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § QUD Stack Traces
-- ════════════════════════════════════════════════════

/-- Initial state: push the Big Question. -/
def stack_0 : QUDStack D0World := QUDStack.empty.push q_1

/-- Pursue Hannah's food: push q_a. -/
def stack_1 : QUDStack D0World := stack_0.push q_a

/-- Pursue Hannah+beans: push q_ai. -/
def stack_2 : QUDStack D0World := stack_1.push q_ai

/-- "Hannah ate the beans" answers q_ai: pop. -/
def stack_3 : QUDStack D0World := stack_2.pop

/-- Stack depths trace the discourse. -/
theorem stack_depths :
    stack_0.depth = 1 ∧ stack_1.depth = 2 ∧
    stack_2.depth = 3 ∧ stack_3.depth = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- After popping q_ai, the immediate QUD is q_a. -/
theorem stack_3_qud : stack_3.immediateQUD = some q_a := rfl

-- ════════════════════════════════════════════════════
-- § Negative Partial Answerhood
-- ════════════════════════════════════════════════════

/-- "Hannah didn't eat beans" (¬hb) negatively partially answers "Did Hannah
    eat beans?" — it rules out the hb alternative.

    This exercises the fixed `partiallyAnswers` (negative answerhood branch). -/
theorem neg_hb_partially_answers_qai :
    partiallyAnswers (fun w => !w.hb) q_ai allWorlds = true := by native_decide

/-- "Hannah didn't eat beans" also partially answers "What did Hannah eat?"
    by ruling out the beans-only and both alternatives. -/
theorem neg_hb_partially_answers_qa :
    partiallyAnswers (fun w => !w.hb) q_a allWorlds = true := by native_decide

-- ════════════════════════════════════════════════════
-- § Positive Partial Answerhood
-- ════════════════════════════════════════════════════

/-- "Hannah ate beans" positively partially answers q_ai. -/
theorem hb_partially_answers_qai :
    partiallyAnswers hannahBeans q_ai allWorlds = true := by native_decide

/-- "Hannah ate beans" partially answers the Big Question. -/
theorem hb_partially_answers_q1 :
    partiallyAnswers hannahBeans q_1 allWorlds = true := by native_decide

-- ════════════════════════════════════════════════════
-- § Relevance (@cite{roberts-2012} Def. 15)
-- ════════════════════════════════════════════════════

/-- "Hannah ate beans" is relevant to q_1 (the Big Question)
    as a single-alternative assertion. -/
def hannahBeans_assertion : Issue D0World := ⟨[hannahBeans]⟩

theorem hannahBeans_relevant_to_q1 :
    moveRelevant hannahBeans_assertion q_1 [] allWorlds = true := by native_decide

/-- q_a is relevant to q_1 as a subquestion: each of q_a's alternatives
    partially answers q_1. -/
theorem qa_relevant_to_q1 :
    moveRelevant q_a q_1 [] allWorlds = true := by native_decide

/-- "Hannah ate beans" is relevant to the entire D₀ strategy. -/
theorem hannahBeans_relevant_to_strategy :
    moveRelevantToStrategy hannahBeans_assertion strat_1 allWorlds = true := by native_decide

-- ════════════════════════════════════════════════════
-- § Q-A Congruence / Focus Type Identity
-- ════════════════════════════════════════════════════

/-- The Rooth–Hamblin type identity grounds Q-A congruence:
    propositional focus values and Hamblin question denotations are the
    same type. @cite{rooth-1992}, @cite{roberts-2012} Def. 25. -/
theorem focus_question_type_identity :
    Semantics.FocusInterpretation.PropFocusValue D0World =
    Semantics.Questions.Hamblin.QuestionDen D0World := rfl

-- ════════════════════════════════════════════════════
-- § Issue → QUD Bridge + At-Issueness
-- ════════════════════════════════════════════════════

/-- Convert "What did Hannah eat?" to a QUD equivalence relation via `Issue.toQUD`.
    Two worlds are equivalent iff they agree on all q_a alternatives (same ⟨hb, ht⟩). -/
def qa_qud : QUD D0World := q_a.toQUD "qa"

/-- "Roger ate beans" is at-issue relative to q_a: it varies within q_a's
    partition cells (worlds with the same Hannah-food can differ on Roger-food).

    `atIssuenessFromQUD` (@cite{tonhauser-beaver-degen-2018}) measures whether
    content provides information beyond what the QUD resolves. Content that
    varies within QUD cells is not yet settled by the QUD answer. -/
theorem rogerBeans_at_issue_wrt_qa :
    Core.Discourse.AtIssueness.isAtIssue
      (Core.Discourse.AtIssueness.atIssuenessFromQUD qa_qud rogerBeans allWorlds)
      Core.Discourse.AtIssueness.defaultThreshold = true := by native_decide

/-- "Hannah ate beans" is NOT at-issue relative to q_a: it is already resolved
    by q_a's partition (constant within each cell). -/
theorem hannahBeans_not_at_issue_wrt_qa :
    Core.Discourse.AtIssueness.isAtIssue
      (Core.Discourse.AtIssueness.atIssuenessFromQUD qa_qud hannahBeans allWorlds)
      Core.Discourse.AtIssueness.defaultThreshold = false := by native_decide

-- ════════════════════════════════════════════════════
-- § Issue ↔ QUD Bridge Verification
-- ════════════════════════════════════════════════════

-- D₀ questions are genuine partitions (verified via `isPartition`).

/-- q_a is a partition of allWorlds. -/
theorem qa_isPartition : q_a.isPartition allWorlds = true := by native_decide

/-- q_b is a partition of allWorlds. -/
theorem qb_isPartition : q_b.isPartition allWorlds = true := by native_decide

/-- q_ai (polar) is a partition of allWorlds. -/
theorem qai_isPartition : q_ai.isPartition allWorlds = true := by native_decide

/-- q_1 (Big Question) is a partition of allWorlds. -/
theorem q1_isPartition : q_1.isPartition allWorlds = true := by native_decide

-- The bridge: refinesOn and questionEntails agree on D₀ partitions.
-- These concrete instances verify the general theorem
-- `refinesOn_iff_questionEntails_of_partition` (Core/Partition.lean).

/-- Partition refinement = question entailment: q_1 → q_a. -/
theorem bridge_q1_qa :
    refinesOn (q_1.toQUD) (q_a.toQUD) allWorlds =
    questionEntails q_1 q_a allWorlds := by native_decide

/-- Partition refinement = question entailment: q_1 → q_b. -/
theorem bridge_q1_qb :
    refinesOn (q_1.toQUD) (q_b.toQUD) allWorlds =
    questionEntails q_1 q_b allWorlds := by native_decide

/-- Partition refinement = question entailment: q_a → q_ai. -/
theorem bridge_qa_qai :
    refinesOn (q_a.toQUD) (q_ai.toQUD) allWorlds =
    questionEntails q_a q_ai allWorlds := by native_decide

/-- Asymmetric: q_a does NOT refine q_1 (matching qa_not_entails_q1). -/
theorem bridge_qa_q1 :
    refinesOn (q_a.toQUD) (q_1.toQUD) allWorlds =
    questionEntails q_a q_1 allWorlds := by native_decide

/-- Round-trip: toIssue ∘ toQUD recovers the same number of alternatives
    as the original partition for q_a (4 cells). -/
theorem toIssue_roundtrip_qa_cells :
    ((q_a.toQUD).toIssue allWorlds).alternatives.length = 4 := by native_decide

/-- Round-trip: toIssue ∘ toQUD recovers 16 cells for the Big Question
    (one per world — finest partition). -/
theorem toIssue_roundtrip_q1_cells :
    ((q_1.toQUD).toIssue allWorlds).alternatives.length = 16 := by native_decide

/-- Round-trip: toIssue ∘ toQUD recovers 2 cells for polar q_ai. -/
theorem toIssue_roundtrip_qai_cells :
    ((q_ai.toQUD).toIssue allWorlds).alternatives.length = 2 := by native_decide

end Phenomena.Focus.Studies.Roberts2012
