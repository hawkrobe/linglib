import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Entailment
import Linglib.Semantics.Questions.Resolution

/-!
# Questions under discussion: stack and strategy
[roberts-2012]

The inquiry coordinate of the conversational scoreboard: the stack of
accepted-but-unanswered questions (head is the immediate QUD;
subquestions push, answers pop), the rose-tree strategy of inquiry
decomposing a question into subquestions whose joint resolution answers
the parent, and relevance of a move to the inquiry (`moveRelevant`,
`moveRelevantToStrategy`).

## Fidelity notes

`moveRelevant` is existential answerhood relevance: the partial-answer
clause of [roberts-2012]'s Relevance (15), weaker than her strategy
clause for interrogative moves. It is the proxy
[ippolito-kiss-williams-2025] use for their relevance assumption (iii),
consumed by the discourse *only* definedness condition in their (16).
That the `subquestions` argument really lists subquestions of the QUD is
the caller's obligation.
-/

namespace Discourse

/-- A QUD stack: ordered list of accepted, unanswered questions
    (Roberts 2012 Def 10g). -/
structure QUDStack (W : Type*) where
  questions : List (Question W)

namespace QUDStack

variable {W : Type*}

/-- Empty QUD stack (discourse initial state). -/
def empty : QUDStack W := ⟨[]⟩

/-- The immediate QUD: the most recently accepted, unanswered question. -/
def immediateQUD (s : QUDStack W) : Option (Question W) := s.questions.head?

/-- Accept a new question: push onto the stack. -/
def push (s : QUDStack W) (q : Question W) : QUDStack W := ⟨q :: s.questions⟩

/-- Answer the immediate QUD: pop from the stack. -/
def pop (s : QUDStack W) : QUDStack W := ⟨s.questions.tail⟩

/-- Current depth of the QUD stack. -/
def depth (s : QUDStack W) : Nat := s.questions.length

end QUDStack

open Question

/-- A strategy of inquiry as a rose tree: each node a question, children
    subquestions whose joint resolution answers the parent (Roberts Def 12). -/
inductive Strategy (W : Type*) where
  | leaf : Question W → Strategy W
  | branch : Question W → List (Strategy W) → Strategy W

namespace Strategy

variable {W : Type*}

/-- The question at the root of this (sub)strategy. -/
def question : Strategy W → Question W
  | .leaf q | .branch q _ => q

/-- Immediate substrategies (empty for leaves). -/
def substrategies : Strategy W → List (Strategy W)
  | .leaf _ => []
  | .branch _ ss => ss

/-- All questions in the strategy (root + all descendants). -/
def allQuestions : Strategy W → List (Question W)
  | .leaf q => [q]
  | .branch q ss => q :: ss.flatMap allQuestions

/-- Leaf questions only (terminal nodes of the strategy). -/
def leaves : Strategy W → List (Question W)
  | .leaf q => [q]
  | .branch _ ss => ss.flatMap leaves

/-- A strategy is complete at a single level: the meet of children's
    questions entails the parent. Recurse on substrategies for full-tree
    verification. -/
def isComplete : Strategy W → Prop
  | .leaf _ => True
  | .branch q children =>
    let combined := (children.map (·.question)).foldl (· ⊓ ·) ⊤
    combined.Entails q

end Strategy

variable {W : Type*}

/-- A move is relevant if one of its alternatives partially answers the
QUD or one of the subquestions. -/
def moveRelevant (den qud : Question W) (subquestions : List (Question W)) : Prop :=
  ∃ a ∈ Question.alt den,
    Question.PartiallyAnswers a qud ∨
      ∃ q ∈ subquestions, Question.PartiallyAnswers a q

/-- A discourse move is relevant to a strategy if some alternative of
    `den` partially answers some question in the strategy. -/
def moveRelevantToStrategy (den : Question W) (strat : Strategy W) : Prop :=
  ∃ a ∈ Question.alt den, ∃ q ∈ strat.allQuestions, Question.PartiallyAnswers a q

/-- A move is relevant if one of its alternatives partially answers the
QUD directly, with no subquestions. -/
theorem moveRelevant_of_partiallyAnswers
    {den qud : Question W} {a : Set W} (ha : a ∈ Question.alt den)
    (h : Question.PartiallyAnswers a qud) :
    moveRelevant den qud [] :=
  ⟨a, ha, Or.inl h⟩

/-- Strategy relevance is `moveRelevant` against the root question and
the descendant questions. -/
theorem moveRelevantToStrategy_iff_moveRelevant
    (den : Question W) (strat : Strategy W) :
    moveRelevantToStrategy den strat ↔
      moveRelevant den strat.question
        (strat.substrategies.flatMap Strategy.allQuestions) := by
  cases strat <;>
    simp [moveRelevantToStrategy, moveRelevant, Strategy.allQuestions,
      Strategy.question, Strategy.substrategies]

/-- Polar reduction of `moveRelevant` to partial answerhood of `p` and
`pᶜ`. -/
theorem moveRelevant_polar_iff {p : Set W} {qud : Question W}
    {subquestions : List (Question W)}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    moveRelevant (Question.polar p) qud subquestions ↔
      (Question.PartiallyAnswers p qud ∨
        ∃ Q ∈ subquestions, Question.PartiallyAnswers p Q) ∨
      (Question.PartiallyAnswers pᶜ qud ∨
        ∃ Q ∈ subquestions, Question.PartiallyAnswers pᶜ Q) := by
  simp only [moveRelevant, Question.alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left]

end Discourse
