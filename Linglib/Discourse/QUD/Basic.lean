import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Relevance

/-!
# Questions under discussion: stack and strategy
[roberts-2012]

The inquiry coordinate of the conversational scoreboard: the stack of
accepted-but-unanswered questions (head is the immediate QUD;
subquestions push, answers pop) and the rose-tree strategy of inquiry
decomposing a question into subquestions whose joint resolution answers
the parent.
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
    Question.questionEntails combined q

end Strategy

/-- A discourse move is relevant to a strategy if some alternative of
    `den` partially answers some question in the strategy. -/
def moveRelevantToStrategy {W : Type*} (den : Question W) (strat : Strategy W) : Prop :=
  ∃ a ∈ Question.alt den, ∃ q ∈ strat.allQuestions, Question.partiallyAnswers q a

end Discourse
