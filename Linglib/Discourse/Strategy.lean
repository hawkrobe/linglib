import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Relevance

/-!
# Strategy of Inquiry: Rose-Tree Decomposition of a QUD
@cite{roberts-2012}

A `Strategy W` is a rose-tree plan to answer a question by pursuing
subquestions whose collective answers resolve the parent. The
companion `QUDStack` is the current unanswered slice.
-/

namespace Discourse

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
