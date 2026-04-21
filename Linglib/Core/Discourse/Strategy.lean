import Linglib.Core.Question.Hamblin
import Linglib.Core.Question.Relevance

/-!
# Strategy of Inquiry: Rose-Tree Decomposition of a QUD
@cite{roberts-2012}

A `Strategy W` is @cite{roberts-2012} Def. 12: a plan to answer a question by
pursuing subquestions. Modeled as a rose tree where each node is a question
and children are subquestions whose collective answers resolve the parent.
The companion stack representation (`QUDStack`) captures the *current*
unanswered slice; a strategy captures the *full plan*.

The strategy is parameterized by `Core.Question W` — the Set-based
inquisitive-content lattice. The completeness predicate uses lattice
meet `⊓` (children's joint answer) and the Prop-valued
`Core.Question.questionEntails` from `Core/Question/Relevance.lean`.
-/

namespace Discourse

open Core

/-- A strategy of inquiry: a plan to answer a question by pursuing subquestions.

    @cite{roberts-2012} Def. 12: "A strategy of inquiry Strat(q) is a set
    of questions {q₁, ..., qₙ} such that ... if all the questions in
    Strat(q) were answered, q would be answered too."

    Modeled as a rose tree: each node is a question, children are
    subquestions whose collective answers resolve the parent. -/
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

/-- A strategy is **complete** at a single level: the meet of child
    questions (their joint resolution) entails the parent question.

    @cite{roberts-2012} Def. 12: answering all subquestions answers the parent.

    This checks only the root node; recurse on sub-strategies for full-tree
    verification. The meet `⊓` is taken in the inquisitive-content lattice;
    `⊤` is the trivial issue (resolved by every state). -/
def isComplete : Strategy W → Prop
  | .leaf _ => True
  | .branch q children =>
    let combined := (children.map (·.question)).foldl (· ⊓ ·) ⊤
    Question.questionEntails combined q

end Strategy

/-- A discourse move is relevant to a strategy if some alternative of `den`
    partially answers some question in the strategy.

    Derived from `Core.Question.moveRelevant` by treating every question in
    the strategy tree as a candidate subquestion. -/
def moveRelevantToStrategy {W : Type*} (den : Question W) (strat : Strategy W) : Prop :=
  ∃ a ∈ Question.alt den, ∃ q ∈ strat.allQuestions, Question.partiallyAnswers q a

end Discourse
