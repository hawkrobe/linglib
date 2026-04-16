import Linglib.Core.Inquisitive
import Linglib.Core.QUD.Relevance

/-!
# Strategy of Inquiry: Rose-Tree Decomposition of a QUD
@cite{roberts-2012}

A `Strategy W` is Roberts 2012 Def. 12: a plan to answer a question by
pursuing subquestions. Modeled as a rose tree where each node is a question
and children are subquestions whose collective answers resolve the parent.
The companion stack representation (`QUDStack`) captures the *current*
unanswered slice; a strategy captures the *full plan*.
-/

namespace Discourse

/-- A strategy of inquiry: a plan to answer a question by pursuing subquestions.

    @cite{roberts-2012} Def. 12: "A strategy of inquiry Strat(q) is a set
    of questions {q₁, ..., qₙ} such that ... if all the questions in
    Strat(q) were answered, q would be answered too."

    Modeled as a rose tree: each node is a question, children are
    subquestions whose collective answers resolve the parent. -/
inductive Strategy (W : Type*) where
  | leaf : Issue W → Strategy W
  | branch : Issue W → List (Strategy W) → Strategy W

namespace Strategy

variable {W : Type*}

/-- The question at the root of this (sub)strategy. -/
def question : Strategy W → Issue W
  | .leaf q | .branch q _ => q

/-- Immediate substrategies (empty for leaves). -/
def substrategies : Strategy W → List (Strategy W)
  | .leaf _ => []
  | .branch _ ss => ss

/-- All questions in the strategy (root + all descendants). -/
def allQuestions : Strategy W → List (Issue W)
  | .leaf q => [q]
  | .branch q ss => q :: ss.flatMap allQuestions

/-- Leaf questions only (terminal nodes of the strategy). -/
def leaves : Strategy W → List (Issue W)
  | .leaf q => [q]
  | .branch _ ss => ss.flatMap leaves

/-- A strategy is **complete** at a single level: the intersection of
    child questions entails the parent question.

    @cite{roberts-2012} Def. 12: answering all subquestions answers the parent.

    This checks only the root node; use separately on sub-strategies
    for full-tree verification. -/
def isComplete (s : Strategy W) (worlds : List W) : Bool :=
  match s with
  | .leaf _ => true
  | .branch q children =>
    let combined := children.map (·.question) |>.foldl (·.inter · worlds)
      (Issue.ofAlternatives [trivialState])
    questionEntails combined q worlds

end Strategy

/-- A discourse move is relevant to a strategy if it partially answers
    any question in the strategy.

    Derived from `moveRelevant` by extracting all subquestions from the
    strategy tree. -/
def moveRelevantToStrategy {W : Type*} (den : Issue W) (strat : Strategy W)
    (worlds : List W) : Bool :=
  let allQs := strat.allQuestions
  den.alternatives.any fun alt =>
    allQs.any fun q => partiallyAnswers alt q worlds

end Discourse
