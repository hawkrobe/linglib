import Linglib.Core.Agent.DecisionTheory

/-!
# Relevance-Parameterized Question Denotations
@cite{van-rooy-2003}

Theory-level constructs from @cite{van-rooy-2003}'s decision-theoretic
question semantics. These are general mechanisms, not paper-specific models.

## Key Definitions

- `RelevanceFunction`: Op(P)(w) — relevance-maximal groups per world
- `underspecifiedDenotation`: ⟦?xPx⟧^R — the unified question denotation
- `mentionAllRelevance` / `mentionSomeRelevance`: Standard instantiations of Op
- `isDecisionRelevant` / `decisionRelevantDomain`: Domain selection via UV

## Design

The `RelevanceFunction` abstracts over the decision problem: it captures
*which* groups of satisfiers are optimal without exposing the DP's action
set or utility function. The DP determines the relevance function; the
relevance function determines the question denotation.

This separation matches @cite{van-rooy-2003}'s architecture: §3 defines
utility of answers via DPs, §5 defines the question denotation via Op(P),
and the connection is that Op(P)(w) collects the groups with maximal
relevance/utility.
-/

namespace Semantics.Questions.Relevance

open Core.DecisionTheory

/-! ## Op(P): Relevance-Maximal Satisfiers

@cite{van-rooy-2003}, §5 (p. 752–753): Op(P)(w) selects the group(s) of
P-satisfiers in world w that are maximally relevant to the agent's
decision problem. -/

/-- A relevance function assigns to each world a set of "optimal groups"
of entities — those groups that are maximally relevant to the agent's
decision problem.

@cite{van-rooy-2003}, p. 753: ⟦Op(P)⟧^R = {⟨w,g⟩ | P(w)(g) & ¬∃g'[P(w)(g') & P(g') > P(g)]} -/
structure RelevanceFunction (W E : Type*) where
  /-- The predicate (e.g., "sells Italian newspapers") -/
  predicate : W → E → Bool
  /-- The optimal groups in each world: subsets of satisfiers that are
      maximally relevant to the decision problem -/
  optimalGroups : W → List (List E)

/-- Standard mention-all: Op(P)(w) = {ext(P)(w)}, the full extension.
Only one group per world: all satisfiers together. -/
def mentionAllRelevance {W E : Type*} [DecidableEq E]
    (predicate : W → E → Bool) (domain : List E) : RelevanceFunction W E where
  predicate := predicate
  optimalGroups := λ w => [domain.filter (predicate w)]

/-- Mention-some relevance: Op(P)(w) = {{a} : P(a)(w)}, each satisfier
is its own optimal group. Any single satisfier suffices. -/
def mentionSomeRelevance {W E : Type*}
    (predicate : W → E → Bool) (domain : List E) : RelevanceFunction W E where
  predicate := predicate
  optimalGroups := λ w => domain.filter (predicate w) |>.map (·::[])

/-! ## ⟦?xPx⟧^R: The Underspecified Question Denotation

@cite{van-rooy-2003}, §5 (p. 752):

  ⟦?xPx⟧^R = {λv[g ∈ Op(P)(v)] : w ∈ W & g ∈ Op(P)(w)}

Each "answer" is a proposition saying "group g is among the optimal
groups." When Op = mention-all, this reduces to G&S. When Op = mention-some,
this produces one answer per satisfier. -/

/-- The relevance-parameterized question denotation ⟦?xPx⟧^R.

@cite{van-rooy-2003}, p. 752. -/
def underspecifiedDenotation {W E : Type*} [BEq E] [BEq (List E)]
    (rf : RelevanceFunction W E) (worlds : List W) : List (W → Bool) :=
  let allGroups := worlds.flatMap rf.optimalGroups |>.eraseDups
  allGroups.map λ g => λ v => rf.optimalGroups v |>.any (· == g)

/-! ## Domain Selection

@cite{van-rooy-2003}, §4.2 (p. 745–746): The wh-domain of a question
contains exactly those individuals whose P-status is decision-relevant.
An individual d is decision-relevant if learning whether P(d) holds has
positive utility value. -/

/-- An individual d is decision-relevant for question ?xP(x) given DP
if learning whether P(d) holds has positive utility value.

@cite{van-rooy-2003}, p. 746: d ∈ D_optimal iff knowing P(d) vs ¬P(d)
could affect the agent's decision. -/
def isDecisionRelevant {W : Type*} [Fintype W] [DecidableEq W]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A)
    (predicate : W → Bool) : Bool :=
  let yesCell := Finset.univ.filter (λ w => predicate w = true)
  utilityValue dp actions yesCell > 0

/-- The decision-relevant domain: entities whose P-status matters for
the agent's decision problem.

@cite{van-rooy-2003}, p. 746: D_optimal = {d | UV(P(d)) > 0}. -/
def decisionRelevantDomain {W E : Type*} [Fintype W] [DecidableEq W]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A)
    (predicate : W → E → Bool) (domain : List E) : List E :=
  domain.filter λ d => isDecisionRelevant dp actions (predicate · d)

end Semantics.Questions.Relevance
