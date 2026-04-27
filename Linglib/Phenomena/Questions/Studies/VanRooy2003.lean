import Linglib.Core.Question.Basic
import Linglib.Core.Question.Hamblin
import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Semantics.Questions.DecisionTheoretic

/-!
# @cite{van-rooy-2003}: Questioning to Resolve Decision Problems
@cite{groenendijk-stokhof-1984} @cite{karttunen-1977} @cite{ginzburg-1995} @cite{merin-1999}

Single-paper formalisation of @cite{van-rooy-2003}, "Questioning to
Resolve Decision Problems", *Linguistics and Philosophy* 26.6:
727–763. The paper grounds question semantics in Bayesian decision
theory: questions are evaluated by how their answers affect the
optimal action in the questioner's decision problem.

## Substrate identification

The decision-theoretic machinery — `EU`, `UV`, `VSI`, `DecisionProblem`
— is already in `Core/Agent/DecisionTheory.lean`. Van Rooy's notation
maps to the substrate as:

| @cite{van-rooy-2003}                             | substrate                                  |
|--------------------------------------------------|--------------------------------------------|
| `EU(a) = ∑_w P(w) · U(a, w)`                     | `Core.DecisionTheory.expectedUtility`      |
| `UV(Choose now) = max_a EU(a)`                   | `Core.DecisionTheory.dpValue`              |
| `EU(a, C) = ∑_w P_C(w) · U(a, w)`                | `Core.DecisionTheory.conditionalEU`        |
| `UV(Learn C, choose later) = max_a EU(a, C)`     | `Core.DecisionTheory.valueAfterLearning`   |
| `UV(C) = UV(L C, c later) − UV(C now)`           | `Core.DecisionTheory.utilityValue`         |
| `UV*(C) = VSI(C)` ≥ 0                            | `Core.DecisionTheory.valueSampleInfo`      |
| `Q ⊑ Q'`  (every Q-alt ⊆ some Q'-alt)            | `Core.Question.questionEntails`            |
| `C resolves DP`                                  | `Core.DecisionTheory.IsResolved`           |

## What this file proves

* **§3.1 Action-induced partition `A*`** (p. 736-737):
  `optimalityCell dp acts a` and `actionPartition`.
* **§3.1 *C* resolves DP** (p. 736): the substrate's
  `Core.DecisionTheory.IsResolved dp acts C` — some action weakly
  dominates every other on every world in C.
* **§4.1 Blackwell-style ordering** (p. 741): the "Q is more
  informative than Q'" notion is `Core.Question.questionEntails Q Q'`
  (no paper-specific alias needed).
* **§4.1 Decision-relevance preservation**: under the *strong*
  Blackwell condition (`CoversAltsOf` from substrate), preservation
  holds. The substrate's `CoversAltsOf.preserves_decisionRelevant`
  IS the @cite{van-rooy-2003} theorem.

## What this file does NOT replicate

* The *identification-question* discussion (§2 (1)–(8)) requires
  named-individual / referential machinery beyond plain `Set W`;
  deferred.
* The *underspecified meaning* proposal (§5) requires a typed
  ambiguity-resolution layer beyond `Question W`; deferred.
* The Italian-newspaper mention-some example (§3.2 (12)) is the
  natural target for the next refinement, when the
  `Phenomena.Questions.MentionSome` data file is wired up.
-/

namespace Phenomena.Questions.Studies.VanRooy2003

open Core Core.DecisionTheory Core.Question
open Semantics.Questions.DecisionTheoretic

variable {W A : Type*}

/-! ### §3.1 Action-induced partition `A*` (p. 736-737)

@cite{van-rooy-2003} p. 736: "Notice that not only a question, but
also the set of alternative actions, A, gives rise to a set of
propositions. We can relate each action a ∈ A to the set of worlds
in which there is no other action b in A that is strictly better.
We will denote the proposition corresponding with a by a*". -/

/-- The **optimality cell** of action `a` (van Rooy's `a*`): the set
    of worlds where `a` strictly dominates every other action in
    `acts`. @cite{van-rooy-2003} p. 736. -/
def optimalityCell (dp : DecisionProblem W A) (acts : Set A) (a : A) : Set W :=
  {w | ∀ b ∈ acts, b ≠ a → dp.utility w a > dp.utility w b}

/-- The **action-induced partition** `A*`: the set of optimality
    cells. @cite{van-rooy-2003} p. 736-737. -/
def actionPartition (dp : DecisionProblem W A) (acts : Set A) : Set (Set W) :=
  optimalityCell dp acts '' acts

/-- The optimality cells are pairwise disjoint: each world lies in at
    most one cell. (Page 737: "the set of propositions A* does in
    general not partition the state space, but it does when for each
    world `w` there is always exactly one action a ∈ A such that
    ∀b ∈ A−{a} : U(a,w) > U(b,w)".) -/
theorem optimalityCell_pairwise_disjoint
    (dp : DecisionProblem W A) (acts : Set A)
    {a a' : A} (haa' : a ≠ a')
    (w : W) (hwa : w ∈ optimalityCell dp acts a) (hwa' : w ∈ optimalityCell dp acts a')
    (ha_acts : a ∈ acts) (ha'_acts : a' ∈ acts) :
    False := by
  have h1 : dp.utility w a > dp.utility w a' := hwa a' ha'_acts (Ne.symm haa')
  have h2 : dp.utility w a' > dp.utility w a := hwa' a ha_acts haa'
  exact absurd h1 (not_lt_of_gt h2)

/-! ### §3.1 *C* resolves DP (p. 736)

> "We should say that information `C` resolves a decision problem if
> after learning `C`, one of the actions in `A` dominates all other
> actions, i.e., if in each resulting world no action has a higher
> utility than this one."

This is exactly `Core.DecisionTheory.IsResolved dp acts C`. We do not
introduce a paper-vocabulary alias — consumers should use the
substrate predicate directly. -/

/-! ### §4.1 Question ordering (p. 741)

@cite{van-rooy-2003} p. 741: "Q is a *better* question than Q' [...]
in terms of @cite{groenendijk-stokhof-1984} partition semantics this
comes down to the natural requirement that for every element of Q
there must be an element of Q' such that the former entails the
latter, i.e., `Q ⊑ Q'`:

    Q ⊑ Q' iff ∀q ∈ Q : ∃q' ∈ Q' : q ⊆ q'."

This is exactly `Core.Question.questionEntails Q Q'`. We do not
introduce a paper-vocabulary alias — consumers should write
`questionEntails Q Q'` (or use `≤` on `Question W`'s lattice
instance) directly. The relation is reflexive (`questionEntails_refl`)
and transitive (`questionEntails_trans`). -/

/-! ### §4.1 Decision-relevance preservation

@cite{van-rooy-2003} §4.1 asserts that a finer (more informative)
question is at least as decision-useful as a coarser one. The
substrate-level claim: under the strong Blackwell condition
`CoversAltsOf` (every nonempty Q'-alt is covered by a nonempty
Q-alt), the inquisitive `IsDecisionRelevant Q' dp acts` lifts to
`Q`. The bare `questionEntails` (P-alts ⊆ Q-alts) gives only one
half of the correspondence; for the inquisitive substrate the dual
must be supplied separately.

For *partition* questions (where every alternative is non-empty and
the alternatives jointly cover the state space), `questionEntails`
and `CoversAltsOf` coincide, recovering @cite{van-rooy-2003}'s
partition-based theorem. -/

/-- @cite{van-rooy-2003} §4.1 **decision-relevance preservation
    under the strong Blackwell condition**: when `Q` covers `Q'`'s
    alternatives, decision-relevance lifts. Direct re-export of the
    substrate's `CoversAltsOf.preserves_decisionRelevant`. -/
theorem decisionRelevance_preserved_under_cover
    {Q Q' : Question W} (hCover : CoversAltsOf Q Q')
    {dp : DecisionProblem W A} {acts : Set A}
    (hQ' : IsDecisionRelevant Q' dp acts) :
    IsDecisionRelevant Q dp acts :=
  hCover.preserves_decisionRelevant hQ'

/-! ### Substrate gap note

The bare @cite{van-rooy-2003} `Q ⊑ Q'` ordering does **not** suffice
for decision-relevance preservation on the inquisitive substrate:
`questionEntails` says only that `Q`-alts ⊆ `Q'`-alts, not the dual
"every `Q'`-alt is covered by a `Q`-alt". On a partition `Question W`
the two directions coincide and @cite{van-rooy-2003}'s informal
argument goes through; on a general inquisitive `Question W` they
split. The substrate exposes the dual as `CoversAltsOf` and proves
preservation against that direction. See the docstring of
`Semantics.Questions.DecisionTheoretic.CoversAltsOf`. -/

end Phenomena.Questions.Studies.VanRooy2003
