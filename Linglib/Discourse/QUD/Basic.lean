import Linglib.Core.Data.RoseTree.Basic
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Entailment
import Linglib.Semantics.Questions.Resolution

/-!
# Questions under discussion: stack and strategy

The inquiry coordinate of the conversational scoreboard, after
[roberts-2012]: the stack of accepted-but-unanswered questions
(`QUDStack`, her definition (10g); the head is the immediate QUD),
strategies of inquiry as rose trees of questions (`Strategy`, her (12);
[buring-2003]'s d-trees are the explicit tree-shaped ancestor),
hereditary strategy completeness (`IsComplete`), and relevance of a
move's denotation to a set of questions (`Relevant`, built from the
assertion clause of her Relevance (15)). [ginzburg-2012]'s KoS models
the same coordinate as a partially ordered set with its own update
rules; that structure lives with the gameboard in
`Discourse/Gameboard/`. [beaver-roberts-simons-tonhauser-2017] is the
modern survey statement of the framework; [riester-2019] gives explicit
reconstruction rules and well-formedness constraints for QUD trees over
corpus data.

## Main definitions

* `Discourse.QUDStack` — the stack, as a `List (Question W)`
* `Discourse.QUDStack.WellFormed` — Roberts' ordering constraint
  (10g.iii), relative to a context set
* `Discourse.Strategy` — strategies of inquiry as `RoseTree (Question W)`
* `Discourse.Strategy.IsComplete` — at every branching node, the meet of
  the children's questions entails the parent's
* `Discourse.Relevant` — some alternative of the move partially answers
  some question in the set

## Fidelity notes

Roberts' (10g) makes QUD a function from moves to ordered sets of
accepted, unanswered questions; `QUDStack` models a single value of that
function, and clause (iii) — each question's complete answers
contextually entail partial answers to every question below it — is
`WellFormed`, relative to a context set because entailment in her (9) is
contextual throughout. She warns against strengthening (iii) to question
entailment (her bridging-question discourse (13) violates it). Questions
are retired when answered or determined practically unanswerable, and
she licenses non-LIFO removal (answering a lower question discharges the
higher questions in its strategy); `List.tail` is the unconditional LIFO
special case, and the licensing conditions are the caller's obligation.

Her (12) defines `Strat(q)` derivatively — its substrategies are those
for the questions accepted while `q` was the immediate QUD — with
well-formedness left to "rational considerations", and the second
component an unordered set. The ordered `RoseTree` follows
[buring-2003]. `IsComplete` is the success criterion her D₀ discussion
illustrates (complete answers to the subquestions jointly yield a
complete answer to the parent), not a clause of (12); the converse
direction (parent entails children-meet) is exactly what (13) rules out.

`Relevant` is existential answerhood relevance: weaker than (15), whose
guarantee is universal (every complete answer to the move contextually
entails a partial answer to the QUD), and set-valued where (15) targets
only `last(QUD)`. The set extension is the proxy
[ippolito-kiss-williams-2025] use for their relevance assumption,
consumed by the discourse *only* definedness condition in their (16);
that the set really holds subquestions of the QUD is the caller's
obligation.
-/

namespace Discourse

/-- A QUD stack ([roberts-2012] definition (10g)): the accepted, unanswered
questions, most recent first, so the head is the immediate QUD. Accepting a
question is `List.cons`; retiring one from the top is `List.tail`. -/
abbrev QUDStack (W : Type*) := List (Question W)

namespace QUDStack

variable {W : Type*}

/-- Roberts' ordering constraint (10g.iii) on a QUD stack, relative to context
set `C`: for `higher` accepted more recently than `lower`, every complete
answer to `higher` contextually entails a partial answer to `lower`. -/
def WellFormed (C : Set W) (s : QUDStack W) : Prop :=
  s.Pairwise fun higher lower =>
    ∀ a ∈ Question.alt higher, Question.PartiallyAnswers (C ∩ a) lower

@[simp] theorem wellFormed_nil (C : Set W) : WellFormed C ([] : QUDStack W) :=
  List.Pairwise.nil

@[simp] theorem wellFormed_singleton (C : Set W) (q : Question W) :
    WellFormed C [q] :=
  List.pairwise_singleton ..

/-- Accepting `q` preserves well-formedness iff `q`'s complete answers
contextually partially answer every question already on the stack. -/
theorem wellFormed_cons {C : Set W} {q : Question W} {s : QUDStack W} :
    WellFormed C (q :: s) ↔
      (∀ lower ∈ s, ∀ a ∈ Question.alt q,
        Question.PartiallyAnswers (C ∩ a) lower) ∧ WellFormed C s :=
  List.pairwise_cons

/-- Retiring the immediate QUD preserves well-formedness. -/
theorem WellFormed.tail {C : Set W} {s : QUDStack W} (h : WellFormed C s) :
    WellFormed C s.tail :=
  List.Pairwise.tail h

end QUDStack

/-- A strategy of inquiry as a rose tree of questions ([roberts-2012]
definition (12), [buring-2003]'s d-trees): each node a question, its children
the subquestions pursued to answer it. -/
abbrev Strategy (W : Type*) := RoseTree (Question W)

namespace Strategy

variable {W : Type*}

/-- A strategy is **complete** when at every branching node the meet of the
children's questions entails the parent's question: jointly resolving the
subquestions resolves the parent. Terminal nodes are trivially complete. -/
inductive IsComplete : Strategy W → Prop
  | node {q : Question W} {cs : List (Strategy W)}
      (complete : cs ≠ [] →
        ((cs.map RoseTree.value : Multiset (Question W))).inf.Entails q)
      (children : ∀ c ∈ cs, IsComplete c) : IsComplete (.node q cs)

theorem IsComplete.leaf (q : Question W) : IsComplete (.leaf q : Strategy W) :=
  .node (fun h => absurd rfl h) nofun

/-- Binary branching: a two-child node is complete when the meet of the
children's questions entails the parent's and both children are complete. -/
theorem IsComplete.node_pair {q : Question W} {s t : Strategy W}
    (h : (s.value ⊓ t.value).Entails q)
    (hs : s.IsComplete) (ht : t.IsComplete) :
    IsComplete (.node q [s, t]) := by
  refine .node (fun _ => ?_) ?_
  · simpa using h
  · rintro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hs
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ht
      · exact absurd hc (List.not_mem_nil)

@[simp] theorem isComplete_node_iff {q : Question W} {cs : List (Strategy W)} :
    IsComplete (.node q cs) ↔
      (cs ≠ [] →
        ((cs.map RoseTree.value : Multiset (Question W))).inf.Entails q) ∧
        ∀ c ∈ cs, IsComplete c :=
  ⟨fun h => by cases h with | node h₁ h₂ => exact ⟨h₁, h₂⟩,
    fun ⟨h₁, h₂⟩ => .node h₁ h₂⟩

end Strategy

variable {W : Type*}

/-- A move with denotation `den` is **relevant** to the questions in `qs` when
some alternative of `den` partially answers some question in `qs` — the
assertion clause of [roberts-2012]'s Relevance (15), existentially weakened
and extended to a question set (see the fidelity notes). -/
def Relevant (den : Question W) (qs : Set (Question W)) : Prop :=
  ∃ a ∈ Question.alt den, ∃ q ∈ qs, Question.PartiallyAnswers a q

/-- Polar reduction of `Relevant` to partial answerhood of `p` and `pᶜ`. -/
theorem relevant_polar_iff {p : Set W} {qs : Set (Question W)}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    Relevant (Question.polar p) qs ↔
      (∃ q ∈ qs, Question.PartiallyAnswers p q) ∨
        ∃ q ∈ qs, Question.PartiallyAnswers pᶜ q := by
  simp only [Relevant, Question.alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left]

end Discourse
