import Linglib.Core.Data.RoseTree.Basic
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Entailment
import Linglib.Semantics.Questions.Resolution

/-!
# Questions under discussion: stack and strategy

The inquiry coordinate of the conversational scoreboard, after
[roberts-2012]: the stack of accepted-but-unanswered questions, a
`List (Question W)` with the immediate QUD at its head, well formed when
each question is a contextual subquestion of every question below it
(definition (10g), `List.Pairwise (Question.IsSubquestionOf C)`);
strategies of inquiry as rose trees of questions (`Strategy`, (12);
[buring-2003]'s d-trees are the explicit tree-shaped ancestor),
hereditary strategy completeness (`IsComplete`), and relevance of a
move's denotation to a set of questions (`Question.IsRelevantTo`, built from the
assertion clause of Relevance (15)). [ginzburg-2012]'s KoS models
the same coordinate as a partially ordered set with its own update
rules; that structure lives with the gameboard in
`Discourse/Gameboard/`. [beaver-roberts-simons-tonhauser-2017] is the
modern survey statement of the framework; [riester-2019] gives explicit
reconstruction rules and well-formedness constraints for QUD trees over
corpus data.

## Main definitions

* `Discourse.Strategy` — strategies of inquiry as `RoseTree (Question W)`
* `Discourse.Strategy.WellFormed` — every question in a subtree is a
  contextual subquestion of the subtree's root
* `Discourse.Strategy.IsComplete` — at every branching node, the meet of
  the children's questions entails the parent's
* `Question.IsRelevantTo` — some alternative of the move partially
  answers some question in the set

## Fidelity notes

Definition (10g) makes QUD a function from moves to ordered sets of
accepted, unanswered questions; a `List (Question W)` models a single value
of that function, and clause (iii) — each question's complete answers
contextually entail partial answers to every question below it — is
`List.Pairwise (Question.IsSubquestionOf C)`, relative to a context set
because entailment in (9) is contextual throughout. The paper warns
against strengthening (iii) to question entailment (the bridging-question
discourse (13) violates it). Questions
are retired when answered or determined practically unanswerable, and
the paper licenses non-LIFO removal (answering a lower question discharges the
higher questions in its strategy); `List.tail` is the unconditional LIFO
special case, and the licensing conditions are the caller's obligation.

Definition (12) gives `Strat(q)` derivatively — its substrategies are those
for the questions accepted while `q` was the immediate QUD — with
well-formedness left to "rational considerations", and the second
component an unordered set. The ordered `RoseTree` follows
[buring-2003]. A strategy read off well-formed stacks has every question
of a subtree a contextual subquestion of that subtree's root, and since
the relation is not transitive `WellFormed` states this for every
ancestor, not only the parent. `IsComplete` is the success criterion the D₀ discussion
illustrates (complete answers to the subquestions jointly yield a
complete answer to the parent), not a clause of (12); the converse
direction (parent entails children-meet) is exactly what (13) rules out.

`IsRelevantTo` is existential answerhood relevance: weaker than (15), whose
guarantee is universal (every complete answer to the move contextually
entails a partial answer to the QUD), and set-valued where (15) targets
only `last(QUD)`. The set extension is the proxy
[ippolito-kiss-williams-2025] use for their relevance assumption,
consumed by the discourse *only* definedness condition in their (16);
that the set really holds subquestions of the QUD is the caller's
obligation.
-/

namespace Discourse

/-- A strategy of inquiry as a rose tree of questions ([roberts-2012]
definition (12), [buring-2003]'s d-trees): each node a question, its children
the subquestions pursued to answer it. -/
abbrev Strategy (W : Type*) := RoseTree (Question W)

namespace Strategy

variable {W : Type*}

/-- A strategy is **well formed** in the context `C` when every question in a subtree is a
contextual subquestion of that subtree's root ([roberts-2012] definition (12), the strategies
read off the stacks of (10g)). -/
inductive WellFormed (C : Set W) : Strategy W → Prop
  | node {q : Question W} {cs : List (Strategy W)}
      (sub : ∀ c ∈ cs, ∀ r ∈ c.values, Question.IsSubquestionOf C r q)
      (children : ∀ c ∈ cs, WellFormed C c) : WellFormed C (.node q cs)

theorem WellFormed.leaf (C : Set W) (q : Question W) : WellFormed C (.leaf q : Strategy W) :=
  .node nofun nofun

@[simp] theorem wellFormed_node_iff {C : Set W} {q : Question W} {cs : List (Strategy W)} :
    WellFormed C (.node q cs) ↔
      (∀ c ∈ cs, ∀ r ∈ c.values, Question.IsSubquestionOf C r q) ∧ ∀ c ∈ cs, WellFormed C c :=
  ⟨fun | .node h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .node h₁ h₂⟩

/-- Every question of a well-formed strategy is a contextual subquestion of its root. -/
theorem WellFormed.isSubquestionOf_root {C : Set W} : ∀ {t : Strategy W}, WellFormed C t →
    ∀ r ∈ t.values, Question.IsSubquestionOf C r t.value
  | .node _ _, .node h _, r, hr => by
    rw [RoseTree.values_node, List.mem_cons, List.mem_flatten] at hr
    rcases hr with rfl | ⟨l, hl, hrl⟩
    · exact .refl _ _
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
      exact h c hc r hrl

/-- A strategy is **complete** when at every branching node the meet of the
children's questions entails the parent's question: jointly resolving the
subquestions resolves the parent. Terminal nodes are trivially complete. -/
inductive IsComplete : Strategy W → Prop
  | node {q : Question W} {cs : List (Strategy W)}
      (complete : cs ≠ [] → ((cs.map RoseTree.value : Multiset (Question W))).inf ≤ q)
      (children : ∀ c ∈ cs, IsComplete c) : IsComplete (.node q cs)

theorem IsComplete.leaf (q : Question W) : IsComplete (.leaf q : Strategy W) :=
  .node (fun h => absurd rfl h) nofun

/-- Binary branching: a two-child node is complete when the meet of the
children's questions entails the parent's and both children are complete. -/
theorem IsComplete.node_pair {q : Question W} {s t : Strategy W}
    (h : s.value ⊓ t.value ≤ q) (hs : s.IsComplete) (ht : t.IsComplete) :
    IsComplete (.node q [s, t]) :=
  .node (fun _ => by simpa using h) (by simp [hs, ht])

@[simp] theorem isComplete_node_iff {q : Question W} {cs : List (Strategy W)} :
    IsComplete (.node q cs) ↔
      (cs ≠ [] → ((cs.map RoseTree.value : Multiset (Question W))).inf ≤ q) ∧
        ∀ c ∈ cs, IsComplete c :=
  ⟨fun | .node h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .node h₁ h₂⟩

end Strategy

variable {W : Type*}


end Discourse
