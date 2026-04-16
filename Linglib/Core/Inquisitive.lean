import Linglib.Core.QUD.Basic

/-!
# Inquisitive Semantics: Information States and Issues
@cite{ciardelli-groenendijk-roelofsen-2018}

The intensional side of question semantics: propositions as sets of worlds,
questions as sets of propositions (alternatives).

`InfoState W = W → Bool` characterises a set of compatible worlds; an
`Issue W` packages a list of maximal resolving info states (alternatives).
This file defines the basic InfoState/Issue algebra: support, entailment,
issue construction (`polar`, `which`, `ofAlternatives`), issue operations
(`inter`, `union`), the bridge to `QUD` partitions (`Issue.toQUD`), and the
`widerThan` granularity ordering (@cite{deo-thomas-2025}).

Roberts 2012 entailment/relevance (`questionEntails`, `partiallyAnswers`,
`isSubquestion`, `moveRelevant`) lives in `Core/QUD/Relevance.lean`.

The connection: a `QUD M` induces an `Issue W` when we fix a world type W
and a denotation function M → (W → Bool). Each equivalence class of the
QUD maps to an alternative of the Issue. `QUD.refines` (Core/Partition.lean)
corresponds to `questionEntails`: if Q refines q at the partition level,
then Q entails q at the issue level.
-/

namespace Discourse

-- Information States

/-- An information state: worlds compatible with current information.

In standard Inquisitive Semantics, an info state is a SET of worlds.
Here we represent it as a characteristic function σ : W → Bool.

Semantically: σ w = true means "world w is compatible with the information".
The empty info state (σ = λ_ => false) represents inconsistent information. -/
abbrev InfoState (W : Type*) := W → Bool

/-- The absurd/inconsistent info state: no worlds are compatible. -/
def absurdState {W : Type*} : InfoState W := λ _ => false

/-- The trivial info state: all worlds are compatible (total ignorance). -/
def trivialState {W : Type*} : InfoState W := λ _ => true

/-- Check if an info state is empty (inconsistent). -/
def InfoState.isEmpty {W : Type*} (σ : InfoState W) (worlds : List W) : Bool :=
  !worlds.any σ

/-- Check if an info state is non-empty. -/
def InfoState.isNonEmpty {W : Type*} (σ : InfoState W) (worlds : List W) : Bool :=
  worlds.any σ

/-- Info state σ is a subset of σ' (σ ⊆ σ'). -/
def InfoState.subset {W : Type*} (σ σ' : InfoState W) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → σ' w

/-- Intersection of two info states. -/
def InfoState.inter {W : Type*} (σ σ' : InfoState W) : InfoState W :=
  λ w => σ w && σ' w

/-- Union of two info states. -/
def InfoState.union {W : Type*} (σ σ' : InfoState W) : InfoState W :=
  λ w => σ w || σ' w

-- Support and Entailment

/-- Info state σ supports proposition p iff σ ⊆ ⟦p⟧.

This is the fundamental relation in Inquisitive Semantics:
σ ⊨ p (σ supports p) iff every world in σ makes p true.

If σ is empty, it supports every proposition (ex falso quodlibet). -/
def supports {W : Type*} (σ : InfoState W) (p : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → p w

/-- Propositional entailment: p entails q iff every p-world is a q-world.

Equivalently: the info state ⟦p⟧ supports ⟦q⟧ over all worlds. -/
def propEntails {W : Type*} (p q : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !p w || q w

-- Issues (Questions in Inquisitive Semantics)

/-- An issue: set of information states that resolve the question.

In full Inquisitive Semantics, issues must be:
1. **Downward-closed**: if σ resolves and σ' ⊆ σ, then σ' resolves
2. **Non-empty**: the absurd state ∅ resolves every issue

Here we represent an issue by its maximal (largest) resolving states,
called **alternatives**. Downward closure is then implicit.

This representation aligns with Hamblin semantics: the alternatives are
the possible complete answers. -/
structure Issue (W : Type*) where
  /-- The maximal resolving states (alternatives) -/
  alternatives : List (InfoState W)

namespace Issue

variable {W : Type*}

/-- Check if an info state resolves the issue.

σ resolves Q iff σ is contained in some alternative.
(Downward closure: any sub-state of an alternative also resolves.) -/
def resolves (q : Issue W) (σ : InfoState W) (worlds : List W) : Bool :=
  q.alternatives.any λ alt => σ.subset alt worlds

/-- An issue is inquisitive if it has multiple alternatives.

Non-inquisitive issues have exactly one alternative (assertions).
Inquisitive issues genuinely ask for information. -/
def isInquisitive (q : Issue W) : Bool :=
  q.alternatives.length > 1

/-- An issue is informative if not all states resolve it.

Non-informative issues are resolved by the trivial state (tautologies).
Informative issues rule out some possibilities. -/
def isInformative (q : Issue W) (worlds : List W) : Bool :=
  !q.resolves trivialState worlds

/-- The empty issue: resolved by any info state. -/
def empty : Issue W := { alternatives := [trivialState] }

/-- The absurd issue: resolved only by the absurd state. -/
def absurd : Issue W := { alternatives := [absurdState] }

/-- A proposition is a mention-some answer to Q: it resolves Q by settling
at least one alternative without settling all of them.

In the decision-theoretic setting, mention-some answerhood is defined
relative to a decision problem (see `Core.Agent.DecisionTheory.isMentionSome`).
This definition is the purely logical version from inquisitive semantics:
an answer settles Q partially. -/
def isMentionSomeAnswer (q : Issue W) (answer : InfoState W) (worlds : List W) : Bool :=
  -- Settles at least one alternative (answer ⊆ some alt)
  q.alternatives.any (fun alt => answer.subset alt worlds) &&
  -- Doesn't settle all alternatives
  q.alternatives.any (fun alt => !(answer.subset alt worlds))

/-- A proposition is a mention-all answer to Q: it settles all alternatives
(resolves Q completely by being contained in every alternative). -/
def isMentionAllAnswer (q : Issue W) (answer : InfoState W) (worlds : List W) : Bool :=
  q.alternatives.all (fun alt => answer.subset alt worlds)

/-- Number of alternatives (possible complete answers). -/
def numAlternatives (q : Issue W) : Nat :=
  q.alternatives.length

-- Issue Operations

/-- Intersection of two issues (conjunction): Q ∩ Q'. -/
def inter (q q' : Issue W) (worlds : List W) : Issue W :=
  let pairs := q.alternatives.flatMap λ a =>
    q'.alternatives.filterMap λ a' =>
      let intersection := a.inter a'
      if intersection.isNonEmpty worlds then some intersection else none
  { alternatives := pairs }

/-- Union of two issues (disjunction): Q ∪ Q'. -/
def union (q q' : Issue W) : Issue W :=
  { alternatives := q.alternatives ++ q'.alternatives }

/-- Create an Issue from a polar question.

"Is p true?" has two alternatives: ⟦p⟧ and ⟦¬p⟧. -/
def polar (p : W → Bool) : Issue W :=
  { alternatives := [p, λ w => !p w] }

/-- Create an Issue from a list of alternatives (direct construction). -/
def ofAlternatives (alts : List (InfoState W)) : Issue W :=
  { alternatives := alts }

/-- Create a wh-question Issue: "which x satisfies P?" -/
def which {E : Type*} (domain : List E) (pred : E → W → Bool) : Issue W :=
  { alternatives := domain.map λ e => λ w => pred e w }

/-- Convert an Issue to a QUD: two worlds are equivalent iff they assign the
    same truth value to every alternative.

    This bridges the two question representations in the library:
    - `Issue W` (Hamblin/inquisitive: list of propositional alternatives)
    - `QUD M` (equivalence relation: partition of the meaning space)

    The equivalence relation is: w₁ ~ w₂ iff ∀ alt ∈ q, alt(w₁) = alt(w₂).
    Uses `QUD.ofProject` with the "alternative profile" as the projection. -/
def toQUD (q : Issue W) (name : String := "") : QUD W :=
  QUD.ofProject (fun w => q.alternatives.map (· w)) name

/-- An issue is a genuine partition of the world list: every world satisfies
    exactly one alternative.

    Required for the partition-refinement ↔ question-entailment bridge
    theorem (@cite{groenendijk-stokhof-1984}; see `Core/Partition.lean`). -/
def isPartition (q : Issue W) (worlds : List W) : Bool :=
  worlds.all fun w => (q.alternatives.filter (· w)).length == 1

end Issue

-- Propositional Content of Issues

/-- The informational content of an issue: the union of all alternatives.

This is what the issue "presupposes" — the proposition that SOME alternative
is true. -/
def Issue.infoContent {W : Type*} (q : Issue W) : W → Bool :=
  λ w => q.alternatives.any λ alt => alt w

/-- The highlighted/informational content of an issue. Alias for `infoContent`.

In the standard inquisitive semantics framework, the informational content
(union of all alternatives) IS the highlighted content for declarative
sentences. We keep this alias because @cite{ippolito-kiss-williams-2025} Def. 16 uses "highlighted
content" terminology in defining the at-issue content of discourse *only*. -/
abbrev Issue.highlighted {W : Type*} (q : Issue W) : W → Bool :=
  q.infoContent

-- Width Relation (@cite{deo-thomas-2025})

/-- Proper containment of info states over a finite world list.
    `properlyContains σ σ' worlds` holds when σ' ⊆ σ and σ ∖ σ' ≠ ∅. -/
def properlyContains {W : Type*} (σ σ' : InfoState W) (worlds : List W) : Bool :=
  worlds.all (λ w => !σ' w || σ w) &&
  worlds.any (λ w => σ w && !σ' w)

/-- The width relation between questions (@cite{deo-thomas-2025} (32)).

    `q1.widerThan q2 worlds` holds when q1 is wider (more inquisitive) than q2:
    (a) Same cover: ∪q1 = ∪q2
    (b) No q2-answer is properly contained in any q1-answer
    (c) Some q1-answer is properly contained in some q2-answer

    A wider question makes finer distinctions — its answers are individually
    more specific, allowing more informative resolutions. This is weaker than
    question entailment (@cite{groenendijk-stokhof-1984}) because granularity-based
    construals generally cannot be ordered by entailment strength (fn. 20). -/
def Issue.widerThan {W : Type*} (q1 q2 : Issue W) (worlds : List W) : Bool :=
  -- (a) Same informational content
  worlds.all (λ w => q1.infoContent w == q2.infoContent w) &&
  -- (b) No q2-answer properly contained in any q1-answer
  q2.alternatives.all (λ p2 =>
    !q1.alternatives.any (λ p1 => properlyContains p1 p2 worlds)) &&
  -- (c) Some q1-answer properly contained in some q2-answer
  q1.alternatives.any (λ p1 =>
    q2.alternatives.any (λ p2 => properlyContains p2 p1 worlds))

-- Theorems

/-- Polar questions are always inquisitive (two alternatives). -/
theorem polar_is_inquisitive {W : Type*} (p : W → Bool) :
    (Issue.polar p).isInquisitive = true := rfl

/-- The empty issue is not inquisitive. -/
theorem empty_not_inquisitive {W : Type*} :
    (Issue.empty : Issue W).isInquisitive = false := rfl

end Discourse
