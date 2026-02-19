import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Theories.Semantics.Questions.Partition

/-!
# Inquisitive Semantics Bridge

Questions as Issues: downward-closed sets of information states.
This generalizes both Hamblin (proposition sets) and partition semantics.

## Theoretical Background

In Inquisitive Semantics (Ciardelli, Groenendijk, Roelofsen), questions are
**issues**: downward-closed sets of information states. An information state
σ is a set of worlds representing what's known.

A state σ **supports** proposition p iff σ ⊆ ⟦p⟧ (every world in σ satisfies p).
A state σ **resolves** issue Q iff σ ∈ Q.

Downward closure ensures: if σ resolves Q, then any more informed σ' ⊆ σ also
resolves Q. This captures the intuition that learning more can't un-resolve
a question.

## Key Definitions

- `InfoState`: σ ⊆ W, a set of worlds representing information
- `Issue`: downward-closed set of info states (the question denotation)
- `alternatives`: maximal resolving states (the "cells" of the issue)

## Connection to Thomas (2026)

Thomas's probabilistic answerhood theory uses inquisitive semantics as the
question representation. The `Issue` type here provides the foundation for
probabilistic answerhood in `ProbabilisticAnswerhood.lean`.

## References

- Ciardelli, Groenendijk & Roelofsen (2018). Inquisitive Semantics. Oxford UP.
- Thomas (2026). A probabilistic, question-based approach to additivity.
- Groenendijk & Roelofsen (2009). Inquisitive Semantics and Pragmatics.
-/

namespace Semantics.Questions.Inquisitive

open Semantics.Questions

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

-- Support Relation

/-- Info state σ supports proposition p iff σ ⊆ ⟦p⟧.

This is the fundamental relation in Inquisitive Semantics:
σ ⊨ p (σ supports p) iff every world in σ makes p true.

If σ is empty, it supports every proposition (ex falso quodlibet). -/
def supports {W : Type*} (σ : InfoState W) (p : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → p w

/-- Proposition entailment via support: p entails q iff every state supporting p
also supports q. -/
def propEntails {W : Type*} (p q : W → Bool) (worlds : List W) : Bool :=
  -- Equivalent to: worlds.all λ w => p w → q w
  entails p q worlds

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

-- Mention-Some Detection

/-- A mention-some issue has multiple alternatives (non-singleton).

Mention-some questions are exactly inquisitive issues: multiple alternatives
each suffice as a complete answer. Example: "Where can I buy coffee?" is
answered by any single coffee location.

Thomas (2026) uses this to characterize partial answerhood. -/
def isMentionSome (q : Issue W) : Bool := q.isInquisitive

/-- A mention-all issue has a single alternative (singleton).

The complete answer requires identifying ALL satisfiers.
Example: "Who came to the party?" (exhaustive reading). -/
def isMentionAll (q : Issue W) : Bool :=
  q.alternatives.length == 1

/-- Number of alternatives (possible complete answers). -/
def numAlternatives (q : Issue W) : Nat :=
  q.alternatives.length

-- Issue Operations

/-- Intersection of two issues (conjunction): Q ∩ Q'.

σ resolves Q ∩ Q' iff σ resolves both Q and Q'.
Alternatives: pairs (a, a') where a ∈ Q.alts, a' ∈ Q'.alts, a ∩ a' non-empty. -/
def inter (q q' : Issue W) (worlds : List W) : Issue W :=
  let pairs := q.alternatives.flatMap λ a =>
    q'.alternatives.filterMap λ a' =>
      let intersection := a.inter a'
      if intersection.isNonEmpty worlds then some intersection else none
  { alternatives := pairs }

/-- Union of two issues (disjunction): Q ∪ Q'.

σ resolves Q ∪ Q' iff σ resolves Q or σ resolves Q'.
Alternatives: alts from Q plus alts from Q'. -/
def union (q q' : Issue W) : Issue W :=
  { alternatives := q.alternatives ++ q'.alternatives }

-- Conversion from Other Question Types

/-- Convert a Hamblin question to an Issue.

Hamblin questions denote sets of propositions (possible answers).
Each proposition becomes an alternative (the set of worlds satisfying it). -/
def ofHamblin (h : Hamblin.QuestionDen W) (candidateProps : List (W → Bool)) : Issue W :=
  let relevantProps := candidateProps.filter h
  { alternatives := relevantProps }

/-- Convert a G&S partition question to an Issue.

A partition question Q partitions worlds into equivalence classes.
Each equivalence class becomes an alternative. -/
def ofPartition (q : GSQuestion W) (worlds : List W) : Issue W :=
  let cells := q.toCells worlds
  { alternatives := cells }

/-- Create an Issue from a polar question.

"Is p true?" has two alternatives: ⟦p⟧ and ⟦¬p⟧. -/
def polar (p : W → Bool) : Issue W :=
  { alternatives := [p, λ w => !p w] }

/-- Create an Issue from a list of alternatives (direct construction). -/
def ofAlternatives (alts : List (InfoState W)) : Issue W :=
  { alternatives := alts }

/-- Create a wh-question Issue: "which x satisfies P?"

Each entity e in the domain creates an alternative: the set of worlds where
e satisfies P. -/
def which {E : Type*} (domain : List E) (pred : E → W → Bool) : Issue W :=
  { alternatives := domain.map λ e => λ w => pred e w }

end Issue

-- Propositional Content of Issues

/-- The informational content of an issue: the union of all alternatives.

This is what the issue "presupposes" - the proposition that SOME alternative
is true. In Thomas (2026), this is used to compute P(A | info(R)). -/
def Issue.infoContent {W : Type*} (q : Issue W) : W → Bool :=
  λ w => q.alternatives.any λ alt => alt w

/-- The highlighted proposition: the disjunction of all alternatives.

Same as infoContent, but emphasizes the "highlighted" reading in
inquisitive semantics. -/
def Issue.highlighted {W : Type*} (q : Issue W) : W → Bool :=
  q.infoContent

-- Theorems

/-- Polar questions are always inquisitive (two alternatives). -/
theorem polar_is_inquisitive {W : Type*} (p : W → Bool) :
    (Issue.polar p).isInquisitive = true := rfl

/-- The empty issue is not inquisitive. -/
theorem empty_not_inquisitive {W : Type*} :
    (Issue.empty : Issue W).isInquisitive = false := rfl

/-- Partition-derived issues preserve cell count as alternative count. -/
theorem ofPartition_preserves_cells {W : Type*} (q : GSQuestion W) (worlds : List W) :
    (Issue.ofPartition q worlds).numAlternatives = (q.toCells worlds).length := rfl

-- GSQuestion ↔ Issue Bridge

/-- Convert a GSQuestion to an Issue via its partition cells.

This is a convenience method wrapping `Issue.ofPartition`. The alternatives
of the resulting issue correspond exactly to the cells of the partition. -/
def toIssue {W : Type*} (q : GSQuestion W) (worlds : List W) : Issue W :=
  Issue.ofPartition q worlds

/-- The alternatives of `toIssue` are exactly the partition cells. -/
theorem toIssue_alternatives {W : Type*} (q : GSQuestion W) (worlds : List W) :
    (toIssue q worlds).alternatives = q.toCells worlds := rfl

end Semantics.Questions.Inquisitive
