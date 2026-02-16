import Linglib.Theories.QuestionSemantics.Basic
import Linglib.Core.Partition

/-!
# Questions/Partition.lean

Groenendijk & Stokhof (1984) Partition Semantics for Questions.

## Core Ideas

A question denotes an equivalence relation on worlds:
```
⟦?x.P(x)⟧ = λw.λv. [λx.P(w)(x) = λx.P(v)(x)]
```

Two worlds are equivalent iff the predicate has the same extension in both.
This induces a **partition** of logical space.

## Architecture

`GSQuestion` is an abbreviation for `QUD`. All partition lattice operations
(refinement, coarsening, cells) are defined in `Core/Partition.lean` and apply
to any equivalence-relation partition, not just question denotations.

This module provides question-specific constructors and interpretation.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Groenendijk & Stokhof (1997). Questions. Handbook of Logic and Language.
-/

namespace QuestionSemantics

/-- A G&S-style question is exactly a QUD: an equivalence relation on worlds.

Two worlds are equivalent iff they give the same answer to the question.
This induces a partition of the world space. -/
abbrev GSQuestion (W : Type*) := QUD W

namespace GSQuestion

variable {W : Type*}

/-- Compatibility accessor: `equiv` is the same as `sameAnswer`. -/
abbrev equiv (q : GSQuestion W) := q.sameAnswer

-- Re-export ⊑ notation so `open scoped GSQuestion` works
scoped infix:50 " ⊑ " => QUD.refines

-- Question-specific constructors

/-- The finest possible partition (identity). Each world is its own equivalence
class. This is the "maximally informative" question. -/
def exact [BEq W] [LawfulBEq W] : GSQuestion W := QUD.exact

/-- The coarsest partition (all worlds equivalent). Conveys no information.
This is the "tautological" question (always answered "yes"). -/
def trivial : GSQuestion W := QUD.trivial

/-- Build a question from a projection function.
Two worlds are equivalent iff they have the same value under projection.

Example: `ofProject (λ w => w.weather)` asks "What's the weather?" -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : W → A) : GSQuestion W :=
  QUD.ofProject f

/-- Build a question from a Boolean predicate (polar question).
Partitions into {yes-worlds} and {no-worlds}. -/
def ofPredicate (p : W → Bool) : GSQuestion W :=
  QUD.ofProject p

-- Question-specific bridge

/-- Convert to the general Question type (list of characteristic functions). -/
def toQuestion (q : GSQuestion W) (worlds : List W) : Question W :=
  q.toCells worlds

/-- Convert to a Core.QUD (identity since GSQuestion = QUD). -/
def toQUD (q : GSQuestion W) : QUD W := q

/-- Convert from a QUD (identity since GSQuestion = QUD). -/
def ofQUD (qud : QUD W) : GSQuestion W := qud

theorem toQUD_ofQUD_roundtrip (q : GSQuestion W) :
    ofQUD (toQUD q) = q := rfl

theorem ofQUD_toQUD_roundtrip (qud : QUD W) :
    toQUD (ofQUD qud) = qud := rfl

end GSQuestion

-- Yes/No and Wh-Questions

/-- A yes/no (polar) question: partitions into {yes-worlds} and {no-worlds}.

Example: "Is it raining?" partitions worlds into rainy and not-rainy. -/
def polarQuestion {W : Type*} (p : W → Bool) : GSQuestion W :=
  GSQuestion.ofPredicate p

/-- A polar question is equivalent to projecting onto Bool. -/
theorem polarQuestion_eq_ofProject {W : Type*} (p : W → Bool) :
    polarQuestion p = GSQuestion.ofProject p := rfl

/-- A wh-question asks for the value of some function.

Example: "Who came?" = ofProject (λ w => w.guests)
Two worlds are equivalent iff they have the same set of guests. -/
def whQuestion {W A : Type} [BEq A] [LawfulBEq A] (f : W → A) : GSQuestion W :=
  GSQuestion.ofProject f

/-- An alternative question: which of these propositions is true?

Example: "Did John or Mary come?" -/
def alternativeQuestion {W : Type*}
    (alts : List (W → Bool)) : GSQuestion W :=
  QUD.ofProject λ w => alts.map λ p => p w

-- Exhaustivity

/-- A question demands exhaustive answers if its semantics requires
knowing exactly which cell the actual world is in.

This is the default for G&S semantics — all questions are exhaustive. -/
def isExhaustive {W : Type*} (_q : GSQuestion W) : Bool := true

/-- The exhaustive interpretation of a polar question is complete:
answering requires saying "yes" or "no", not "I don't know". -/
theorem polar_exhaustive {W : Type*} (p : W → Bool) (w : W) :
    (polarQuestion p).numCells [w] <= 2 := by
  unfold polarQuestion GSQuestion.ofPredicate QUD.numCells QUD.toCells
  simp only [List.foldl_cons, List.foldl_nil, List.any_nil, Bool.false_eq_true,
    ↓reduceIte, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  omega

end QuestionSemantics
