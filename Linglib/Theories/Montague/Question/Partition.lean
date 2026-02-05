import Linglib.Theories.Montague.Question.Basic
import Linglib.Core.QUD

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

## Unification with QUD

`GSQuestion` is now an abbreviation for `QUD`. Both represent the same concept:
an equivalence relation that partitions a space. The unification ensures:
- Single source of truth for partition/equivalence semantics
- All theorems proven for QUD apply to GSQuestion
- No duplication of structure definitions

## Refinement

Q refines Q' (Q ⊑ Q') iff knowing Q's answer tells you Q''s answer.
Equivalently: Q's cells are subsets of Q''s cells.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Groenendijk & Stokhof (1997). Questions. Handbook of Logic and Language.
-/

namespace Montague.Question

-- GSQuestion = QUD (Unified)

/-- A G&S-style question is exactly a QUD: an equivalence relation on worlds.

Two worlds are equivalent iff they give the same answer to the question.
This induces a partition of the world space.

Now unified with `Core.QUD` to ensure single source of truth.

Note: Uses `Type` (not `Type`) to match QUD's definition. -/
abbrev GSQuestion (W : Type*) := QUD W

namespace GSQuestion

variable {W : Type*}

/-- Compatibility accessor: `equiv` is the same as `sameAnswer` -/
abbrev equiv (q : GSQuestion W) := q.sameAnswer

-- Basic Constructors (delegating to QUD)

/-- The finest possible partition (identity). Each world is its own equivalence class.
This is the "maximally informative" question. -/
def exact [BEq W] [LawfulBEq W] : GSQuestion W := QUD.exact

/-- The coarsest partition (all worlds equivalent). Conveys no information.
This is the "tautological" question (always answered "yes"). -/
def trivial [BEq W] : GSQuestion W := QUD.trivial

/-- Build a question from a projection function.
Two worlds are equivalent iff they have the same value under projection.

Example: `ofProject (λ w => w.weather)` asks "What's the weather?" -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : W → A) : GSQuestion W :=
  QUD.ofProject f

/-- Build a question from a Boolean predicate (polar question).
Partitions into {yes-worlds} and {no-worlds}. -/
def ofPredicate (p : W → Bool) : GSQuestion W :=
  QUD.ofProject p

/-- Compose two questions: equivalent iff equivalent under both.
Result is the coarsest common refinement (meet in the lattice). -/
def compose (q1 q2 : GSQuestion W) : GSQuestion W :=
  QUD.compose q1 q2

instance [BEq W] : Mul (GSQuestion W) where
  mul := compose

-- Semantic Refinement

/-- Q refines Q' iff Q's equivalence classes are subsets of Q''s.

Intuitively: knowing the Q-answer tells you the Q'-answer.
If two worlds give the same Q-answer, they must give the same Q'-answer.

This is the **semantic entailment** relation for questions. -/
def refines (q q' : GSQuestion W) : Prop :=
  ∀ w v, q.sameAnswer w v = true → q'.sameAnswer w v = true

/-- Notation for refinement: Q ⊑ Q' means Q refines Q' -/
scoped infix:50 " ⊑ " => refines

/-- Refinement is reflexive -/
theorem refines_refl (q : GSQuestion W) : q ⊑ q := λ _ _ h => h

/-- Refinement is transitive -/
theorem refines_trans (q1 q2 q3 : GSQuestion W) :
    q1 ⊑ q2 → q2 ⊑ q3 → q1 ⊑ q3 :=
  λ h12 h23 w v h1 => h23 w v (h12 w v h1)

/-- Refinement is antisymmetric (up to equivalence of the equiv relation) -/
theorem refines_antisymm (q1 q2 : GSQuestion W) :
    q1 ⊑ q2 → q2 ⊑ q1 → (∀ w v, q1.sameAnswer w v = q2.sameAnswer w v) := by
  intro h12 h21 w v
  cases hq1 : q1.sameAnswer w v with
  | false =>
    cases hq2 : q2.sameAnswer w v with
    | false => rfl
    | true => exact absurd (h21 w v hq2) (by simp [hq1])
  | true =>
    exact (h12 w v hq1).symm

/-- The exact question refines all questions -/
theorem exact_refines_all [BEq W] [LawfulBEq W] (q : GSQuestion W) :
    exact ⊑ q := by
  intro w v h
  simp only [exact, QUD.exact] at h
  have heq : w = v := by
    rw [beq_iff_eq] at h
    exact h
  rw [heq]
  exact q.refl v

/-- All questions refine the trivial question -/
theorem all_refine_trivial [BEq W] (q : GSQuestion W) :
    q ⊑ trivial := λ _ _ _ => rfl

/-- Composing with a question refines both factors -/
theorem compose_refines_left (q1 q2 : GSQuestion W) : (q1 * q2) ⊑ q1 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, compose, QUD.compose] at h
  cases h1 : q1.sameAnswer w v <;> cases h2 : q2.sameAnswer w v <;> simp_all

theorem compose_refines_right (q1 q2 : GSQuestion W) : (q1 * q2) ⊑ q2 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, compose, QUD.compose] at h
  cases h1 : q1.sameAnswer w v <;> cases h2 : q2.sameAnswer w v <;> simp_all

-- Partition Cells (delegating to QUD.cell)

/-- Convert a question to its cells (equivalence classes as characteristic functions).
Given a finite list of worlds, compute the partition cells. -/
def toCells (q : GSQuestion W) (worlds : List W) : List (W → Bool) :=
  let representatives := worlds.foldl (λ acc w =>
    if acc.any λ r => q.sameAnswer r w then acc else w :: acc
  ) []
  representatives.map λ rep => λ w => q.sameAnswer rep w

/-- Number of cells in the partition (given a finite world set) -/
def numCells (q : GSQuestion W) (worlds : List W) : Nat :=
  (q.toCells worlds).length

/-- Convert to the general Question type -/
def toQuestion (q : GSQuestion W) (worlds : List W) : Question W :=
  q.toCells worlds

/-- Finer questions have at least as many cells -/
theorem refines_numCells_ge (q q' : GSQuestion W) (worlds : List W) :
    q ⊑ q' → q.numCells worlds >= q'.numCells worlds := by
  sorry -- Requires showing refinement can only increase cell count

-- Connection to QUD (now trivial since GSQuestion = QUD)

/-- Convert to a Core.QUD (identity since GSQuestion = QUD) -/
def toQUD (q : GSQuestion W) : QUD W := q

/-- Convert from a QUD (identity since GSQuestion = QUD) -/
def ofQUD (qud : QUD W) : GSQuestion W := qud

/-- Round-trip is identity -/
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

/-- A polar question is equivalent to projecting onto Bool -/
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

This is the default for G&S semantics - all questions are exhaustive. -/
def isExhaustive {W : Type*} (_q : GSQuestion W) : Bool := true

/-- The exhaustive interpretation of a polar question is complete:
answering requires saying "yes" or "no", not "I don't know". -/
theorem polar_exhaustive {W : Type*} (p : W → Bool) (w : W) :
    (polarQuestion p).numCells [w] <= 2 := by
  sorry -- At most 2 cells

end Montague.Question
