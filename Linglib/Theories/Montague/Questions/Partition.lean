import Linglib.Theories.Montague.Questions.Basic
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

## Refinement

Q refines Q' (Q ⊑ Q') iff knowing Q's answer tells you Q''s answer.
Equivalently: Q's cells are subsets of Q''s cells.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Groenendijk & Stokhof (1997). Questions. Handbook of Logic and Language.
-/

namespace Montague.Questions

-- ============================================================================
-- G&S Question Structure
-- ============================================================================

/-- A G&S-style question: an equivalence relation on worlds.

Two worlds are equivalent iff they give the same answer to the question.
This induces a partition of the world space.

Properties:
- `equiv w w = true` (reflexivity)
- `equiv w v = equiv v w` (symmetry)
- Transitivity follows from these in the Boolean setting -/
structure GSQuestion (W : Type*) where
  /-- Are two worlds equivalent (same answer)? -/
  equiv : W -> W -> Bool
  /-- Equivalence must be reflexive -/
  refl : forall w, equiv w w = true
  /-- Equivalence must be symmetric -/
  symm : forall w v, equiv w v = equiv v w

namespace GSQuestion

variable {W : Type*}

-- ============================================================================
-- Basic Constructors
-- ============================================================================

/-- The finest possible partition (identity). Each world is its own equivalence class.
This is the "maximally informative" question. -/
def exact [DecidableEq W] : GSQuestion W where
  equiv w v := w == v
  refl w := beq_self_eq_true w
  symm w v := by
    simp only [BEq.beq]
    cases Decidable.em (w = v) with
    | inl h => simp [h]
    | inr h => simp [h, Ne.symm h]

/-- The coarsest partition (all worlds equivalent). Conveys no information.
This is the "tautological" question (always answered "yes"). -/
def trivial : GSQuestion W where
  equiv _ _ := true
  refl _ := rfl
  symm _ _ := rfl

/-- Build a question from a projection function.
Two worlds are equivalent iff they have the same value under projection.

Example: `ofProject (fun w => w.weather)` asks "What's the weather?" -/
def ofProject {A : Type} [DecidableEq A] (f : W -> A) : GSQuestion W where
  equiv w v := f w == f v
  refl w := beq_self_eq_true (f w)
  symm w v := by
    simp only [BEq.beq]
    cases Decidable.em (f w = f v) with
    | inl h => simp [h]
    | inr h => simp [h, Ne.symm h]

/-- Build a question from a Boolean predicate (polar question).
Partitions into {yes-worlds} and {no-worlds}. -/
def ofPredicate (p : W -> Bool) : GSQuestion W where
  equiv w v := p w == p v
  refl w := beq_self_eq_true (p w)
  symm w v := by
    simp only [BEq.beq]
    cases p w <;> cases p v <;> rfl

/-- Compose two questions: equivalent iff equivalent under both.
Result is the coarsest common refinement (meet in the lattice). -/
def compose (q1 q2 : GSQuestion W) : GSQuestion W where
  equiv w v := q1.equiv w v && q2.equiv w v
  refl w := by simp [q1.refl, q2.refl]
  symm w v := by rw [q1.symm, q2.symm, Bool.and_comm]

instance : Mul (GSQuestion W) where
  mul := compose

-- ============================================================================
-- Semantic Refinement
-- ============================================================================

/-- Q refines Q' iff Q's equivalence classes are subsets of Q''s.

Intuitively: knowing the Q-answer tells you the Q'-answer.
If two worlds give the same Q-answer, they must give the same Q'-answer.

This is the **semantic entailment** relation for questions. -/
def refines (q q' : GSQuestion W) : Prop :=
  forall w v, q.equiv w v = true -> q'.equiv w v = true

/-- Notation for refinement: Q ⊑ Q' means Q refines Q' -/
scoped infix:50 " ⊑ " => refines

/-- Refinement is reflexive -/
theorem refines_refl (q : GSQuestion W) : q ⊑ q := fun _ _ h => h

/-- Refinement is transitive -/
theorem refines_trans (q1 q2 q3 : GSQuestion W) :
    q1 ⊑ q2 -> q2 ⊑ q3 -> q1 ⊑ q3 :=
  fun h12 h23 w v h1 => h23 w v (h12 w v h1)

/-- Refinement is antisymmetric (up to equivalence of the equiv relation) -/
theorem refines_antisymm (q1 q2 : GSQuestion W) :
    q1 ⊑ q2 -> q2 ⊑ q1 -> (forall w v, q1.equiv w v = q2.equiv w v) := by
  intro h12 h21 w v
  cases hq1 : q1.equiv w v with
  | false =>
    cases hq2 : q2.equiv w v with
    | false => rfl
    | true => exact absurd (h21 w v hq2) (by simp [hq1])
  | true =>
    exact (h12 w v hq1).symm

/-- The exact question refines all questions -/
theorem exact_refines_all [DecidableEq W] (q : GSQuestion W) :
    exact ⊑ q := by
  intro w v h
  simp only [exact, BEq.beq] at h
  have heq : w = v := by
    cases Decidable.em (w = v) with
    | inl heq => exact heq
    | inr hne => simp [hne] at h
  rw [heq]
  exact q.refl v

/-- All questions refine the trivial question -/
theorem all_refine_trivial (q : GSQuestion W) :
    q ⊑ trivial := fun _ _ _ => rfl

/-- Composing with a question refines both factors -/
theorem compose_refines_left (q1 q2 : GSQuestion W) : (q1 * q2) ⊑ q1 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, compose] at h
  cases h1 : q1.equiv w v <;> cases h2 : q2.equiv w v <;> simp_all

theorem compose_refines_right (q1 q2 : GSQuestion W) : (q1 * q2) ⊑ q2 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, compose] at h
  cases h1 : q1.equiv w v <;> cases h2 : q2.equiv w v <;> simp_all

-- ============================================================================
-- Partition Cells
-- ============================================================================

/-- Convert a question to its cells (equivalence classes as characteristic functions).
Given a finite list of worlds, compute the partition cells. -/
def toCells (q : GSQuestion W) (worlds : List W) : List (W -> Bool) :=
  let representatives := worlds.foldl (fun acc w =>
    if acc.any fun r => q.equiv r w then acc else w :: acc
  ) []
  representatives.map fun rep => fun w => q.equiv rep w

/-- Number of cells in the partition (given a finite world set) -/
def numCells (q : GSQuestion W) (worlds : List W) : Nat :=
  (q.toCells worlds).length

/-- Convert to the general Question type -/
def toQuestion (q : GSQuestion W) (worlds : List W) : Question W :=
  q.toCells worlds

/-- Finer questions have at least as many cells -/
theorem refines_numCells_ge (q q' : GSQuestion W) (worlds : List W) :
    q ⊑ q' -> q.numCells worlds >= q'.numCells worlds := by
  sorry -- Requires showing refinement can only increase cell count

-- ============================================================================
-- Connection to QUD
-- ============================================================================

/-- Convert to a Core.QUD on the same space.
Note: QUD is not universe-polymorphic, so this only works for Type. -/
def toQUD {W : Type} (q : GSQuestion W) : QUD W where
  sameAnswer := q.equiv
  name := ""

/-- Convert from a QUD that has the required properties -/
def ofQUD {W : Type} (qud : QUD W)
    (hRefl : forall w, qud.sameAnswer w w = true)
    (hSymm : forall w v, qud.sameAnswer w v = qud.sameAnswer v w) : GSQuestion W where
  equiv := qud.sameAnswer
  refl := hRefl
  symm := hSymm

/-- QUD and GSQuestion are equivalent for well-behaved QUDs -/
theorem toQUD_ofQUD_roundtrip {W : Type} (q : GSQuestion W) :
    ofQUD (toQUD q) q.refl q.symm = q := rfl

end GSQuestion

-- ============================================================================
-- Yes/No and Wh-Questions
-- ============================================================================

/-- A yes/no (polar) question: partitions into {yes-worlds} and {no-worlds}.

Example: "Is it raining?" partitions worlds into rainy and not-rainy. -/
def polarQuestion {W : Type*} (p : W -> Bool) : GSQuestion W :=
  GSQuestion.ofPredicate p

/-- A polar question is equivalent to projecting onto Bool -/
theorem polarQuestion_eq_ofProject {W : Type*} (p : W -> Bool) :
    polarQuestion p = GSQuestion.ofProject p := rfl

/-- A wh-question asks for the value of some function.

Example: "Who came?" = ofProject (fun w => w.guests)
Two worlds are equivalent iff they have the same set of guests. -/
def whQuestion {W A : Type} [DecidableEq A] (f : W -> A) : GSQuestion W :=
  GSQuestion.ofProject f

/-- An alternative question: which of these propositions is true?

Example: "Did John or Mary come?" -/
def alternativeQuestion {W : Type*} [DecidableEq (List Bool)]
    (alts : List (W -> Bool)) : GSQuestion W :=
  GSQuestion.ofProject fun w => alts.map fun p => p w

-- ============================================================================
-- Exhaustivity
-- ============================================================================

/-- A question demands exhaustive answers if its semantics requires
knowing exactly which cell the actual world is in.

This is the default for G&S semantics - all questions are exhaustive. -/
def isExhaustive {W : Type*} (_q : GSQuestion W) : Bool := true

/-- The exhaustive interpretation of a polar question is complete:
answering requires saying "yes" or "no", not "I don't know". -/
theorem polar_exhaustive {W : Type*} (p : W -> Bool) (w : W) :
    (polarQuestion p).numCells [w] <= 2 := by
  sorry -- At most 2 cells

end Montague.Questions
