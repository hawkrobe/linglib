import Linglib.Theories.Montague.Question.Partition

/-!
# Questions/LiftedTypes.lean

Lifted Question Types (G&S 1984, Chapter VI, Section 6; Partee & Rooth 1983).

## The Problem

Coordination of questions poses a type-theoretic puzzle:
- "Who came?" has type ⟨s,⟨s,t⟩⟩ (partition)
- "Who came or who left?" should coordinate two questions

But the disjunction of two equivalence relations is NOT an equivalence relation!
If w ~₁ v and v ~₂ u, we don't get w ~₁ u or w ~₂ u.

## The Solution: Flexible Types

Partee & Rooth (1983) propose:
1. Categories have a **basic type** plus **predictable lifted types**
2. Lifting rules are general procedures (not ad hoc)
3. Interpret at **minimal type** unless higher type is needed
4. Avoid "generalize to worst case"

For questions:
- **Core type**: Partitions (equivalence relations)
- **Lifted type**: Sets of properties of questions

## Lifting

The lift operation:
```
lift : GSQuestion W → LiftedQuestion W
lift(Q) = λP. P(Q)
```

A lifted question is the set of all properties that hold of the underlying question.

## Coordination in Lifted Types

Once lifted, coordination is straightforward:
```
Q₁ ∨ Q₂ = λP. P ∈ Q₁ ∨ P ∈ Q₂     -- property holds of either
Q₁ ∧ Q₂ = λP. P ∈ Q₁ ∧ P ∈ Q₂     -- property holds of both
```

This avoids the transitivity problem entirely.

## Connection to Continuations (Barker & Shan 2014)

Lifted questions form a **continuation monad**. In Barker & Shan's tower notation,
an expression's type is written as a vertical tower:
```
  C | B
  ─────
    A
```
Reading counter-clockwise from the bottom: the expression functions locally as A,
takes scope over B, and returns C. The flat equivalent is `C ⫽ (A ⫽ B)`.

For questions:
- Core type: `GSQuestion W` (the A)
- Lifted type: `(GSQuestion W → Prop) → Prop` (= `Cont Prop (GSQuestion W)`)

### Monad Operations

The continuation monad has three key operations:
- **pure** (= lift): `λq. λP. P(q)` — wrap a value for any continuation
- **bind** (>>=): `λm. λf. λP. m(λq. f(q)(P))` — sequence scope effects
- **run**: `λm. m(λ_. True)` — close off with trivial continuation

### Why This Matters for Natural Language

Barker & Shan argue continuations unify:
1. **Generalized quantifiers**: DPs as `(e → t) → t`
2. **Dynamic semantics**: Sentences as context updates
3. **Scope displacement**: Why quantifiers can outscope their syntactic position

The key insight: expressions denote functions on their own semantic context,
enabling non-local effects while maintaining compositional, left-to-right evaluation.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Section 6.
- Partee & Rooth (1983). Generalized Conjunction and Type Ambiguity.
- Partee (1986). Noun Phrase Interpretation and Type-Shifting Principles.
- Barker & Shan (2014). Continuations and Natural Language. OUP.
-/

namespace Montague.Question.LiftedTypes

open Montague.Question
open scoped GSQuestion  -- For ⊑ notation

-- Core Definitions

/-- A property of questions: something that can be true or false of a GSQuestion.

Examples:
- "resolves decision problem D"
- "has more than 2 cells"
- "refines question Q'"
-/
def QuestionProperty (W : Type*) := GSQuestion W → Prop

/-- A lifted question: a set of properties (Montague-style generalized quantifier over questions).

In the Partee & Rooth framework, lifting a question Q produces the set of all
properties that Q has:
```
lift(Q) = {P | P(Q)}
```

Coordination then works via set operations on properties. -/
def LiftedQuestion (W : Type*) := QuestionProperty W → Prop

namespace LiftedQuestion

variable {W : Type*}

-- Lifting Operation

/-- Lift a core question to the lifted type.

lift(Q) = λP. P(Q)

The lifted question is the characteristic function of Q's properties. -/
def lift (q : GSQuestion W) : LiftedQuestion W :=
  λ P => P q

/-- A lifted question is "principal" if it comes from lifting a core question. -/
def isPrincipal (lq : LiftedQuestion W) : Prop :=
  ∃ q : GSQuestion W, lq = lift q

-- Continuation Monad Structure (Barker & Shan 2014)

/-!
### The Continuation Monad

The type `LiftedQuestion W = (GSQuestion W → Prop) → Prop` is the continuation
monad `Cont Prop` specialized to questions. We provide:

1. **pure** (alias for lift): the monadic unit
2. **bind** (>>=): monadic sequencing
3. **map**: functorial action
4. **run**: evaluate by closing off the continuation

The monad laws (left/right identity, associativity) hold by construction.
-/

/-- Pure: alias for lift, emphasizing the monadic structure.

In B&S tower notation, this is the LIFT type-shifter:
```
  A      LIFT      B | B
phrase    ⟹       phrase
  x                 [ ]
                    ───
                     x
```
Semantically: `⟦pure(x)⟧ = λκ.κ(x)` -/
abbrev pure : GSQuestion W → LiftedQuestion W := lift

/-- Bind (>>=): monadic sequencing for lifted questions.

Allows a lifted question to "feed into" a function that produces another
lifted question, with proper handling of the continuation.

```
m >>= f  =  λP. m(λq. f(q)(P))
```

In B&S terms, this corresponds to the combination schema where the left
element's scope effect wraps around the right's result. -/
def bind (lq : LiftedQuestion W) (f : GSQuestion W → LiftedQuestion W) : LiftedQuestion W :=
  λ P => lq (λ q => f q P)

/-- Map: functorial action on lifted questions.

Applies a function to the underlying question(s) without changing scope structure. -/
def map (f : GSQuestion W → GSQuestion W) (lq : LiftedQuestion W) : LiftedQuestion W :=
  λ P => lq (λ q => P (f q))

/-- Run: evaluate a lifted question by closing off the continuation.

Applies the trivial continuation (constant True), effectively asking
"does there exist a question satisfying the lifted question?"

For principal lifted questions, this always returns True.
This corresponds to B&S's LOWER when we don't need the value back. -/
def run (lq : LiftedQuestion W) : Prop :=
  lq (λ _ => True)

-- Notation for bind
scoped infixl:55 " >>= " => bind

-- Monad Laws

/-- Left identity: pure q >>= f = f q -/
theorem bind_left_id (q : GSQuestion W) (f : GSQuestion W → LiftedQuestion W) :
    (pure q) >>= f = f q := by
  funext P
  simp only [bind, pure, lift]

/-- Right identity: m >>= pure = m -/
theorem bind_right_id (lq : LiftedQuestion W) :
    lq >>= pure = lq := by
  funext P
  simp only [bind, pure, lift]

/-- Associativity: (m >>= f) >>= g = m >>= (λx. f x >>= g) -/
theorem bind_assoc (lq : LiftedQuestion W)
    (f : GSQuestion W → LiftedQuestion W)
    (g : GSQuestion W → LiftedQuestion W) :
    (lq >>= f) >>= g = lq >>= (λ q => f q >>= g) := by
  funext P
  simp only [bind]

/-- Lift distributes over bind (naturality). -/
theorem lift_bind (q : GSQuestion W) (f : GSQuestion W → LiftedQuestion W) :
    lift q >>= f = f q := bind_left_id q f

/-- Map can be defined via bind and pure. -/
theorem map_via_bind (f : GSQuestion W → GSQuestion W) (lq : LiftedQuestion W) :
    map f lq = lq >>= (λ q => pure (f q)) := by
  funext P
  simp only [map, bind, pure, lift]

/-- Run of a principal lifted question is True. -/
theorem run_principal (q : GSQuestion W) : run (lift q) = True := by
  simp only [run, lift]

-- Coordination (the whole point!)

/-- Disjunction of lifted questions.

(Q₁ ∨ Q₂)(P) iff P holds of Q₁ or P holds of Q₂.

This is well-defined and doesn't require transitivity! -/
def disj (lq1 lq2 : LiftedQuestion W) : LiftedQuestion W :=
  λ P => lq1 P ∨ lq2 P

/-- Conjunction of lifted questions.

(Q₁ ∧ Q₂)(P) iff P holds of Q₁ and P holds of Q₂. -/
def conj (lq1 lq2 : LiftedQuestion W) : LiftedQuestion W :=
  λ P => lq1 P ∧ lq2 P

-- Note: Could add Sup/Inf instances with mathlib import

/-- Disjunction of core questions via lifting. -/
def disjCore (q1 q2 : GSQuestion W) : LiftedQuestion W :=
  disj (lift q1) (lift q2)

/-- Conjunction of core questions via lifting. -/
def conjCore (q1 q2 : GSQuestion W) : LiftedQuestion W :=
  conj (lift q1) (lift q2)

-- Coordination and the Monad

/-- Disjunction distributes over bind from the left.

If we have Q₁ ∨ Q₂ and apply f to each, we get f(Q₁) ∨ f(Q₂). -/
theorem disj_bind_left (lq1 lq2 : LiftedQuestion W)
    (f : GSQuestion W → LiftedQuestion W) :
    (disj lq1 lq2) >>= f = disj (lq1 >>= f) (lq2 >>= f) := by
  funext P
  simp only [disj, bind]

/-- Conjunction distributes over bind from the left. -/
theorem conj_bind_left (lq1 lq2 : LiftedQuestion W)
    (f : GSQuestion W → LiftedQuestion W) :
    (conj lq1 lq2) >>= f = conj (lq1 >>= f) (lq2 >>= f) := by
  funext P
  simp only [conj, bind]

/-- Disjunction of lifted questions via the alternative structure.

This shows disjunction is the "choice" operation for the continuation monad,
corresponding to B&S's treatment of coordination in tower semantics. -/
theorem disj_as_choice (lq1 lq2 : LiftedQuestion W) (P : QuestionProperty W) :
    (disj lq1 lq2) P ↔ lq1 P ∨ lq2 P := Iff.rfl

/-- Map preserves disjunction. -/
theorem map_disj (f : GSQuestion W → GSQuestion W) (lq1 lq2 : LiftedQuestion W) :
    map f (disj lq1 lq2) = disj (map f lq1) (map f lq2) := by
  funext P
  simp only [map, disj]

/-- Map preserves conjunction. -/
theorem map_conj (f : GSQuestion W → GSQuestion W) (lq1 lq2 : LiftedQuestion W) :
    map f (conj lq1 lq2) = conj (map f lq1) (map f lq2) := by
  funext P
  simp only [map, conj]

-- Lowering (when possible)

/-- Lower a lifted question back to core type, if it's principal.

This is a partial operation: non-principal lifted questions (like disjunctions
of non-equivalent questions) cannot be lowered. -/
def lower? (_lq : LiftedQuestion W) : Option (GSQuestion W) :=
  -- In practice, we'd need to search for a witness
  -- For now, this is a specification that can't be computed
  none  -- Placeholder; real implementation needs decidability

/-- A lifted question can be lowered iff it's equivalent to some principal one. -/
def isLowerable (lq : LiftedQuestion W) : Prop :=
  ∃ q : GSQuestion W, ∀ P, lq P ↔ P q

-- Properties and Theorems

/-- Lifting preserves identity: lift is injective on extensionally equal questions. -/
theorem lift_injective (q1 q2 : GSQuestion W)
    (h : lift q1 = lift q2) : ∀ P : QuestionProperty W, P q1 ↔ P q2 := by
  intro P
  have : (lift q1) P = (lift q2) P := congrFun h P
  simp only [lift] at this
  exact Iff.of_eq this

/-- Disjunction is commutative. -/
theorem disj_comm (lq1 lq2 : LiftedQuestion W) :
    disj lq1 lq2 = disj lq2 lq1 := by
  funext P
  simp only [disj]
  exact propext Or.comm

/-- Conjunction is commutative. -/
theorem conj_comm (lq1 lq2 : LiftedQuestion W) :
    conj lq1 lq2 = conj lq2 lq1 := by
  funext P
  simp only [conj]
  exact propext And.comm

/-- Disjunction is associative. -/
theorem disj_assoc (lq1 lq2 lq3 : LiftedQuestion W) :
    disj (disj lq1 lq2) lq3 = disj lq1 (disj lq2 lq3) := by
  funext P
  simp only [disj]
  apply propext
  constructor
  · intro h
    cases h with
    | inl h12 => cases h12 with
      | inl h1 => exact Or.inl h1
      | inr h2 => exact Or.inr (Or.inl h2)
    | inr h3 => exact Or.inr (Or.inr h3)
  · intro h
    cases h with
    | inl h1 => exact Or.inl (Or.inl h1)
    | inr h23 => cases h23 with
      | inl h2 => exact Or.inl (Or.inr h2)
      | inr h3 => exact Or.inr h3

/-- Conjunction is associative. -/
theorem conj_assoc (lq1 lq2 lq3 : LiftedQuestion W) :
    conj (conj lq1 lq2) lq3 = conj lq1 (conj lq2 lq3) := by
  funext P
  simp only [conj]
  apply propext
  constructor
  · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- Lifting distributes over conjunction (principal case).

If Q₁ and Q₂ have a common refinement (Q₁ * Q₂ = compose), then:
conj (lift Q₁) (lift Q₂) is equivalent to lift (Q₁ * Q₂) for "refinement properties". -/
theorem lift_conj_refinement (q1 q2 : GSQuestion W) :
    let q12 := GSQuestion.compose q1 q2  -- compose = meet
    ∀ P : QuestionProperty W,
      (∀ q q', q' ⊑ q → P q → P q') →  -- P is upward closed in refinement
      (conj (lift q1) (lift q2)) P → (lift q12) P := by
  intro q12 P hMono hConj
  simp only [conj, lift] at hConj
  -- q1 * q2 refines both q1 and q2
  -- So if P holds of both and P is monotone, P holds of q1 * q2
  sorry  -- Requires showing q12 ⊑ q1 and using monotonicity

-- Connection to Core Questions

/-- The refinement property, lifted to LiftedQuestion.

A lifted question "refines" another if it entails the other's properties. -/
def liftedRefines (lq1 lq2 : LiftedQuestion W) : Prop :=
  ∀ P, lq2 P → lq1 P

/-- Lifting preserves refinement.

If Q ⊑ Q' at core level, then lift(Q) refines lift(Q') at lifted level. -/
theorem lift_preserves_refinement (q q' : GSQuestion W) (h : q ⊑ q') :
    liftedRefines (lift q) (lift q') := by
  intro P hP'
  simp only [lift] at *
  -- P holds of q', and q refines q'
  -- We need: refinement-respecting properties transfer
  -- This is not automatic; it depends on P being "semantic"
  sorry

-- Answerhood in Lifted Types

/-- An answer to a lifted question: a proposition that resolves some underlying question.

In the lifted setting, "p answers LQ" means:
∃Q ∈ LQ. p is an answer to Q

Note: Full definition requires a world list parameter for toCells. -/
def answers (p : W → Prop) (lq : LiftedQuestion W) (worlds : List W) : Prop :=
  lq (λ q => ∃ cell ∈ q.toCells worlds, ∀ w, cell w = true ↔ p w)

/-- Partial answerhood for lifted questions. -/
def partiallyAnswers (p : W → Prop) (lq : LiftedQuestion W) (worlds : List W) : Prop :=
  lq (λ q => ∃ cell ∈ q.toCells worlds, ∀ w, p w → cell w = true)

end LiftedQuestion

-- Notation

scoped infixl:65 " ⊔ " => LiftedQuestion.disj
scoped infixl:70 " ⊓ " => LiftedQuestion.conj

end Montague.Question.LiftedTypes
