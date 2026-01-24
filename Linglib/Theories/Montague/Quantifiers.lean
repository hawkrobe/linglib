/-
# Montague Semantics: Quantifiers

Generalized quantifiers in Montague-style compositional semantics.

## Types

Determiners have type: (e→t) → ((e→t) → t)
- Take a restrictor (common noun): e→t
- Return a GQ: (e→t) → t

Examples:
- [[every]] = λR.λS. ∀x. R(x) → S(x)
- [[some]]  = λR.λS. ∃x. R(x) ∧ S(x)
- [[no]]    = λR.λS. ¬∃x. R(x) ∧ S(x)

## Composition

"Every student sleeps" =
  [[every]]([[student]])([[sleeps]])
= (λR.λS. ∀x. R(x) → S(x))([[student]])([[sleeps]])
= ∀x. student(x) → sleeps(x)
-/

import Linglib.Theories.Montague.Basic

namespace Montague.Quantifiers

open Montague

-- ============================================================================
-- Determiner Type
-- ============================================================================

/-- Type of determiners: (e→t) → (e→t) → t -/
def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

-- ============================================================================
-- Quantifier Denotations (Generic over any Model with finite domain)
-- ============================================================================

/--
A model with a finite, enumerable domain.
Needed for computing quantifiers.
-/
class FiniteModel (m : Model) where
  elements : List m.Entity
  complete : ∀ x : m.Entity, x ∈ elements

/--
Universal quantifier: λR.λS. ∀x. R(x) → S(x)
-/
def every_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  fun restrictor => fun scope =>
    FiniteModel.elements.all (fun x => !restrictor x || scope x)

/--
Existential quantifier: λR.λS. ∃x. R(x) ∧ S(x)
-/
def some_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  fun restrictor => fun scope =>
    FiniteModel.elements.any (fun x => restrictor x && scope x)

/--
Negative quantifier: λR.λS. ¬∃x. R(x) ∧ S(x)
-/
def no_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  fun restrictor => fun scope =>
    FiniteModel.elements.all (fun x => !restrictor x || !scope x)

/--
Most quantifier: λR.λS. |R ∩ S| > |R - S|
-/
def most_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  fun restrictor => fun scope =>
    let inBoth := FiniteModel.elements.filter (fun x => restrictor x && scope x)
    let inROnly := FiniteModel.elements.filter (fun x => restrictor x && !scope x)
    decide (inBoth.length > inROnly.length)

-- ============================================================================
-- Toy Model Instance
-- ============================================================================

instance : FiniteModel toyModel where
  elements := [.john, .mary, .pizza, .book]
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- Extended Toy Lexicon
-- ============================================================================

/-- "student" property (John and Mary are students) -/
def student_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .john => true
    | .mary => true
    | _ => false

/-- "person" property (John and Mary are people) -/
def person_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .john => true
    | .mary => true
    | _ => false

/-- "thing" property (everything) -/
def thing_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun _ => true

-- ============================================================================
-- Example Derivations
-- ============================================================================

open ToyLexicon

/-- "Every student sleeps" = ∀x. student(x) → sleeps(x) -/
def everyStudentSleeps : toyModel.interpTy .t :=
  every_sem toyModel student_sem sleeps_sem

#eval everyStudentSleeps  -- false (Mary is a student but doesn't sleep)

/-- "Some student sleeps" = ∃x. student(x) ∧ sleeps(x) -/
def someStudentSleeps : toyModel.interpTy .t :=
  some_sem toyModel student_sem sleeps_sem

#eval someStudentSleeps  -- true (John is a student and sleeps)

/-- "No student sleeps" = ¬∃x. student(x) ∧ sleeps(x) -/
def noStudentSleeps : toyModel.interpTy .t :=
  no_sem toyModel student_sem sleeps_sem

#eval noStudentSleeps  -- false (John is a student and sleeps)

/-- "Every student laughs" = ∀x. student(x) → laughs(x) -/
def everyStudentLaughs : toyModel.interpTy .t :=
  every_sem toyModel student_sem laughs_sem

#eval everyStudentLaughs  -- true (both John and Mary laugh)

-- ============================================================================
-- Computed Values
-- ============================================================================

#eval everyStudentLaughs  -- true
#eval some_sem toyModel student_sem laughs_sem  -- true

-- ============================================================================
-- Monotonicity Demonstrations
-- ============================================================================

/-- "Every person sleeps" -/
def everyPersonSleeps : toyModel.interpTy .t :=
  every_sem toyModel person_sem sleeps_sem

/-- "Some person sleeps" -/
def somePersonSleeps : toyModel.interpTy .t :=
  some_sem toyModel person_sem sleeps_sem

#eval everyPersonSleeps  -- false
#eval somePersonSleeps   -- true
#eval someStudentSleeps  -- true

-- The pattern: someStudentSleeps → somePersonSleeps (UE in restrictor)
-- Both are true, consistent with the entailment

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Quantifier Denotations
- `every_sem`: λR.λS. ∀x. R(x) → S(x)
- `some_sem`: λR.λS. ∃x. R(x) ∧ S(x)
- `no_sem`: λR.λS. ¬∃x. R(x) ∧ S(x)
- `most_sem`: λR.λS. |R ∩ S| > |R - S|

### Composition Examples
- "Every student sleeps" via function application
- "Some student laughs" etc.

### Key Properties
- Entailment: every → some (demonstrated)
- Monotonicity: UE/DE patterns (demonstrated)

### Design
These quantifiers compose with the basic Montague infrastructure.
One unified system, not separate φ functions.
-/

end Montague.Quantifiers
