/-
# Montague Semantics Derivations

Formal proofs that Montague semantics correctly predicts truth conditions
for basic sentences.

This module connects the theoretical machinery in `Basic.lean` to the
empirical data in `Phenomena/Semantics/TruthConditions.lean`.

## Architecture

- `Phenomena/Semantics/TruthConditions.lean`: theory-neutral empirical data
- `Theories/Montague/Basic.lean`: formal semantic machinery
- THIS FILE: proofs that the theory captures the phenomena
-/

import Linglib.Theories.Montague.Basic
import Linglib.Phenomena.Semantics.TruthConditions

namespace Montague.Derivation.TruthConditions

open Montague
open ToyLexicon
open Phenomena.Semantics.TruthConditions

-- ============================================================================
-- Intransitive Verb Derivations
-- ============================================================================

/-
These theorems prove that ⟦V⟧(⟦NP⟧) yields the truth value that
speakers judge for "NP V" sentences.
-/

/-- "John sleeps" is true (matches johnSleepsTrue) -/
theorem john_sleeps : apply sleeps_sem john_sem = true := rfl

/-- "Mary sleeps" is false (matches marySleepsFalse) -/
theorem mary_not_sleeps : apply sleeps_sem mary_sem = false := rfl

/-- "John laughs" is true (matches johnLaughsTrue) -/
theorem john_laughs : apply laughs_sem john_sem = true := rfl

/-- "Mary laughs" is true (matches maryLaughsTrue) -/
theorem mary_laughs : apply laughs_sem mary_sem = true := rfl

-- ============================================================================
-- Transitive Verb Derivations
-- ============================================================================

/-
For transitive verbs, we compute ⟦V⟧(⟦OBJ⟧)(⟦SUBJ⟧).
Note: object applies first due to standard semantic argument ordering.
-/

/-- "John sees Mary" is true (matches johnSeesMaryTrue) -/
theorem john_sees_mary : apply (apply sees_sem mary_sem) john_sem = true := rfl

/-- "Mary sees John" is true (matches marySeesJohnTrue) -/
theorem mary_sees_john : apply (apply sees_sem john_sem) mary_sem = true := rfl

/-- "John sees John" is false (matches johnSeesJohnFalse) -/
theorem john_not_sees_john : apply (apply sees_sem john_sem) john_sem = false := rfl

/-- "John eats pizza" is true (matches johnEatsPizzaTrue) -/
theorem john_eats_pizza : apply (apply eats_sem ToyEntity.pizza) john_sem = true := rfl

/-- "John eats Mary" is false (matches johnEatsMaryFalse) -/
theorem john_not_eats_mary : apply (apply eats_sem mary_sem) john_sem = false := rfl

/-- "Mary eats pizza" is true (matches maryEatsPizzaTrue) -/
theorem mary_eats_pizza : apply (apply eats_sem ToyEntity.pizza) mary_sem = true := rfl

/-- "John reads book" is true (matches johnReadsBookTrue) -/
theorem john_reads_book : apply (apply reads_sem ToyEntity.book) john_sem = true := rfl

-- ============================================================================
-- Formal Correspondence to Phenomena
-- ============================================================================

/-
These theorems establish exact correspondence between the theory's
predictions and the empirical judgments.
-/

/-- Montague predicts johnSleepsTrue correctly -/
theorem captures_john_sleeps :
    (apply sleeps_sem john_sem = true) ↔ johnSleepsTrue.judgedTrue = true := by
  constructor <;> intro _ <;> rfl

/-- Montague predicts marySleepsFalse correctly -/
theorem captures_mary_sleeps :
    (apply sleeps_sem mary_sem = false) ↔ marySleepsFalse.judgedTrue = false := by
  constructor <;> intro _ <;> rfl

/-- Montague captures the intransitive predication contrast -/
theorem captures_intransitive_contrast :
    apply sleeps_sem john_sem = johnSleepsTrue.judgedTrue ∧
    apply sleeps_sem mary_sem = marySleepsFalse.judgedTrue := by
  constructor <;> rfl

/-- Montague captures the transitive seeing contrast -/
theorem captures_transitive_seeing :
    apply (apply sees_sem mary_sem) john_sem = johnSeesMaryTrue.judgedTrue ∧
    apply (apply sees_sem john_sem) john_sem = johnSeesJohnFalse.judgedTrue := by
  constructor <;> rfl

-- ============================================================================
-- Composition via interpSV and interpSVO
-- ============================================================================

/-
These examples show the same derivations using the composition helpers.
-/

/-- "John sleeps" via interpSV -/
example : interpSV toyModel john_sem sleeps_sem = true := rfl

/-- "Mary sleeps" via interpSV -/
example : interpSV toyModel mary_sem sleeps_sem = false := rfl

/-- "John sees Mary" via interpSVO -/
example : interpSVO toyModel john_sem sees_sem mary_sem = true := rfl

/-- "John sees John" via interpSVO -/
example : interpSVO toyModel john_sem sees_sem john_sem = false := rfl

/-- "John eats pizza" via interpSVO -/
example : interpSVO toyModel john_sem eats_sem ToyEntity.pizza = true := rfl

-- ============================================================================
-- Truth via isTrue predicate
-- ============================================================================

/-- "John sleeps" is true in our model -/
theorem john_sleeps_isTrue : isTrue toyModel (interpSV toyModel john_sem sleeps_sem) := rfl

/-- "John sees Mary" is true in our model -/
theorem john_sees_mary_isTrue : isTrue toyModel (interpSVO toyModel john_sem sees_sem mary_sem) := rfl

/-- "John eats pizza" is true in our model -/
theorem john_eats_pizza_isTrue : isTrue toyModel (interpSVO toyModel john_sem eats_sem ToyEntity.pizza) := rfl

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Coverage

This module proves Montague semantics captures:

### Intransitive Predication
- ⟦sleeps⟧(⟦John⟧) = true  ✓
- ⟦sleeps⟧(⟦Mary⟧) = false ✓
- ⟦laughs⟧(⟦John⟧) = true  ✓
- ⟦laughs⟧(⟦Mary⟧) = true  ✓

### Transitive Predication
- ⟦sees⟧(⟦Mary⟧)(⟦John⟧) = true  ✓
- ⟦sees⟧(⟦John⟧)(⟦Mary⟧) = true  ✓
- ⟦sees⟧(⟦John⟧)(⟦John⟧) = false ✓
- ⟦eats⟧(⟦pizza⟧)(⟦John⟧) = true ✓
- ⟦eats⟧(⟦Mary⟧)(⟦John⟧) = false ✓

### Composition Principle
Function application (⟦α β⟧ = ⟦α⟧(⟦β⟧)) correctly derives
sentence meanings from word meanings.
-/

end Montague.Derivation.TruthConditions

-- Backward compatibility alias
namespace Montague.Derivations
  export Montague.Derivation.TruthConditions (john_sleeps mary_not_sleeps john_laughs mary_laughs
    john_sees_mary mary_sees_john john_not_sees_john john_eats_pizza john_not_eats_mary
    mary_eats_pizza john_reads_book captures_john_sleeps captures_mary_sleeps
    captures_intransitive_contrast captures_transitive_seeing)
end Montague.Derivations
