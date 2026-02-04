/-
# Scontras & Pearl (2021): Quantifier Scope Ambiguity Data

Empirical data on truth-value judgments for scopally ambiguous sentences.

## Key Empirical Finding

"Every horse didn't jump" exhibits scope ambiguity:
- Surface scope: ∀>¬ ("For every horse, it didn't jump" = none jumped)
- Inverse scope: ¬>∀ ("Not every horse jumped" = some didn't)

**Experiment 1 results** (Scontras & Pearl 2021, Table 1):
| Horses jumped | % True |
|---------------|--------|
| 0 (none)      | 92%    |
| 1 (partial)   | 59%    |
| 2 (all)       | 18%    |

The partial-world result (59%) shows listeners integrate BOTH scope readings.
Neither scope alone explains the data:
- Surface scope (∀>¬): predicts 0-horses=true, 1,2=false
- Inverse scope (¬>∀): predicts 0,1-horses=true, 2=false

Reference:
Scontras, G. & Pearl, L. (2021). "When pragmatics matters more for truth-value
judgments: An investigation of quantifier scope ambiguity."
-/

namespace Phenomena.Quantification.Studies.ScontrasPearl2021

-- World States

/-- How many horses jumped (out of 2) -/
inductive JumpOutcome where
  | zero   -- 0 horses jumped
  | one    -- 1 horse jumped
  | two    -- 2 horses jumped (all)
  deriving DecidableEq, BEq, Repr, Inhabited

-- Scope Readings

/-- Scope configuration for "every...not" -/
inductive ScopeReading where
  | surface  -- ∀>¬: "For every horse, it didn't jump"
  | inverse  -- ¬>∀: "Not every horse jumped"
  deriving DecidableEq, BEq, Repr, Inhabited

-- Truth Conditions by Scope

/--
Truth conditions for "Every horse didn't jump" under each scope reading.

Surface (∀>¬): True iff ALL horses failed to jump (none jumped)
Inverse (¬>∀): True iff NOT ALL horses jumped (at least one didn't)
-/
def scopeTruth : ScopeReading → JumpOutcome → Bool
  | .surface, .zero => true   -- ∀x.¬jump(x): none jumped
  | .surface, .one  => false  -- ∀x.¬jump(x): one jumped, so false
  | .surface, .two  => false  -- ∀x.¬jump(x): all jumped, so false
  | .inverse, .zero => true   -- ¬∀x.jump(x): none jumped, so not all
  | .inverse, .one  => true   -- ¬∀x.jump(x): one jumped, not all
  | .inverse, .two  => false  -- ¬∀x.jump(x): all jumped, so false

-- Experimental Data (Scontras & Pearl 2021, Experiment 1)

/-- Experimental result: percentage judged true for each world -/
structure ExperimentalResult where
  world : JumpOutcome
  percentTrue : Nat  -- 0-100
  deriving Repr

/-- Experiment 1 results (Table 1) -/
def exp1Results : List ExperimentalResult :=
  [ { world := .zero, percentTrue := 92 }
  , { world := .one,  percentTrue := 59 }
  , { world := .two,  percentTrue := 18 }
  ]

/-- Extract result for a specific world -/
def getResult (w : JumpOutcome) : Nat :=
  match exp1Results.find? (λ r => r.world == w) with
  | some r => r.percentTrue
  | none => 0

-- Key Empirical Facts

/-- Zero-horse world: 92% true -/
theorem zero_result : getResult .zero = 92 := rfl

/-- One-horse world: 59% true (MIXED JUDGMENTS) -/
theorem one_result : getResult .one = 59 := rfl

/-- Two-horse world: 18% true -/
theorem two_result : getResult .two = 18 := rfl

-- Theorems About the Data

/--
**Key finding**: Mixed judgments exist for partial worlds.

The 59% rate for 1-horse shows neither categorical "true" nor "false".
This is evidence for scope integration/uncertainty.
-/
theorem mixed_judgments_exist :
    getResult .one > 20 ∧ getResult .one < 80 := by
  native_decide

/--
**Neither scope reading explains all data**.

Surface scope predicts: zero=T, one=F, two=F
Inverse scope predicts: zero=T, one=T, two=F

But observed: zero=92%, one=59%, two=18%

The 59% for one-horse falsifies both:
- Surface predicts ~0% true (it's false under ∀>¬)
- Inverse predicts ~100% true (it's true under ¬>∀)
-/
theorem neither_scope_fits_all :
    -- Surface predicts one=false, but observed 59%
    (scopeTruth .surface .one = false) ∧
    (getResult .one > 40) ∧
    -- Inverse predicts one=true, but observed only 59%
    (scopeTruth .inverse .one = true) ∧
    (getResult .one < 70) := by
  native_decide

/--
**Ordering**: True judgments decrease as horses jump.

zero > one > two
-/
theorem judgment_ordering :
    getResult .zero > getResult .one ∧
    getResult .one > getResult .two := by
  native_decide

/--
**Scope truth table correctness**.
-/
theorem surface_scope_truth :
    scopeTruth .surface .zero = true ∧
    scopeTruth .surface .one = false ∧
    scopeTruth .surface .two = false := by
  native_decide

theorem inverse_scope_truth :
    scopeTruth .inverse .zero = true ∧
    scopeTruth .inverse .one = true ∧
    scopeTruth .inverse .two = false := by
  native_decide

-- Summary

/-
## What This Module Provides

### Types
- `JumpOutcome`: World states (0, 1, or 2 horses jumped)
- `ScopeReading`: Surface (∀>¬) vs inverse (¬>∀) scope
- `ExperimentalResult`: Percentage true for each world

### Data
- `exp1Results`: Experimental percentages from Table 1
- `scopeTruth`: Truth conditions for each scope × world

### Key Findings (Theorems)
- `mixed_judgments_exist`: 1-horse world shows 40-80% true (mixed)
- `neither_scope_fits_all`: No single scope explains the pattern
- `judgment_ordering`: zero > one > two (monotonic decrease)

### Theoretical Significance

The partial-world results suggest:
1. Listeners don't commit to a single scope reading
2. They integrate probabilities across readings
3. Pragmatic factors (RSA) influence scope resolution

This motivates the lifted-variable RSA model where interpretation
is a random variable jointly inferred with world state.
-/

end Phenomena.Quantification.Studies.ScontrasPearl2021
