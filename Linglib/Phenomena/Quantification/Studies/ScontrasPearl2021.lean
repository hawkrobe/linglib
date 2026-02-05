/-
# Scontras & Pearl (2021): Quantifier Scope Ambiguity

Truth-value judgments for scopally ambiguous sentences. Partial-world result (59%) shows listeners integrate both scope readings.

## Main definitions
- `JumpOutcome`, `ScopeReading`, `ExperimentalResult`

## References
- Scontras & Pearl (2021). When pragmatics matters more for truth-value judgments.
-/

namespace Phenomena.Quantification.Studies.ScontrasPearl2021

/-- How many horses jumped (out of 2) -/
inductive JumpOutcome where
  | zero   -- 0 horses jumped
  | one    -- 1 horse jumped
  | two    -- 2 horses jumped (all)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Scope configuration for "every...not" -/
inductive ScopeReading where
  | surface  -- ∀>¬: "For every horse, it didn't jump"
  | inverse  -- ¬>∀: "Not every horse jumped"
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Truth conditions for "Every horse didn't jump" under each scope reading. -/
def scopeTruth : ScopeReading → JumpOutcome → Bool
  | .surface, .zero => true   -- ∀x.¬jump(x): none jumped
  | .surface, .one  => false  -- ∀x.¬jump(x): one jumped, so false
  | .surface, .two  => false  -- ∀x.¬jump(x): all jumped, so false
  | .inverse, .zero => true   -- ¬∀x.jump(x): none jumped, so not all
  | .inverse, .one  => true   -- ¬∀x.jump(x): one jumped, not all
  | .inverse, .two  => false  -- ¬∀x.jump(x): all jumped, so false

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

/-- Zero-horse world: 92% true -/
theorem zero_result : getResult .zero = 92 := rfl

/-- One-horse world: 59% true (mixed judgments) -/
theorem one_result : getResult .one = 59 := rfl

/-- Two-horse world: 18% true -/
theorem two_result : getResult .two = 18 := rfl

/-- Mixed judgments exist for partial worlds. -/
theorem mixed_judgments_exist :
    getResult .one > 20 ∧ getResult .one < 80 := by
  native_decide

/-- Neither scope reading explains all data. -/
theorem neither_scope_fits_all :
    -- Surface predicts one=false, but observed 59%
    (scopeTruth .surface .one = false) ∧
    (getResult .one > 40) ∧
    -- Inverse predicts one=true, but observed only 59%
    (scopeTruth .inverse .one = true) ∧
    (getResult .one < 70) := by
  native_decide

/-- True judgments decrease as horses jump. -/
theorem judgment_ordering :
    getResult .zero > getResult .one ∧
    getResult .one > getResult .two := by
  native_decide

/-- Scope truth table correctness. -/
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

end Phenomena.Quantification.Studies.ScontrasPearl2021
