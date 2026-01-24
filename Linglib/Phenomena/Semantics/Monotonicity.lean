/-
# Monotonicity Inference Judgments

Empirical data: which inferences involving set inclusion do people accept?

Monotonicity determines whether inferences "go through" when you
substitute a subset for a superset (or vice versa).

## Key Pattern

Given: dogs ⊆ animals

- "Every dog barks" → "Every animal barks"?  NO (DE in restrictor)
- "Some dog barks" → "Some animal barks"?   YES (UE in restrictor)
- "No dog barks" → "No animal barks"?        NO (DE in restrictor)

## Data Source

- Ladusaw (1980) on polarity sensitivity
- van Benthem (1986) on monotonicity
- Barwise & Cooper (1981) on generalized quantifiers
-/

import Linglib.Phenomena.EmpiricalData

namespace Phenomena.Semantics.Monotonicity

open Phenomena

-- ============================================================================
-- Monotonicity Judgment Data Structure
-- ============================================================================

/--
Type of monotonicity position being tested.
-/
inductive Position where
  | restrictor  -- First argument of determiner: "Every [STUDENT] smokes"
  | scope       -- Second argument of determiner: "Every student [SMOKES]"
  deriving DecidableEq, BEq, Repr

/--
Direction of the set inclusion in the inference.
-/
inductive Direction where
  | upward    -- Subset to superset (dogs → animals)
  | downward  -- Superset to subset (animals → dogs)
  deriving DecidableEq, BEq, Repr

/--
A monotonicity inference judgment.
-/
structure MonotonicityJudgment where
  /-- The determiner being tested -/
  determiner : String
  /-- Which argument position -/
  position : Position
  /-- Direction of inference -/
  direction : Direction
  /-- The premise -/
  premise : String
  /-- The conclusion -/
  conclusion : String
  /-- Given set relation (e.g., "dogs ⊆ animals") -/
  setRelation : String
  /-- Do speakers judge this as valid? -/
  judgedValid : Bool
  deriving Repr

-- ============================================================================
-- "Every" Monotonicity
-- ============================================================================

/--
"Every" is DE in restrictor: dogs ⊆ animals, but "every animal" ↛ "every dog"

Actually the VALID direction is: every animal barks → every dog barks
(If every animal barks, and dogs are animals, then every dog barks)
-/
def everyRestrictorDE : MonotonicityJudgment :=
  { determiner := "every"
  , position := .restrictor
  , direction := .downward  -- animals → dogs is valid
  , premise := "Every animal barks"
  , conclusion := "Every dog barks"
  , setRelation := "dogs ⊆ animals"
  , judgedValid := true
  }

/--
"Every" restrictor: upward is INVALID.

"Every dog barks" ↛ "Every animal barks"
-/
def everyRestrictorNotUE : MonotonicityJudgment :=
  { determiner := "every"
  , position := .restrictor
  , direction := .upward
  , premise := "Every dog barks"
  , conclusion := "Every animal barks"
  , setRelation := "dogs ⊆ animals"
  , judgedValid := false
  }

/--
"Every" is UE in scope: barks ⊆ makes_noise

"Every dog barks" → "Every dog makes noise"
-/
def everyScopeUE : MonotonicityJudgment :=
  { determiner := "every"
  , position := .scope
  , direction := .upward
  , premise := "Every dog barks"
  , conclusion := "Every dog makes noise"
  , setRelation := "barks ⊆ makes_noise"
  , judgedValid := true
  }

-- ============================================================================
-- "Some" Monotonicity
-- ============================================================================

/--
"Some" is UE in restrictor: dogs ⊆ animals

"Some dog barks" → "Some animal barks"
-/
def someRestrictorUE : MonotonicityJudgment :=
  { determiner := "some"
  , position := .restrictor
  , direction := .upward
  , premise := "Some dog barks"
  , conclusion := "Some animal barks"
  , setRelation := "dogs ⊆ animals"
  , judgedValid := true
  }

/--
"Some" is UE in scope: barks ⊆ makes_noise

"Some dog barks" → "Some dog makes noise"
-/
def someScopeUE : MonotonicityJudgment :=
  { determiner := "some"
  , position := .scope
  , direction := .upward
  , premise := "Some dog barks"
  , conclusion := "Some dog makes noise"
  , setRelation := "barks ⊆ makes_noise"
  , judgedValid := true
  }

-- ============================================================================
-- "No" Monotonicity
-- ============================================================================

/--
"No" is DE in restrictor: dogs ⊆ animals

"No animal barks" → "No dog barks"
-/
def noRestrictorDE : MonotonicityJudgment :=
  { determiner := "no"
  , position := .restrictor
  , direction := .downward
  , premise := "No animal barks"
  , conclusion := "No dog barks"
  , setRelation := "dogs ⊆ animals"
  , judgedValid := true
  }

/--
"No" is DE in scope: barks ⊆ makes_noise

"No dog makes noise" → "No dog barks"
-/
def noScopeDE : MonotonicityJudgment :=
  { determiner := "no"
  , position := .scope
  , direction := .downward
  , premise := "No dog makes noise"
  , conclusion := "No dog barks"
  , setRelation := "barks ⊆ makes_noise"
  , judgedValid := true
  }

/--
"No" scope: upward is INVALID.

"No dog barks" ↛ "No dog makes noise"
-/
def noScopeNotUE : MonotonicityJudgment :=
  { determiner := "no"
  , position := .scope
  , direction := .upward
  , premise := "No dog barks"
  , conclusion := "No dog makes noise"
  , setRelation := "barks ⊆ makes_noise"
  , judgedValid := false
  }

-- ============================================================================
-- Collected Data
-- ============================================================================

/-- All monotonicity judgments -/
def allMonotonicityJudgments : List MonotonicityJudgment :=
  [ everyRestrictorDE
  , everyRestrictorNotUE
  , everyScopeUE
  , someRestrictorUE
  , someScopeUE
  , noRestrictorDE
  , noScopeDE
  , noScopeNotUE
  ]

-- ============================================================================
-- Summary Patterns
-- ============================================================================

/--
Summary of determiner monotonicity patterns.
-/
structure MonotonicityPattern where
  determiner : String
  restrictorUE : Bool  -- Is restrictor position UE?
  scopeUE : Bool       -- Is scope position UE?
  deriving Repr

/-- "Every": DE restrictor, UE scope -/
def everyPattern : MonotonicityPattern :=
  { determiner := "every", restrictorUE := false, scopeUE := true }

/-- "Some": UE restrictor, UE scope -/
def somePattern : MonotonicityPattern :=
  { determiner := "some", restrictorUE := true, scopeUE := true }

/-- "No": DE restrictor, DE scope -/
def noPattern : MonotonicityPattern :=
  { determiner := "no", restrictorUE := false, scopeUE := false }

/-- All patterns -/
def allPatterns : List MonotonicityPattern :=
  [everyPattern, somePattern, noPattern]

-- ============================================================================
-- Theorems About the Data
-- ============================================================================

/-- "Every" has the classic DE-restrictor, UE-scope pattern -/
theorem everyMonotonicity :
    everyRestrictorDE.judgedValid = true ∧
    everyRestrictorNotUE.judgedValid = false ∧
    everyScopeUE.judgedValid = true := by
  native_decide

/-- "Some" is UE in both positions -/
theorem someMonotonicity :
    someRestrictorUE.judgedValid = true ∧
    someScopeUE.judgedValid = true := by
  native_decide

/-- "No" is DE in both positions -/
theorem noMonotonicity :
    noRestrictorDE.judgedValid = true ∧
    noScopeDE.judgedValid = true ∧
    noScopeNotUE.judgedValid = false := by
  native_decide

-- ============================================================================
-- Connection to Scalar Implicatures
-- ============================================================================

/-
## Why Monotonicity Matters for Pragmatics

DE positions BLOCK scalar implicatures:

In UE: "Some students passed" → SI: "Not all passed"
In DE: "No student ate some cookies" → NO SI about "all"

This is because in DE contexts, the scale reverses:
- UE: all ⊢ some (all is stronger)
- DE: some ⊢ all (some is stronger!)

The empirical monotonicity judgments here are the FOUNDATION for
understanding why scalar implicatures are blocked in certain contexts.

Theories/Semantics/Entailment.lean should prove it predicts these patterns.
Theories/NeoGricean/ScalarImplicatures.lean uses this to predict SI blocking.
-/

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `MonotonicityJudgment`: determiner, position, direction, validity
- `MonotonicityPattern`: summary of UE/DE for each position

### Empirical Data
- "Every": DE restrictor, UE scope
- "Some": UE both
- "No": DE both

### Key Patterns
- `everyMonotonicity`: restrictor DE, scope UE
- `someMonotonicity`: both UE
- `noMonotonicity`: both DE

### Theory Connection
- Theories/Semantics/ should predict these patterns
- Theories/NeoGricean/ uses these to predict SI blocking in DE contexts
-/

end Phenomena.Semantics.Monotonicity
