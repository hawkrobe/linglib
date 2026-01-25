/-
# Montague Semantics: Scope Enumeration

Infrastructure for representing and enumerating quantifier scope configurations.

## Scope Ambiguity

Sentences with multiple scope-taking elements can have multiple readings:

"Every horse didn't jump"
- Surface scope (∀>¬): ∀x. horse(x) → ¬jump(x)
- Inverse scope (¬>∀): ¬∀x. horse(x) → jump(x)

This module provides:
1. `ScopeConfig` - Enumeration of scope orderings
2. `QNScope` - Specific quantifier-negation scope
3. `ScopeDerivation` - Derivations with multiple scope readings

## References

- May (1985) "Logical Form: Its Structure and Derivation"
- Montague (1973) "The Proper Treatment of Quantification"
- Scontras & Pearl (2021) "When pragmatics matters more for truth-value judgments"
-/

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Quantifiers

namespace Montague.Scope

open Montague
open Montague.Quantifiers

-- ============================================================================
-- Scope Configurations
-- ============================================================================

/-- General scope configuration for two operators -/
inductive ScopeConfig where
  | surface  -- First operator takes wide scope
  | inverse  -- Second operator takes wide scope
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Specific quantifier-negation scope orderings -/
inductive QNScope where
  | forallNeg  -- ∀>¬: Universal scopes over negation
  | negForall  -- ¬>∀: Negation scopes over universal
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert general config to QN-specific scope -/
def toQNScope : ScopeConfig → QNScope
  | .surface => .forallNeg
  | .inverse => .negForall

-- ============================================================================
-- Scope Derivation Structure
-- ============================================================================

/--
A derivation that can be interpreted under multiple scope readings.

The key insight is that the SAME syntactic derivation can yield
DIFFERENT semantic values depending on scope resolution.
-/
structure ScopeDerivation (m : Model) (τ : Ty) where
  /-- Surface form (string representation) -/
  surface : String
  /-- Semantic value as function of scope config -/
  meaningAt : ScopeConfig → m.interpTy τ
  /-- Available scope readings -/
  availableScopes : List ScopeConfig := [.surface, .inverse]

/-- Get all meanings for a scope derivation -/
def ScopeDerivation.allMeanings {m : Model} {τ : Ty}
    (d : ScopeDerivation m τ) : List (ScopeConfig × m.interpTy τ) :=
  d.availableScopes.map λ s => (s, d.meaningAt s)

-- ============================================================================
-- World-Parametric Scope Derivation (for RSA integration)
-- ============================================================================

/--
A scope derivation where meaning is parameterized by both scope AND world.

This is the key structure for RSA integration: rather than evaluating
at a fixed model, we get truth conditions as a function of world state.

`World` is the type of possible world states (e.g., how many horses jumped).
`meaningAt scope world` returns whether the sentence is true under that
scope reading in that world.
-/
structure WorldParametricScopeDerivation (World : Type) where
  /-- Surface form -/
  surface : String
  /-- Truth conditions parameterized by scope and world -/
  meaningAt : ScopeConfig → World → Bool
  /-- Available scope readings -/
  availableScopes : List ScopeConfig := [.surface, .inverse]
  /-- Enumeration of possible worlds -/
  worlds : List World

-- ============================================================================
-- Scope Enumeration Utilities
-- ============================================================================

/-- All binary scope configurations -/
def allScopeConfigs : List ScopeConfig := [.surface, .inverse]

/-- All QN scope orderings -/
def allQNScopes : List QNScope := [.forallNeg, .negForall]

/-- Check if scope config yields true under given semantics -/
def scopeYieldsTrue {m : Model}
    (d : ScopeDerivation m .t) (s : ScopeConfig) : Bool :=
  d.meaningAt s

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Types
- `ScopeConfig`: General binary scope (surface/inverse)
- `QNScope`: Quantifier-negation specific (∀>¬ vs ¬>∀)
- `ScopeDerivation`: Derivation with scope-parameterized meaning (fixed model)
- `WorldParametricScopeDerivation`: Derivation parameterized by scope AND world

### Key Functions
- `toQNScope`: Convert general config to QN-specific
- `ScopeDerivation.allMeanings`: Get all scope readings

### Integration with RSA

This module provides the **Interp** dimension for lifted-variable RSA:
- RSA.Interp = ScopeConfig or QNScope
- RSA.meaning i u w = derivation.meaningAt i w

See `Phenomena/ScontrasPearl2021/Data.lean` for a concrete example
(`everyHorseDidntJump_parametric`) that uses this infrastructure.
-/

end Montague.Scope
