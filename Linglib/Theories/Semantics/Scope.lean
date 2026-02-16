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

import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Core.Interfaces.ScopeTheory

namespace Semantics.Scope

open ScopeTheory

open Semantics.Montague
open Semantics.Lexical.Determiner.Quantifier

-- Scope Configurations

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

-- Connection to ScopeTheory Interface

/-- Convert ScopeConfig to abstract ScopeReading for binary scope -/
def ScopeConfig.toScopeReading (s : ScopeConfig) (op1 op2 : String) : ScopeReading :=
  match s with
  | .surface => ScopeReading.surface [op1, op2]
  | .inverse => ScopeReading.inverse [op1, op2]

/-- Convert list of ScopeConfigs to AvailableScopes (defaults to binary if empty) -/
def toAvailableScopes (configs : List ScopeConfig) (op1 op2 : String) : AvailableScopes :=
  let readings := configs.map (·.toScopeReading op1 op2)
  if h : readings = [] then
    -- Fallback: if empty, provide both readings
    AvailableScopes.binary (ScopeReading.surface [op1, op2]) (ScopeReading.inverse [op1, op2])
  else
    ⟨readings, h⟩

-- Scope Derivation Structure

/--
A derivation that can be interpreted under multiple scope readings.

The same syntactic derivation can yield different semantic values
depending on scope resolution.
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

-- Scoped Form (for HasAvailableScopes interface)

/--
A form (utterance) with scope ambiguity.

This is the Montague-side representation of scope:
- What scope readings are available
- Identifiers for the scope-takers

Note: World-parametric meaning (for RSA) is handled separately in RSA/.
-/
structure ScopedForm where
  /-- Surface form (string representation) -/
  surface : String
  /-- Available scope readings -/
  availableScopes : List ScopeConfig := [.surface, .inverse]
  /-- First scope-taker identifier -/
  scopeTaker1 : String := "op1"
  /-- Second scope-taker identifier -/
  scopeTaker2 : String := "op2"
  deriving Repr

/-- Get available scopes as abstract ScopeReadings -/
def ScopedForm.toAvailableScopes (f : ScopedForm) : AvailableScopes :=
  Semantics.Scope.toAvailableScopes f.availableScopes f.scopeTaker1 f.scopeTaker2

/-- Marker type for Montague scope theory -/
def MontagueScopeTheory : Type := Unit

/-- Montague implements HasAvailableScopes for ScopedForm -/
instance : HasAvailableScopes MontagueScopeTheory ScopedForm where
  availableScopes := ScopedForm.toAvailableScopes

-- Scope Enumeration Utilities

/-- All binary scope configurations -/
def allScopeConfigs : List ScopeConfig := [.surface, .inverse]

/-- All QN scope orderings -/
def allQNScopes : List QNScope := [.forallNeg, .negForall]

/-- Check if scope config yields true under given semantics -/
def scopeYieldsTrue {m : Model}
    (d : ScopeDerivation m .t) (s : ScopeConfig) : Bool :=
  d.meaningAt s

end Semantics.Scope

