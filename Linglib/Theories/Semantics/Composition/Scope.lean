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

-/

import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Quantification.Quantifier
import Linglib.Core.ScopeTypes

namespace Semantics.Scope

open ScopeTheory

open Semantics.Montague
open Semantics.Quantification.Quantifier

-- Scope Configurations

/-- General scope configuration for two operators -/
inductive ScopeConfig where
  | surface  -- First operator takes wide scope
  | inverse  -- Second operator takes wide scope
  deriving DecidableEq, Repr, Inhabited

/-- Specific quantifier-negation scope orderings -/
inductive QNScope where
  | forallNeg  -- ∀>¬: Universal scopes over negation
  | negForall  -- ¬>∀: Negation scopes over universal
  deriving DecidableEq, Repr, Inhabited

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

-- Scope Enumeration Utilities

/-- All binary scope configurations -/
def allScopeConfigs : List ScopeConfig := [.surface, .inverse]

/-- All QN scope orderings -/
def allQNScopes : List QNScope := [.forallNeg, .negForall]

/-- Check if scope config yields true under given semantics -/
def scopeYieldsTrue {m : Model} [∀ (p : m.interpTy .t), Decidable p]
    (d : ScopeDerivation m .t) (s : ScopeConfig) : Bool :=
  decide (d.meaningAt s)

-- ============================================================================
-- Scope Entailment (@cite{musolino-lidz-2003})
-- ============================================================================

/-- Entailment structure between scope readings.
    Determines whether a quantifier-negation pair is diagnostic for
    scope preferences: independent readings allow contexts where exactly
    one reading is true; nested readings (one entails the other) do not. -/
inductive ScopeEntailment where
  | surfaceEntailsInverse  -- surface ⊂ inverse (e.g., ∀>¬ entails ¬>∀)
  | inverseEntailsSurface  -- inverse ⊂ surface
  | independent            -- neither entails the other (e.g., exact numerals)
  | equivalent             -- readings are extensionally identical
  deriving DecidableEq, Repr, Inhabited

/-- Diagnostic scope pairs allow contexts where exactly one reading is true.
    Only independent pairs are diagnostic; nested or equivalent pairs are not. -/
def ScopeEntailment.isDiagnostic : ScopeEntailment → Bool
  | .independent => true
  | _ => false

/-- Classify scope entailment from truth-value functions over a world list. -/
def classifyScopeEntailment {W : Type}
    (worlds : List W) (surface inverse : W → Bool) : ScopeEntailment :=
  let sEntI := worlds.all (fun w => !surface w || inverse w)
  let iEntS := worlds.all (fun w => !inverse w || surface w)
  match sEntI, iEntS with
  | true, true   => .equivalent
  | true, false  => .surfaceEntailsInverse
  | false, true  => .inverseEntailsSurface
  | false, false => .independent

end Semantics.Scope

