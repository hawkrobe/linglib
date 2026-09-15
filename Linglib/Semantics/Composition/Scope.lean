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

import Linglib.Semantics.Quantification.Quantifier

namespace Semantics.Scope

open Semantics.Composition
open Quantification

/-! ### Scope readings -/

/-- A scope reading: an ordering of scope-taking elements, widest first. -/
structure ScopeReading where
  /-- Identifiers for the scope-taking elements, in scope order. -/
  ordering : List String
  deriving DecidableEq, Repr, Inhabited

/-- The surface scope reading: linear order is scope order. -/
def ScopeReading.surface (elements : List String) : ScopeReading := ⟨elements⟩

/-- The inverse scope reading. -/
def ScopeReading.inverse (elements : List String) : ScopeReading := ⟨elements.reverse⟩

/-- The nonempty set of scope readings a form makes available. -/
structure AvailableScopes where
  /-- The available readings. -/
  readings : List ScopeReading
  /-- At least one reading is available. -/
  nonempty : readings ≠ [] := by simp
  deriving Repr

/-- A single available reading. -/
def AvailableScopes.singleton (r : ScopeReading) : AvailableScopes := ⟨[r], by simp⟩

/-- Exactly the surface and the inverse reading. -/
def AvailableScopes.binary (surface inverse : ScopeReading) : AvailableScopes :=
  ⟨[surface, inverse], by simp⟩

/-- Whether a reading is available. -/
def AvailableScopes.hasReading (a : AvailableScopes) (r : ScopeReading) : Prop :=
  r ∈ a.readings

instance (a : AvailableScopes) (r : ScopeReading) : Decidable (a.hasReading r) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Whether more than one reading is available. -/
def AvailableScopes.isAmbiguous (a : AvailableScopes) : Prop := a.readings.length > 1

instance (a : AvailableScopes) : Decidable a.isAmbiguous :=
  inferInstanceAs (Decidable (_ > _))

/-- Binary scope availability: the surface reading only, the inverse only, or both. -/
inductive BinaryScopeAvailability where
  | surfaceOnly
  | inverseOnly
  | ambiguous
  deriving DecidableEq, Repr, Inhabited

/-- The available readings of a binary availability over two named scope-takers. -/
def BinaryScopeAvailability.toAvailableScopes
    (b : BinaryScopeAvailability) (s₁ s₂ : String) : AvailableScopes :=
  match b with
  | .surfaceOnly => AvailableScopes.singleton (ScopeReading.surface [s₁, s₂])
  | .inverseOnly => AvailableScopes.singleton (ScopeReading.inverse [s₁, s₂])
  | .ambiguous =>
    AvailableScopes.binary (ScopeReading.surface [s₁, s₂]) (ScopeReading.inverse [s₁, s₂])

/-! ### Scope configurations -/

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
structure ScopeDerivation (α : Type) where
  /-- Surface form (string representation) -/
  surface : String
  /-- Semantic value as function of scope config -/
  meaningAt : ScopeConfig → α
  /-- Available scope readings -/
  availableScopes : List ScopeConfig := [.surface, .inverse]

/-- Get all meanings for a scope derivation -/
def ScopeDerivation.allMeanings {α : Type} (d : ScopeDerivation α) : List (ScopeConfig × α) :=
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
def scopeYieldsTrue (d : ScopeDerivation Prop) [∀ s, Decidable (d.meaningAt s)]
    (s : ScopeConfig) : Bool :=
  decide (d.meaningAt s)

-- ============================================================================
-- Scope Entailment ([musolino-lidz-2003])
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

