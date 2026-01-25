/-
# Scope Theory Interface

Abstract interface for theories that determine available scope readings.

## Overview

Scope ambiguity arises when multiple scope-taking elements (quantifiers,
negation, modals, intensional verbs) can take scope in different orders.
Different theories make different predictions about:

1. **Availability**: Which scope readings are possible for a given form
2. **Preference**: Which reading is preferred (connects to RSA)

## Key Insight

The SAME surface string can have different available readings depending on:
- Derivational structure (CCG: different derivations → different scopes)
- Word order (Dutch/German: verb raising vs verb projection raising)
- Prosody (focus can affect scope preferences)

This interface abstracts over these mechanisms.

## Architecture

- `ScopeTheory` typeclass: what it means to determine available scopes
- `ScopePreference` typeclass: what it means to rank scope readings
- Implementations in Theories/ (CCG, Montague, etc.)

## References

- May (1985) "Logical Form: Its Structure and Derivation"
- Steedman (2000) "The Syntactic Process" Chapter 6
- Scontras & Pearl (2021) "When pragmatics matters more for truth-value judgments"
-/

import Linglib.Theories.Montague.Scope

namespace ScopeTheory

open Montague.Scope

-- ============================================================================
-- Scope Reading Enumeration
-- ============================================================================

/--
A scope reading: an ordering of scope-taking elements.

For n scope-takers, there are n! possible orderings, though not all
may be available in a given sentence.
-/
structure ScopeReading where
  /-- Identifiers for scope-taking elements, in scope order (widest first) -/
  ordering : List String
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The surface scope reading (linear order = scope order) -/
def ScopeReading.surface (elements : List String) : ScopeReading :=
  ⟨elements⟩

/-- Reverse (inverse) scope reading -/
def ScopeReading.inverse (elements : List String) : ScopeReading :=
  ⟨elements.reverse⟩

-- ============================================================================
-- Available Scopes
-- ============================================================================

/--
The set of available scope readings for a form.

This is what a scope theory must determine: given some representation
of the utterance (derivation, LF, surface string + prosody, etc.),
what scope readings are possible?
-/
structure AvailableScopes where
  /-- All available scope readings -/
  readings : List ScopeReading
  /-- At least one reading must be available -/
  nonempty : readings ≠ [] := by simp
  deriving Repr

/-- Singleton: only one reading available -/
def AvailableScopes.singleton (r : ScopeReading) : AvailableScopes :=
  ⟨[r], by simp⟩

/-- Binary: exactly two readings (surface and inverse) -/
def AvailableScopes.binary (surface inverse : ScopeReading) : AvailableScopes :=
  ⟨[surface, inverse], by simp⟩

/-- Check if a specific reading is available -/
def AvailableScopes.hasReading (a : AvailableScopes) (r : ScopeReading) : Bool :=
  a.readings.contains r

/-- Is the scope ambiguous (more than one reading)? -/
def AvailableScopes.isAmbiguous (a : AvailableScopes) : Bool :=
  a.readings.length > 1

-- ============================================================================
-- Scope Theory Typeclass
-- ============================================================================

/--
Typeclass for theories that determine available scope readings.

A scope theory takes some representation of an utterance and determines
which scope readings are available. Different theories use different
representations:

- **CCG**: Derivation structure determines scope
- **May-style LF**: QR determines scope at LF
- **Surface + Prosody**: Information Structure affects scope

Type parameters:
- `T`: The theory marker type
- `Form`: The representation of utterances (derivations, LFs, etc.)
-/
class HasAvailableScopes (T : Type) (Form : Type) where
  /-- Determine available scope readings for a form -/
  availableScopes : Form → AvailableScopes

/-- Convenience function to get available scopes -/
def getAvailableScopes {T Form : Type} [HasAvailableScopes T Form] (form : Form) : AvailableScopes :=
  HasAvailableScopes.availableScopes (T := T) form

-- ============================================================================
-- Scope Preference (connects to RSA)
-- ============================================================================

/--
A ranked preference over scope readings.

This is what RSA/pragmatics determines: given the available readings,
which is preferred in context?
-/
structure ScopePreference where
  /-- Readings ranked by preference (most preferred first) -/
  ranking : List ScopeReading
  /-- Scores for each reading (higher = more preferred) -/
  scores : List Float
  /-- Rankings and scores must align -/
  aligned : ranking.length = scores.length := by simp
  deriving Repr

/--
Typeclass for theories that rank scope readings.

This connects to RSA: given available readings and context,
compute preferences.
-/
class HasScopePreference (T : Type) (Form Context : Type) where
  /-- Rank available scope readings in context -/
  preferScopes : Form → Context → AvailableScopes → ScopePreference

-- ============================================================================
-- Binary Scope (Quantifier-Negation, Two Quantifiers)
-- ============================================================================

/--
Specialized interface for binary scope ambiguity.

Many common cases involve exactly two scope-takers:
- Quantifier + negation (every horse didn't jump)
- Two quantifiers (someone loves everyone)
-/
structure BinaryScopeForm (α : Type) where
  /-- The form/derivation -/
  form : α
  /-- First scope-taker (surface-wide) -/
  scopeTaker1 : String
  /-- Second scope-taker (surface-narrow) -/
  scopeTaker2 : String
  deriving Repr

/--
Binary scope availability: surface only, inverse only, or both.
-/
inductive BinaryScopeAvailability where
  | surfaceOnly   -- Only scopeTaker1 > scopeTaker2
  | inverseOnly   -- Only scopeTaker2 > scopeTaker1
  | ambiguous     -- Both readings available
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert to general AvailableScopes -/
def BinaryScopeAvailability.toAvailableScopes
    (b : BinaryScopeAvailability) (s1 s2 : String) : AvailableScopes :=
  match b with
  | .surfaceOnly => AvailableScopes.singleton (ScopeReading.surface [s1, s2])
  | .inverseOnly => AvailableScopes.singleton (ScopeReading.inverse [s1, s2])
  | .ambiguous => AvailableScopes.binary
      (ScopeReading.surface [s1, s2])
      (ScopeReading.inverse [s1, s2])

/--
Typeclass for binary scope theories.
-/
class HasBinaryScope (T : Type) (Form : Type) where
  /-- Determine binary scope availability -/
  binaryScope : BinaryScopeForm Form → BinaryScopeAvailability

-- ============================================================================
-- Connection to WorldParametricScopeDerivation
-- ============================================================================

/--
Convert AvailableScopes to the list of ScopeConfigs used in RSA.

This bridges the abstract interface to the concrete RSA implementation.
-/
def toScopeConfigs (a : AvailableScopes) : List ScopeConfig :=
  a.readings.filterMap fun r =>
    if r.ordering.length == 2 then
      if r.ordering == r.ordering.reverse then none  -- degenerate case
      else if r == ScopeReading.surface r.ordering then some .surface
      else some .inverse
    else none

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Core Types
- `ScopeReading`: An ordering of scope-takers
- `AvailableScopes`: Set of available readings for a form
- `ScopePreference`: Ranked preferences over readings
- `BinaryScopeAvailability`: Specialized for two scope-takers

### Interfaces (Typeclasses)
- `HasAvailableScopes`: Determine available scope readings
- `HasScopePreference`: Rank readings (connects to RSA)
- `HasBinaryScope`: Specialized binary interface

### Design Principles
1. **Abstract over representations**: CCG derivations, LFs, surface+prosody
2. **Separate availability from preference**: Grammar determines possible,
   pragmatics determines preferred
3. **Connect to RSA**: ScopePreference feeds into RSA computations

### What's NOT Here (belongs in implementations)
- CCG derivation → scope (Theories/CCG/Scope.lean)
- Word order → scope (Theories/CCG/ or Theories/Montague/)
- RSA preference computation (Theories/RSA/)
-/

end ScopeTheory
