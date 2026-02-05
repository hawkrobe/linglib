/-!
# Scope Theory Interface

Abstract interface for theories that determine available scope readings.
-/

namespace ScopeTheory

/-- A scope reading: an ordering of scope-taking elements. -/
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

/-- The set of available scope readings for a form. -/
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

/-- Typeclass for theories that determine available scope readings. -/
class HasAvailableScopes (T : Type) (Form : Type) where
  /-- Determine available scope readings for a form -/
  availableScopes : Form → AvailableScopes

/-- Convenience function to get available scopes -/
def getAvailableScopes {T Form : Type} [HasAvailableScopes T Form] (form : Form) : AvailableScopes :=
  HasAvailableScopes.availableScopes (T := T) form

/-- A ranked preference over scope readings. -/
structure ScopePreference where
  /-- Readings ranked by preference (most preferred first) -/
  ranking : List ScopeReading
  /-- Scores for each reading (higher = more preferred) -/
  scores : List Float
  /-- Rankings and scores must align -/
  aligned : ranking.length = scores.length := by simp
  deriving Repr

/-- Typeclass for theories that rank scope readings. -/
class HasScopePreference (T : Type) (Form Context : Type) where
  /-- Rank available scope readings in context -/
  preferScopes : Form → Context → AvailableScopes → ScopePreference

/-- Specialized interface for binary scope ambiguity. -/
structure BinaryScopeForm (α : Type) where
  /-- The form/derivation -/
  form : α
  /-- First scope-taker (surface-wide) -/
  scopeTaker1 : String
  /-- Second scope-taker (surface-narrow) -/
  scopeTaker2 : String
  deriving Repr

/-- Binary scope availability: surface only, inverse only, or both. -/
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

/-- Typeclass for binary scope theories. -/
class HasBinaryScope (T : Type) (Form : Type) where
  /-- Determine binary scope availability -/
  binaryScope : BinaryScopeForm Form → BinaryScopeAvailability

end ScopeTheory
