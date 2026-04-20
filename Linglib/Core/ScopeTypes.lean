/-!
# Scope Types

Theory-neutral data types for scope readings and preferences.
-/

namespace ScopeTheory

/-- A scope reading: an ordering of scope-taking elements. -/
structure ScopeReading where
  /-- Identifiers for scope-taking elements, in scope order (widest first) -/
  ordering : List String
  deriving DecidableEq, Repr, Inhabited

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
def AvailableScopes.hasReading (a : AvailableScopes) (r : ScopeReading) : Prop :=
  r ∈ a.readings

instance (a : AvailableScopes) (r : ScopeReading) : Decidable (a.hasReading r) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Is the scope ambiguous (more than one reading)? -/
def AvailableScopes.isAmbiguous (a : AvailableScopes) : Prop :=
  a.readings.length > 1

instance (a : AvailableScopes) : Decidable a.isAmbiguous :=
  inferInstanceAs (Decidable (_ > _))

/-- A ranked preference over scope readings. -/
structure ScopePreference where
  /-- Readings ranked by preference (most preferred first) -/
  ranking : List ScopeReading
  /-- Scores for each reading (higher = more preferred) -/
  scores : List Float
  /-- Rankings and scores must align -/
  aligned : ranking.length = scores.length := by simp
  deriving Repr

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
  deriving DecidableEq, Repr, Inhabited

/-- Convert to general AvailableScopes -/
def BinaryScopeAvailability.toAvailableScopes
    (b : BinaryScopeAvailability) (s1 s2 : String) : AvailableScopes :=
  match b with
  | .surfaceOnly => AvailableScopes.singleton (ScopeReading.surface [s1, s2])
  | .inverseOnly => AvailableScopes.singleton (ScopeReading.inverse [s1, s2])
  | .ambiguous => AvailableScopes.binary
      (ScopeReading.surface [s1, s2])
      (ScopeReading.inverse [s1, s2])

end ScopeTheory
