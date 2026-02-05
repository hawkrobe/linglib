/-
# Parse

Grammatical ambiguity representation. A `Parse` represents one reading among
potentially many (scope, EXH placement, attachment, etc.).
-/

namespace Core

/-- A grammatical parse represents one reading among potentially many. -/
structure Parse where
  /-- Unique identifier for this parse -/
  id : String
  /-- Human-readable description -/
  description : String := ""
  deriving DecidableEq, Repr, BEq, Hashable

instance : ToString Parse := ⟨Parse.id⟩

/-- The literal/default parse -/
def Parse.literal : Parse := ⟨"lit", "Literal/default reading"⟩

/-- Surface scope parse -/
def Parse.surface : Parse := ⟨"surface", "Surface scope (first QP scopes over second)"⟩

/-- Inverse scope parse -/
def Parse.inverse : Parse := ⟨"inverse", "Inverse scope (second QP scopes over first)"⟩

/-- Standard scope parses for doubly-quantified sentences -/
def scopeParses : List Parse := [Parse.surface, Parse.inverse]

theorem scope_parses_count : scopeParses.length = 2 := rfl

end Core
