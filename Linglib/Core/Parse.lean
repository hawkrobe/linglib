/-!
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

/-- Positions where EXH can occur in a doubly-quantified sentence. -/
inductive ExhPosition where
  | M : ExhPosition  -- Matrix (whole sentence)
  | O : ExhPosition  -- Outer quantifier
  | I : ExhPosition  -- Inner quantifier
  deriving DecidableEq, Repr, BEq, Hashable

/-- Convert EXH positions to a parse -/
def Parse.fromExhPositions (positions : List ExhPosition) : Parse :=
  let id := if positions.isEmpty then "lit"
    else positions.map (λ p => match p with
      | .M => "M" | .O => "O" | .I => "I") |> String.intercalate ""
  let desc := if positions.isEmpty then "Literal (no EXH)"
    else s!"EXH at {id}"
  ⟨id, desc⟩

/-- All 8 EXH parses for doubly-quantified sentences -/
def exhParses : List Parse :=
  [ Parse.fromExhPositions []
  , Parse.fromExhPositions [.M]
  , Parse.fromExhPositions [.O]
  , Parse.fromExhPositions [.I]
  , Parse.fromExhPositions [.M, .O]
  , Parse.fromExhPositions [.M, .I]
  , Parse.fromExhPositions [.O, .I]
  , Parse.fromExhPositions [.M, .O, .I]
  ]

/-- Check if a parse includes a specific EXH position -/
def Parse.hasExhAt (p : Parse) (pos : ExhPosition) : Bool :=
  let char := match pos with | .M => 'M' | .O => 'O' | .I => 'I'
  p.id.any (· == char)

theorem scope_parses_count : scopeParses.length = 2 := rfl
theorem exh_parses_count : exhParses.length = 8 := rfl

end Core
