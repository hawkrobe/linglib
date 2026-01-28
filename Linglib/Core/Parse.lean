/-
# Parse: Grammatical Ambiguity Representation

A `Parse` represents a grammatical reading - one of potentially many ways
the grammar can analyze a sentence.

## Examples of Parse Ambiguity

1. **Scope ambiguity**: surface vs inverse quantifier scope
2. **EXH placement**: where exhaustification operator inserts
3. **Attachment ambiguity**: PP attachment sites
4. **Ellipsis resolution**: different antecedents

## Design

`Parse` is a GENERAL type for any grammatical ambiguity. Specific phenomena
build on this:

- `Exhaustifiable` (NeoGricean): for EXH insertion sites
- Scope readings (Montague): for quantifier scope
- etc.

RSA models use `Parse` as their `Interp` type parameter, regardless of
what kind of grammatical ambiguity it represents.
-/

namespace Core

/-- A grammatical parse represents one reading among potentially many.

    This is a general type - it doesn't imply anything about what KIND
    of ambiguity (scope, EXH, attachment, etc.). -/
structure Parse where
  /-- Unique identifier for this parse -/
  id : String
  /-- Human-readable description -/
  description : String := ""
  deriving DecidableEq, Repr, BEq, Hashable

instance : ToString Parse := ⟨Parse.id⟩

/-- The literal/default parse -/
def Parse.literal : Parse := ⟨"lit", "Literal/default reading"⟩

-- ============================================================================
-- Scope Parses (for quantifier scope ambiguity)
-- ============================================================================

/-- Surface scope parse -/
def Parse.surface : Parse := ⟨"surface", "Surface scope (first QP scopes over second)"⟩

/-- Inverse scope parse -/
def Parse.inverse : Parse := ⟨"inverse", "Inverse scope (second QP scopes over first)"⟩

/-- Standard scope parses for doubly-quantified sentences -/
def scopeParses : List Parse := [Parse.surface, Parse.inverse]

-- ============================================================================
-- EXH Position Parses (for exhaustification)
-- ============================================================================

/-- Positions where EXH can occur in a doubly-quantified sentence.

    For "Q₁ of the Xs V'd Q₂ of the Ys":
    - M (matrix): applies to whole sentence
    - O (outer): applies to outer quantifier Q₁
    - I (inner): applies to inner quantifier Q₂ -/
inductive ExhPosition where
  | M : ExhPosition  -- Matrix (whole sentence)
  | O : ExhPosition  -- Outer quantifier
  | I : ExhPosition  -- Inner quantifier
  deriving DecidableEq, Repr, BEq, Hashable

/-- Convert EXH positions to a parse -/
def Parse.fromExhPositions (positions : List ExhPosition) : Parse :=
  let id := if positions.isEmpty then "lit"
    else positions.map (fun p => match p with
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

-- ============================================================================
-- Verification
-- ============================================================================

theorem scope_parses_count : scopeParses.length = 2 := rfl
theorem exh_parses_count : exhParses.length = 8 := rfl

end Core
