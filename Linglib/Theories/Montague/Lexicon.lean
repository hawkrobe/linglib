/-
# Montague Semantics: Lexicon

Lexical entries that bundle syntactic words with semantic denotations
and scalar alternative information.

This extends Core.Basic.Word with:
- Montague type and denotation
- Horn scale membership (for scalar implicatures)

## Architecture

- Core/Basic.lean: Word = form + Cat + Features (syntax only)
- Montague/Scales.lean: HornScale with ordering and entailment
- This file: SemLexEntry = Word + Ty + denotation + scale position

Pragmatics (NeoGricean, RSA) imports this, not Core directly,
when it needs meanings.
-/

import Linglib.Core.Basic
import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Quantifiers
import Linglib.Theories.Montague.Scales

namespace Montague.Lexicon

open Montague
open Montague.Quantifiers
open Montague.Scales
open Lexicon  -- Core lexicon (Word definitions)

-- ============================================================================
-- Semantic Lexical Entries
-- ============================================================================

/--
Scale membership: which scale an item belongs to and its position.
This links surface forms to the abstract scales in Scales.lean.
-/
inductive ScaleMembership where
  | quantifier (pos : Quantifiers.QuantExpr)
  | connective (pos : Connectives.ConnExpr)
  | modal (pos : Modals.ModalExpr)
  | numeral (pos : Numerals.NumExpr)
  deriving Repr

/--
A semantic lexical entry bundles:
- A syntactic word (from Core)
- A Montague type
- A denotation in that type
- Optional scale membership (for scalar items)
-/
structure SemLexEntry (m : Model) where
  word : Word
  ty : Ty
  denot : m.interpTy ty
  scaleMembership : Option ScaleMembership := none

/-- Get the surface form -/
def SemLexEntry.form {m : Model} (e : SemLexEntry m) : String := e.word.form

/-- Check if this is a scalar item -/
def SemLexEntry.isScalar {m : Model} (e : SemLexEntry m) : Bool := e.scaleMembership.isSome

/-- Get stronger alternatives on the scale (for scalar implicatures) -/
def SemLexEntry.strongerAlternatives {m : Model} (e : SemLexEntry m) : List String :=
  match e.scaleMembership with
  | none => []
  | some (.quantifier pos) =>
    (Scales.strongerAlternatives Quantifiers.quantScale pos).map fun
      | .none_ => "no"
      | .some_ => "some"
      | .most => "most"
      | .all => "all"
  | some (.connective pos) =>
    (Scales.strongerAlternatives Connectives.connScale pos).map fun
      | .or_ => "or"
      | .and_ => "and"
  | some (.modal pos) =>
    (Scales.strongerAlternatives Modals.modalScale pos).map fun
      | .possible => "might"
      | .necessary => "must"
  | some (.numeral pos) =>
    (Scales.strongerAlternatives Numerals.numScale pos).map fun
      | .one => "one"
      | .two => "two"
      | .three => "three"
      | .four => "four"
      | .five => "five"

-- ============================================================================
-- Toy Model Lexicon
-- ============================================================================

open ToyEntity
open ToyLexicon

/-- "some" as determiner: λP.λQ. ∃x. P(x) ∧ Q(x) -/
def some_entry : SemLexEntry toyModel :=
  { word := Lexicon.some_
  , ty := Ty.det
  , denot := some_sem toyModel
  , scaleMembership := some (.quantifier .some_)
  }

/-- "every" / "all" as determiner: λP.λQ. ∀x. P(x) → Q(x) -/
def every_entry : SemLexEntry toyModel :=
  { word := Lexicon.every
  , ty := Ty.det
  , denot := every_sem toyModel
  , scaleMembership := some (.quantifier .all)
  }

/-- "most" as determiner: λP.λQ. |P∩Q| > |P-Q| -/
def most_entry : SemLexEntry toyModel :=
  { word := ⟨"most", Cat.D, { number := Option.some .pl }⟩
  , ty := Ty.det
  , denot := most_sem toyModel
  , scaleMembership := some (.quantifier .most)
  }

/-- "no" as determiner: λP.λQ. ¬∃x. P(x) ∧ Q(x) -/
def no_entry : SemLexEntry toyModel :=
  { word := ⟨"no", Cat.D, {}⟩
  , ty := Ty.det
  , denot := no_sem toyModel
  , scaleMembership := some (.quantifier .none_)  -- on scale but at bottom
  }

/-- "John" as proper name -/
def john_entry : SemLexEntry toyModel :=
  { word := Lexicon.john
  , ty := .e
  , denot := ToyEntity.john
  -- scaleMembership defaults to none (proper names aren't scalar)
  }

/-- "Mary" as proper name -/
def mary_entry : SemLexEntry toyModel :=
  { word := Lexicon.mary
  , ty := .e
  , denot := ToyEntity.mary
  }

/-- "sleeps" as intransitive verb -/
def sleeps_entry : SemLexEntry toyModel :=
  { word := Lexicon.sleeps
  , ty := .e ⇒ .t
  , denot := ToyLexicon.sleeps_sem
  }

/-- "laughs" as intransitive verb -/
def laughs_entry : SemLexEntry toyModel :=
  { word := Lexicon.laughs
  , ty := .e ⇒ .t
  , denot := ToyLexicon.laughs_sem
  }

/-- "student" as common noun -/
def student_entry : SemLexEntry toyModel :=
  { word := ⟨"student", Cat.N, { number := Option.some .sg }⟩
  , ty := .e ⇒ .t
  , denot := student_sem
  }

/-- "students" as common noun (plural) -/
def students_entry : SemLexEntry toyModel :=
  { word := ⟨"students", Cat.N, { number := Option.some .pl }⟩
  , ty := .e ⇒ .t
  , denot := student_sem  -- same denotation as singular
  }

-- ============================================================================
-- Lexicon Lookup
-- ============================================================================

/-- A lexicon maps surface forms to semantic entries -/
def SemLexicon (m : Model) := String → Option (SemLexEntry m)

/-- The toy model lexicon -/
def toyLexicon : SemLexicon toyModel := λ form =>
  match form with
  | "some" => some some_entry
  | "every" => some every_entry
  | "all" => some every_entry  -- "all" and "every" have same denotation
  | "most" => some most_entry
  | "no" => some no_entry
  | "John" => some john_entry
  | "Mary" => some mary_entry
  | "sleeps" => some sleeps_entry
  | "laughs" => some laughs_entry
  | "student" => some student_entry
  | "students" => some students_entry
  | _ => none

/-- Look up scalar alternatives for a form -/
def lookupAlternatives {m : Model} (lex : SemLexicon m) (form : String) : List (SemLexEntry m) :=
  match lex form with
  | none => []
  | some entry =>
    entry.strongerAlternatives.filterMap λ altForm => lex altForm

-- ============================================================================
-- Theorems
-- ============================================================================

/-- "some" is a scalar item -/
theorem some_is_scalar :
    some_entry.isScalar = true := rfl

/-- "every" is a scalar item -/
theorem every_is_scalar :
    every_entry.isScalar = true := rfl

/-- Non-scalar items return empty alternatives -/
theorem john_not_scalar :
    john_entry.isScalar = false := rfl

-- Note: Full evaluation of strongerAlternatives depends on Scales functions
-- which use native_decide. For demonstration, we verify structure is correct.

end Montague.Lexicon
