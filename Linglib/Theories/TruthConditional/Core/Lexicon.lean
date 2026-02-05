/-
# Montague Semantics: Lexicon

Lexical entries with semantic denotations and scalar alternatives.

## Main definitions

`ScaleMembership`, `SemLexEntry`, `SemLexicon`, `toyLexicon`

## References

Montague (1973)
-/

import Linglib.Core.Basic
import Linglib.Theories.TruthConditional.Basic
import Linglib.Theories.TruthConditional.Determiner.Quantifier
import Linglib.Core.Scales

namespace TruthConditional.Core

open TruthConditional
open TruthConditional.Determiner.Quantifier
open Core.Scales

private def word_some : Word := ⟨"some", Cat.D, {}⟩
private def word_every : Word := ⟨"every", Cat.D, { number := some .sg }⟩
private def word_john : Word := ⟨"John", Cat.D, { number := some .sg, person := some .third }⟩
private def word_mary : Word := ⟨"Mary", Cat.D, { number := some .sg, person := some .third }⟩
private def word_sleeps : Word := ⟨"sleeps", Cat.V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
private def word_laughs : Word := ⟨"laughs", Cat.V, { valence := some .intransitive, number := some .sg, person := some .third }⟩

/-- Scale membership position -/
inductive ScaleMembership where
  | quantifier (pos : Quantifiers.QuantExpr)
  | connective (pos : Connectives.ConnExpr)
  | modal (pos : Modals.ModalExpr)
  | numeral (pos : Numerals.NumExpr)
  deriving Repr

/-- Semantic lexical entry -/
structure SemLexEntry (m : Model) where
  word : Word
  ty : Ty
  denot : m.interpTy ty
  scaleMembership : Option ScaleMembership := none

def SemLexEntry.form {m : Model} (e : SemLexEntry m) : String := e.word.form
def SemLexEntry.isScalar {m : Model} (e : SemLexEntry m) : Bool := e.scaleMembership.isSome

def SemLexEntry.strongerAlternatives {m : Model} (e : SemLexEntry m) : List String :=
  match e.scaleMembership with
  | none => []
  | some (.quantifier pos) =>
    (Core.Scales.strongerAlternatives Quantifiers.quantScale pos).map λ
      | .none_ => "no"
      | .some_ => "some"
      | .most => "most"
      | .all => "all"
  | some (.connective pos) =>
    (Core.Scales.strongerAlternatives Connectives.connScale pos).map λ
      | .or_ => "or"
      | .and_ => "and"
  | some (.modal pos) =>
    (Core.Scales.strongerAlternatives Modals.modalScale pos).map λ
      | .possible => "might"
      | .necessary => "must"
  | some (.numeral pos) =>
    (Core.Scales.strongerAlternatives Numerals.numScale pos).map λ
      | .one => "one"
      | .two => "two"
      | .three => "three"
      | .four => "four"
      | .five => "five"

open ToyEntity
open ToyLexicon

def some_entry : SemLexEntry toyModel :=
  { word := word_some
  , ty := Ty.det
  , denot := some_sem toyModel
  , scaleMembership := some (.quantifier .some_)
  }

def every_entry : SemLexEntry toyModel :=
  { word := word_every
  , ty := Ty.det
  , denot := every_sem toyModel
  , scaleMembership := some (.quantifier .all)
  }

def most_entry : SemLexEntry toyModel :=
  { word := ⟨"most", Cat.D, { number := Option.some .pl }⟩
  , ty := Ty.det
  , denot := most_sem toyModel
  , scaleMembership := some (.quantifier .most)
  }

def no_entry : SemLexEntry toyModel :=
  { word := ⟨"no", Cat.D, {}⟩
  , ty := Ty.det
  , denot := no_sem toyModel
  , scaleMembership := some (.quantifier .none_)
  }

def john_entry : SemLexEntry toyModel :=
  { word := word_john
  , ty := .e
  , denot := ToyEntity.john
  }

def mary_entry : SemLexEntry toyModel :=
  { word := word_mary
  , ty := .e
  , denot := ToyEntity.mary
  }

def sleeps_entry : SemLexEntry toyModel :=
  { word := word_sleeps
  , ty := .e ⇒ .t
  , denot := ToyLexicon.sleeps_sem
  }

def laughs_entry : SemLexEntry toyModel :=
  { word := word_laughs
  , ty := .e ⇒ .t
  , denot := ToyLexicon.laughs_sem
  }

def student_entry : SemLexEntry toyModel :=
  { word := ⟨"student", Cat.N, { number := Option.some .sg }⟩
  , ty := .e ⇒ .t
  , denot := student_sem
  }

def students_entry : SemLexEntry toyModel :=
  { word := ⟨"students", Cat.N, { number := Option.some .pl }⟩
  , ty := .e ⇒ .t
  , denot := student_sem
  }

def SemLexicon (m : Model) := String → Option (SemLexEntry m)

def toyLexicon : SemLexicon toyModel := λ form =>
  match form with
  | "some" => some some_entry
  | "every" => some every_entry
  | "all" => some every_entry
  | "most" => some most_entry
  | "no" => some no_entry
  | "John" => some john_entry
  | "Mary" => some mary_entry
  | "sleeps" => some sleeps_entry
  | "laughs" => some laughs_entry
  | "student" => some student_entry
  | "students" => some students_entry
  | _ => none

def lookupAlternatives {m : Model} (lex : SemLexicon m) (form : String) : List (SemLexEntry m) :=
  match lex form with
  | none => []
  | some entry =>
    entry.strongerAlternatives.filterMap λ altForm => lex altForm

theorem some_is_scalar : some_entry.isScalar = true := rfl
theorem every_is_scalar : every_entry.isScalar = true := rfl
theorem john_not_scalar : john_entry.isScalar = false := rfl

end TruthConditional.Core
