/-
# Montague Semantics: Lexicon

Lexical entries with semantic denotations and scalar alternatives.

## Main definitions

`ScaleMembership`, `SemLexEntry`, `SemLexicon`, `toyLexicon`

## References

Montague (1973)
-/

import Linglib.Core.Basic
import Linglib.Theories.Semantics.Compositional.Basic
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Core.HornScale
import Linglib.Core.Morphology.Number

namespace TruthConditional.Core

open TruthConditional
open TruthConditional.Determiner.Quantifier
open Core.Scale

private def word_some : Word := ⟨"some", .DET, {}⟩
private def word_every : Word := ⟨"every", .DET, { number := some .sg }⟩
private def word_john : Word := ⟨"John", .DET, { number := some .sg, person := some .third }⟩
private def word_mary : Word := ⟨"Mary", .DET, { number := some .sg, person := some .third }⟩
private def word_sleeps : Word := ⟨"sleeps", .VERB, { valence := some .intransitive, number := some .sg, person := some .third }⟩
private def word_laughs : Word := ⟨"laughs", .VERB, { valence := some .intransitive, number := some .sg, person := some .third }⟩

/-- Scale membership position for closed-class expressions.

Numerals are excluded: under lower-bound semantics they form an infinite
scale (not representable as a finite `HornScale`), and under bilateral
semantics they don't form a scale at all (Kennedy 2015). See
`Theories/TruthConditional/Determiner/Numeral/Semantics.lean`. -/
inductive ScaleMembership where
  | quantifier (pos : Quantifiers.QuantExpr)
  | connective (pos : Connectives.ConnExpr)
  | modal (pos : Modals.ModalExpr)
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
    (Core.Scale.strongerAlternatives Quantifiers.quantScale pos).map λ
      | .none_ => "no"
      | .some_ => "some"
      | .most => "most"
      | .all => "all"
  | some (.connective pos) =>
    (Core.Scale.strongerAlternatives Connectives.connScale pos).map λ
      | .or_ => "or"
      | .and_ => "and"
  | some (.modal pos) =>
    (Core.Scale.strongerAlternatives Modals.modalScale pos).map λ
      | .possible => "might"
      | .necessary => "must"

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
  { word := ⟨"most", .DET, { number := Option.some .pl }⟩
  , ty := Ty.det
  , denot := most_sem toyModel
  , scaleMembership := some (.quantifier .most)
  }

def no_entry : SemLexEntry toyModel :=
  { word := ⟨"no", .DET, {}⟩
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

/-- Student noun stem: paradigm generates both sg and pl entries.

    In the toy model (no mereological structure), the plural rule is
    semantically flat (`semEffect := id`). In a model with Link-style
    plurals, use `Number.pluralNounRule` with closure/atom predicates. -/
def studentStem : Core.Morphology.Stem (toyModel.interpTy (.e ⇒ .t)) :=
  { lemma_ := "student"
  , cat := .NOUN
  , baseFeatures := { number := some .Sing }
  , paradigm := [Core.Morphology.Number.pluralNounRuleFlat] }

private def studentPluralRule := Core.Morphology.Number.pluralNounRuleFlat (α := ToyEntity)

/-- Singular "student" entry derived from stem. -/
def student_entry : SemLexEntry toyModel :=
  { word := { form := studentStem.lemma_
            , cat := studentStem.cat
            , features := studentStem.baseFeatures }
  , ty := .e ⇒ .t
  , denot := student_sem }

/-- Plural "students" entry derived from stem via plural rule. -/
def students_entry : SemLexEntry toyModel :=
  { word := { form := studentPluralRule.formRule studentStem.lemma_
            , cat := studentStem.cat
            , features := studentPluralRule.featureRule studentStem.baseFeatures }
  , ty := .e ⇒ .t
  , denot := studentPluralRule.semEffect student_sem }

/-- The stem-derived singular entry preserves the expected form and features. -/
theorem student_entry_form : student_entry.word.form = "student" := rfl
theorem student_entry_number : student_entry.word.features.number = some .Sing := rfl

/-- The stem-derived plural entry produces the expected form and features. -/
theorem students_entry_form : students_entry.word.form = "students" := rfl
theorem students_entry_number : students_entry.word.features.number = some .Plur := rfl

/-- In the toy model (flat plural semantics), both entries share the
    same denotation since `pluralNounRuleFlat.semEffect = id`. -/
theorem student_plural_flat_sem :
    students_entry.denot = student_entry.denot := rfl

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
