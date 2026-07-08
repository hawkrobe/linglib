import Linglib.Syntax.Category.Determiner.Basic

/-!
# Mauritian Creole Definiteness Fragment
[schwarz-2013]

Mauritian Creole (French-lexified creole, ISO `mfe`). A single post-nominal
**strong** definite clitic *la* (familiarity/anaphoric); uniqueness definites
are bare nominals (no weak article). Under [schwarz-2013] §4.1 this is a
strong-article-only language → the `.markedAnaphoric` Moroney cell.
-/

namespace MauritianCreole.Definiteness

/-- Mauritian Creole: post-nominal strong definite *la* (anaphoric/familiarity);
    weak uniqueness is bare (no weak article). -/
def determiners : List Determiner.Entry :=
  [ .article { form := "la", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] } ]

/-- Mauritian Creole derives the `.markedAnaphoric` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .markedAnaphoric := by decide

end MauritianCreole.Definiteness
