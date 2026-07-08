import Linglib.Syntax.Category.Determiner.Basic

/-!
# Akan Definiteness Fragment
[schwarz-2013]

Akan (Kwa, ISO `ak`). A single overt **strong** definite article *nó*
(familiarity/anaphoric); uniqueness definites are expressed by bare nominals
(no weak article). Indefinites use *bí*. Under [schwarz-2013] §4.1 this is
a strong-article-only language → the `.markedAnaphoric` Moroney cell.
-/

namespace Akan.Definiteness

/-- Akan: strong definite article *nó* (anaphoric/familiarity); weak uniqueness
    is bare (no weak article); indefinite *bí*. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "nó", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] },
    .article { form := "bí", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]

/-- Akan derives the `.markedAnaphoric` Moroney cell (only the anaphoric
    definite is marked; uniqueness is bare). -/
theorem marking : Determiner.markingStrategy determiners = .markedAnaphoric := by decide

end Akan.Definiteness
