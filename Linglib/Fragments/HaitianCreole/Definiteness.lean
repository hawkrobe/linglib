import Linglib.Syntax.Category.Determiner.Basic

/-!
# Haitian Creole Definiteness Fragment
[schwarz-2013]

Haitian Creole (French-lexified creole, ISO `ht`). A single post-nominal
definite determiner *la* serves **both** anaphoric and uniqueness uses — no
weak/strong split. This is [schwarz-2013]'s §4.3 exception to the
crosslinguistic two-article pattern: one syncretic article → the
`.generallyMarked` Moroney cell.
-/

namespace HaitianCreole.Definiteness

/-- Haitian Creole: a single definite *la* covering both uniqueness and
    anaphoric uses (no weak/strong split). -/
def determiners : List Determiner.Entry :=
  [ .article { form := "la", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] } ]

/-- Haitian Creole derives the `.generallyMarked` Moroney cell (one syncretic
    form). -/
theorem marking : Determiner.markingStrategy determiners = .generallyMarked := by decide

end HaitianCreole.Definiteness
