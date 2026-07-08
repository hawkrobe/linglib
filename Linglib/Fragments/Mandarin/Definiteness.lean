import Linglib.Syntax.Category.Determiner.Basic

/-!
# Mandarin Definiteness Fragment
[jenks-2018] [moroney-2021]

Mandarin has no overt indefinite or unique-definite article. Anaphoric
definiteness is carried by demonstratives (*nà* 'that', *zhè* 'this');
bare nouns serve unique definites. Possession is via *de*. Under the
[moroney-2021] typology this is the `.markedAnaphoric` strategy:
only the anaphoric type has a dedicated form.
-/

namespace Mandarin.Definiteness

/-- Mandarin: no overt articles; the demonstrative (*nà* 'that') obligatorily
    expones anaphoric definites; uniqueness is bare (no determiner);
    possessives via *de*. -/
def determiners : List Determiner.Entry :=
  [ .demonstrative { form := "na", deictic := .distal, definiteUses := [.anaphoric] },
    .possessive { form := "de" } ]

/-- Mandarin's inventory derives the `.markedAnaphoric` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .markedAnaphoric := by decide

end Mandarin.Definiteness
