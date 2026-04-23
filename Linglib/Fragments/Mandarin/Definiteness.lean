import Linglib.Core.Nominal.ArticleInventory

/-!
# Mandarin Definiteness Fragment
@cite{jenks-2018} @cite{moroney-2021}

Mandarin has no overt indefinite or unique-definite article. Anaphoric
definiteness is carried by demonstratives (*nà* 'that', *zhè* 'this');
bare nouns serve unique definites. Possession is via *de*. Under the
@cite{moroney-2021} typology this is the `.markedAnaphoric` strategy:
only the anaphoric type has a dedicated form.
-/

namespace Fragments.Mandarin.Definiteness

open Core.Nominal (ArticleInventory)
open Features.Definiteness (DefMarkingStrategy)

/-- Mandarin: no overt indefinite/unique articles; demonstratives carry the
    anaphoric load (*nà* 'that'); possessives via *de*. -/
def articleInventory : ArticleInventory :=
  { hasIndefinite             := False
    hasUniqueArticle          := False
    hasAnaphoricArticle       := True
    hasDemonstrative          := True
    hasPossessive             := True }

/-- Mandarin's inventory derives the `.markedAnaphoric` Moroney cell. -/
theorem articleInventory_marking :
    articleInventory.toMarkingStrategy = .markedAnaphoric := rfl

end Fragments.Mandarin.Definiteness
