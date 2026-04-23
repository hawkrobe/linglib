import Linglib.Core.Nominal.ArticleInventory

/-!
# Thai Definiteness Fragment
@cite{jenks-2015} @cite{moroney-2021}

Thai patterns with Mandarin on the @cite{moroney-2021} typology: bare nouns
serve uniqueness contexts and demonstratives carry the anaphoric load —
no overt indefinite or unique article. Possessives are productive. Under
the @cite{moroney-2021} typology this is the `.markedAnaphoric` strategy.
-/

namespace Fragments.Thai.Definiteness

open Core.Nominal (ArticleInventory)
open Features.Definiteness (DefMarkingStrategy)

/-- Thai @cite{jenks-2015}: same definite-marking pattern as Mandarin —
    bare nouns for uniqueness contexts, demonstratives for anaphoric
    contexts. -/
def articleInventory : ArticleInventory :=
  { hasIndefinite             := False
    hasUniqueArticle          := False
    hasAnaphoricArticle       := True
    hasDemonstrative          := True
    hasPossessive             := True }

/-- Thai's inventory derives the `.markedAnaphoric` Moroney cell — same
    cell as Mandarin (same definite-marking pattern). -/
theorem articleInventory_marking :
    articleInventory.toMarkingStrategy = .markedAnaphoric := rfl

end Fragments.Thai.Definiteness
