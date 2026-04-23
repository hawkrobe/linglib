import Linglib.Core.Nominal.ArticleInventory

/-!
# English Definiteness Fragment
@cite{schwarz-2009} @cite{schwarz-2013} @cite{moroney-2021}

English uses a single syncretic definite article *the* for both uniqueness
and anaphoric definiteness, an indefinite *a/an*, demonstratives *this/that*,
and possessives *my/your/...*. Under the @cite{moroney-2021} typology this
is the `.generallyMarked` strategy: a single form covers all
@cite{schwarz-2009} use types.
-/

namespace Fragments.English.Definiteness

open Core.Nominal (ArticleInventory)
open Features.Definiteness (DefMarkingStrategy)

/-- English: indefinite *a/an*; the syncretic definite *the* (one form for
    both unique and anaphoric); demonstratives *this/that*; possessives
    *my/your/...*. -/
def articleInventory : ArticleInventory :=
  { hasIndefinite             := True
    hasUniqueArticle          := True
    hasAnaphoricArticle       := True
    uniqueAnaphoricSyncretism := True
    hasDemonstrative          := True
    hasPossessive             := True }

/-- English's inventory derives the `.generallyMarked` Moroney cell. -/
theorem articleInventory_marking :
    articleInventory.toMarkingStrategy = .generallyMarked := rfl

end Fragments.English.Definiteness
