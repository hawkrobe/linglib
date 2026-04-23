import Linglib.Core.Nominal.ArticleInventory

/-!
# German Definiteness Fragment
@cite{schwarz-2009} @cite{schwarz-2013} @cite{moroney-2021}

German morphologically distinguishes the weak (uniqueness) article — often
contracted, e.g., *im*, *vom*, *zum* — from the strong (anaphoric/familiarity)
article — full forms *dem*, *von dem*. Indefinite *ein-*, demonstratives,
and possessives complete the inventory. Under the @cite{moroney-2021}
typology this is the `.bipartite` strategy: distinct forms for each
@cite{schwarz-2009} use type.
-/

namespace Fragments.German.Definiteness

open Core.Nominal (ArticleInventory)
open Features.Definiteness (DefMarkingStrategy)

/-- German: indefinite *ein-*; *distinct* weak (contracted, e.g., *im*) and
    strong (*dem*) definite articles; demonstratives; possessives. The
    unique vs anaphoric distinction is morphologically marked. -/
def articleInventory : ArticleInventory :=
  { hasIndefinite             := True
    hasUniqueArticle          := True
    hasAnaphoricArticle       := True
    uniqueAnaphoricSyncretism := False
    hasDemonstrative          := True
    hasPossessive             := True }

/-- German's inventory derives the `.bipartite` Moroney cell. -/
theorem articleInventory_marking :
    articleInventory.toMarkingStrategy = .bipartite := rfl

end Fragments.German.Definiteness
