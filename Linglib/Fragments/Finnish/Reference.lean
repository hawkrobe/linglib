import Linglib.Typology.Reference

/-!
# Finnish article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Finnish

/-- Finnish (Uralic): no definite or indefinite articles; two-way demonstrative
    distance: *tämä* (proximal) vs *tuo*/*se* (distal); same forms for
    pronominal and adnominal demonstratives; 3rd-person pronoun *hän* (human) /
    *se* (nonhuman) — *se* is identical to the distal demonstrative
    (related-for-nonhuman pattern). -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Finnish"
  , family := "Uralic"
  , iso := "fin"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedNonhuman }

end Fragments.Finnish
