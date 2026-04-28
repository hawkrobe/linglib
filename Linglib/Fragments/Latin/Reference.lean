import Linglib.Typology.Reference

/-!
# Latin article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Latin

/-- Latin (Indo-European, Italic): no definite or indefinite articles (bare
    nouns are ambiguous); textbook three-way distance-oriented demonstrative
    system: *hic* (proximal), *iste* (medial), *ille* (distal); same forms
    for pronominal and adnominal demonstratives (with full case/gender/number
    inflection in both uses); 3rd-person pronoun *is*/*ea*/*id* historically
    related to all demonstratives via shared inflection patterns. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Latin"
  , family := "Indo-European"
  , iso := "lat"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .threeWay
  , demOrientation := some .distanceOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedAll }

end Fragments.Latin
