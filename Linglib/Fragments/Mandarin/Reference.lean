import Linglib.Typology.Reference

/-!
# Mandarin article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese (Sino-Tibetan): no definite or indefinite articles
    (bare nouns are ambiguous for definiteness); two-way demonstrative
    distance: *zhe* (proximal) vs *na* (distal); same forms for pronominal
    and adnominal demonstratives (with optional classifier in adnominal use);
    3rd-person pronoun *ta* unrelated to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , iso := "cmn"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

end Fragments.Mandarin
