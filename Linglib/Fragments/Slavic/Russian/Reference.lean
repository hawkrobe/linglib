import Linglib.Typology.Reference

/-!
# Russian article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian (Indo-European, Slavic): no definite or indefinite articles;
    two-way demonstrative distance: *этот* (proximal) vs *тот* (distal); same
    forms for pronominal and adnominal demonstratives; 3rd-person pronouns
    (*он*/*она*/*оно*) unrelated to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Russian"
  , family := "Indo-European"
  , iso := "rus"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

end Fragments.Slavic.Russian
