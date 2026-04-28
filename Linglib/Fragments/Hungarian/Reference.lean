import Linglib.Typology.Reference

/-!
# Hungarian article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Hungarian

/-- Hungarian (Uralic): definite article *a*/*az* distinct from demonstratives;
    indefinite article *egy* = numeral 'one'; two-way demonstrative distance:
    *ez* (proximal) vs *az* (distal); same forms for pronominal and adnominal
    demonstratives; 3rd-person pronoun *ő* unrelated to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Hungarian"
  , family := "Uralic"
  , iso := "hun"
  , defArticle := some .definiteWord
  , indefArticle := some .numeralOne
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

end Fragments.Hungarian
