import Linglib.Typology.Reference

/-!
# English article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English (Indo-European, Germanic): definite article *the* distinct from
    demonstratives *this*/*that*; indefinite article *a*/*an* distinct from
    numeral *one*; two-way demonstrative distance (proximal/distal); same
    forms for pronominal and adnominal demonstratives; 3rd-person pronouns
    (*he*/*she*/*it*) unrelated to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "English"
  , family := "Indo-European"
  , iso := "eng"
  , defArticle := some .definiteWord
  , indefArticle := some .indefiniteWord
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

end Fragments.English
