import Linglib.Typology.Reference

/-!
# French article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.French

/-- French (Indo-European, Romance): definite article *le*/*la*/*les* distinct
    from demonstratives; indefinite *un*/*une* (historically from numeral 'one'
    but coded by WALS as distinct word); two-way demonstrative distance
    (*ce N-ci* / *ce N-là*); different stems for pronominal *celui*/*celle* vs
    adnominal *ce*/*cette*; 3rd-person pronouns (*il*/*elle*) unrelated to
    demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "French"
  , family := "Indo-European"
  , iso := "fra"
  , defArticle := some .definiteWord
  , indefArticle := some .indefiniteWord
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .differentStems
  , pronDemRelation := some .unrelated }

end Fragments.French
