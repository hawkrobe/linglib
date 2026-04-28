import Linglib.Typology.Reference

/-!
# Hausa article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Hausa

/-- Hausa (Afro-Asiatic, Chadic): no definite or indefinite article;
    four-way person-oriented demonstrative system (one of WALS's key examples
    of a 4+ way system): near speaker, near hearer, away from both, far away
    (some terms tonally differentiated); same forms for pronominal and
    adnominal demonstratives; 3rd-person pronouns related to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Hausa"
  , family := "Afro-Asiatic"
  , iso := "hau"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .fourWay
  , demOrientation := some .personOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedAll }

end Fragments.Hausa
