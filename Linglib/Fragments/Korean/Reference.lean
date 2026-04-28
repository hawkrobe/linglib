import Linglib.Typology.Reference

/-!
# Korean article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Korean

/-- Korean (Koreanic): no definite or indefinite articles (topic marker
    *-un*/*-nun* sometimes conveys definiteness pragmatically); three-way
    person-oriented demonstrative system: *i* (near speaker), *ku* (near
    hearer), *ce* (away from both); different stems — pronominal demonstratives
    formed by combining *i*/*ku*/*ce* with a "defective noun" like *il*
    (thing/fact); 3rd-person pronoun *ku* related to medial demonstrative
    *ku*. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Korean"
  , family := "Koreanic"
  , iso := "kor"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .threeWay
  , demOrientation := some .personOriented
  , demFormType := some .differentStems
  , pronDemRelation := some .relatedNonRemote }

end Fragments.Korean
