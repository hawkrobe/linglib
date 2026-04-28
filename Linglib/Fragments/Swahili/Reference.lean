import Linglib.Typology.Reference

/-!
# Swahili article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Swahili

/-- Swahili (Niger-Congo, Bantu): demonstrative used as definite marker
    (precedes noun for definiteness, follows for deictic use; WALS Ch 37
    value 2); no indefinite article; three-way distance-oriented demonstrative
    system: *h-* (proximal) / *h-o* (medial) / *-le* (distal); same forms for
    pronominal and adnominal demonstratives; 3rd-person pronouns related via
    shared noun-class agreement prefixes. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Swahili"
  , family := "Niger-Congo"
  , iso := "swh"
  , defArticle := some .demonstrativeUsed
  , indefArticle := some .noIndefButDef
  , demDistance := some .threeWay
  , demOrientation := some .distanceOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedGender }

end Fragments.Swahili
