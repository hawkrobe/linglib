import Linglib.Typology.Reference

/-!
# Basque article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Basque

/-- Basque (language isolate): definite suffix *-a*/*-ak* (definite affix);
    no indefinite article (bare nouns are indefinite); three-way distance-
    oriented demonstrative system: *hau* (proximal), *hori* (medial), *hura*
    (distal); same forms for pronominal and adnominal demonstratives; the
    demonstratives *hau*/*hori*/*hura* themselves function as 3rd-person
    pronouns (@cite{saltarelli-etal-1988}). -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Basque"
  , family := "Isolate"
  , iso := "eus"
  , defArticle := some .definiteAffix
  , indefArticle := some .noIndefButDef
  , demDistance := some .threeWay
  , demOrientation := some .distanceOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedAll }

end Fragments.Basque
