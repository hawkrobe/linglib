import Linglib.Typology.Reference

/-!
# Tagalog article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog (Austronesian, Philippine): definite/indefinite distinction via
    case markers — *ang* (definite-like topic marker) vs *ng* (indefinite-like);
    WALS codes as definite word distinct from demonstratives; three-way
    demonstrative distance (*ito*/*iyan*/*iyon*) coded as person-oriented in
    WALS; same forms for pronominal and adnominal demonstratives; 3rd-person
    pronoun *siya* unrelated to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Tagalog"
  , family := "Austronesian"
  , iso := "tgl"
  , defArticle := some .definiteWord
  , indefArticle := some .noIndefButDef
  , demDistance := some .threeWay
  , demOrientation := some .personOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

end Fragments.Tagalog
