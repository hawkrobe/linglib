import Linglib.Typology.Reference

/-!
# Arabic (Egyptian) article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Arabic

/-- Arabic (Egyptian) (Afro-Asiatic, Semitic): definite prefix *al-* on nouns
    (definite affix); no indefinite article (unmarked nouns are indefinite,
    though Standard Arabic *tanwin* marks indefiniteness); two-way demonstrative
    distance: *hada* (proximal) vs *daak* (distal); same forms for pronominal
    and adnominal demonstratives; 3rd-person pronouns (*huwa*/*hiya*) unrelated
    to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Arabic (Egyptian)"
  , family := "Afro-Asiatic"
  , iso := "arz"
  , defArticle := some .definiteAffix
  , indefArticle := some .noIndefButDef
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

end Fragments.Arabic
