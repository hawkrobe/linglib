import Linglib.Typology.Reference

/-!
# German article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.German

/-- German (Indo-European, Germanic): definite *der*/*die*/*das* distinct from
    demonstratives; indefinite *ein* = numeral 'one' (phonologically reduced in
    speech); distance-neutral adnominal demonstratives (*dieser* and stressed
    *der*/*die*/*das* are deictically noncontrastive — distance expressed by
    adverbial *hier*/*da*); pronominal demonstratives inflect for case while
    adnominal co-occur with inflected nouns (different inflectional features);
    3rd-person pronouns (*er*/*sie*/*es*) unrelated to demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "German"
  , family := "Indo-European"
  , iso := "deu"
  , defArticle := some .definiteWord
  , indefArticle := some .numeralOne
  , demDistance := some .noContrast
  , demOrientation := some .notApplicable
  , demFormType := some .differentInflection
  , pronDemRelation := some .unrelated }

end Fragments.German
