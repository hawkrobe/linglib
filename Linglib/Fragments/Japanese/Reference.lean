import Linglib.Typology.Reference

/-!
# Japanese article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Japanese

/-- Japanese (Japonic): no definite or indefinite articles; three-way
    person-oriented demonstrative system (*ko-* near speaker, *so-* near hearer,
    *a-* away from both — the canonical person-oriented system); different
    stems for adnominal *kono*/*sono*/*ano* vs pronominal *kore*/*sore*/*are*;
    3rd-person pronouns (*kare*/*kanojo*) unrelated to demonstratives
    (relatively recent borrowings from Classical Chinese). -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Japanese"
  , family := "Japonic"
  , iso := "jpn"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .threeWay
  , demOrientation := some .personOriented
  , demFormType := some .differentStems
  , pronDemRelation := some .unrelated }

end Fragments.Japanese
