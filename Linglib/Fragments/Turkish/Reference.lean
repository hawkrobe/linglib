import Linglib.Typology.Reference

/-!
# Turkish article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Turkish

/-- Turkish (Turkic): no definite article; indefinite *bir* = numeral 'one'
    (different NP position when used as article vs numeral, per
    @cite{kornfilt-1997}); two-way demonstrative distance: *bu* (proximal) vs
    *o* (distal), with restricted medial *şu*; pronominal demonstratives inflect
    for case and number, adnominal are uninflected particles; 3rd-person
    pronoun *o* identical to distal demonstrative. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Turkish"
  , family := "Turkic"
  , iso := "tur"
  , defArticle := some .noDefButIndef
  , indefArticle := some .numeralOne
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .differentInflection
  , pronDemRelation := some .relatedRemote }

end Fragments.Turkish
