import Linglib.Typology.Reference

/-!
# Danish article-and-demonstrative profile (WALS Chs 37, 38, 41, 42, 43)
@cite{wals-2013}
-/

namespace Fragments.Danish

/-- Danish (Indo-European, Germanic): definite suffix *-en*/*-et* on nouns
    (definite affix); separate definite article *den*/*det* used when an
    adjective is present; indefinite article *en*/*et* = numeral 'one';
    two-way demonstrative distance: *denne* (proximal) vs *den* (distal);
    different inflectional features between pronominal and adnominal uses;
    3rd-person pronouns *han*/*hun*/*den*/*det* — *den*/*det* related to
    demonstratives. -/
def referenceProfile : Typology.ArticleDemProfile :=
  { language := "Danish"
  , family := "Indo-European"
  , iso := "dan"
  , defArticle := some .definiteAffix
  , indefArticle := some .numeralOne
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .differentInflection
  , pronDemRelation := some .relatedRemote }

end Fragments.Danish
