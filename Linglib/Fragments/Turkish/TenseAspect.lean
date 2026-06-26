import Linglib.Morphology.TenseAspect

/-!
# Turkish tense-aspect profile (WALS Chs 65–69, 78)
[wals-2013]
-/

namespace Turkish

/-- Turkish (Turkic): perfective/imperfective (*-di* vs *-iyor*); inflectional
    past; inflectional future (*-ecek*); other perfect (*-miş*, from
    evidential/inferential); suffixing. Evidentiality is part of the tense
    paradigm: *-miş* marks indirect (hearsay/inference) vs *-di* (direct). -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Turkish", iso := "tur", family := "Turkic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .other, affixPosition := .suffixing
  , evidentialityCoding := some .partOfTense }

end Turkish
