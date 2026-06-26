import Linglib.Morphology.TenseAspect

/-!
# Quechua tense-aspect profile (WALS Chs 65–69, 78)
[wals-2013]
-/

namespace Quechua

/-- Quechua (Quechuan): no grammatical perfective/imperfective; inflectional
    past with 2–3 remoteness distinctions (direct vs indirect past);
    inflectional future (*-saq*); other perfect (*-sqa* resultative);
    suffixing. Evidentiality via verbal suffixes (*-mi* direct, *-si*
    hearsay, *-chá* conjecture). -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Quechua", iso := "que", family := "Quechuan"
  , aspect := .none, past := .markedRemoteness2_3, future := .inflectional
  , perfect := .other, affixPosition := .suffixing
  , evidentialityCoding := some .verbalAffix }

end Quechua
