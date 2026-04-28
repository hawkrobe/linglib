import Linglib.Typology.TenseAspect

/-!
# Quechua tense-aspect profile (WALS Chs 65–69, 78)
@cite{wals-2013}
-/

namespace Fragments.Quechua

/-- Quechua (Quechuan): no grammatical perfective/imperfective; inflectional
    past with 2–3 remoteness distinctions (direct vs indirect past);
    inflectional future (*-saq*); other perfect (*-sqa* resultative);
    suffixing. Evidentiality via verbal suffixes (*-mi* direct, *-si*
    hearsay, *-chá* conjecture). -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Quechua", iso := "que", family := "Quechuan"
  , aspect := .none, past := .markedRemoteness2_3, future := .inflectional
  , perfect := .other, affixPosition := .suffixing
  , evidentialityCoding := some .verbalAffix }

end Fragments.Quechua
