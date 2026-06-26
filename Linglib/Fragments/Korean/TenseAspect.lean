import Linglib.Morphology.TenseAspect

/-!
# Korean tense-aspect profile (WALS Chs 65–69, 78)
[wals-2013] [cumming-2026]
-/

namespace Korean

/-- Korean (Koreanic): perfective/imperfective (*-었-* vs *-고 있-*);
    inflectional past (*-었-*); inflectional future (*-겠-*); no distinct
    perfect; suffixing. Evidentiality via verbal suffixes (*-te*
    retrospective, *-ney* contemporaneous; [cumming-2026] analyzes
    these as tense-evidential interactions). -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Korean", iso := "kor", family := "Koreanic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .none, affixPosition := .suffixing
  , evidentialityCoding := some .verbalAffix }

end Korean
