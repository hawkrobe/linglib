import Linglib.Typology.TenseAspect

/-!
# Korean tense-aspect profile (WALS Chs 65–69, 78)
@cite{wals-2013} @cite{cumming-2026}
-/

namespace Fragments.Korean

/-- Korean (Koreanic): perfective/imperfective (*-었-* vs *-고 있-*);
    inflectional past (*-었-*); inflectional future (*-겠-*); no distinct
    perfect; suffixing. Evidentiality via verbal suffixes (*-te*
    retrospective, *-ney* contemporaneous; @cite{cumming-2026} analyzes
    these as tense-evidential interactions). -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Korean", iso := "kor", family := "Koreanic"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .none, affixPosition := .suffixing
  , evidentialityCoding := some .verbalAffix }

end Fragments.Korean
