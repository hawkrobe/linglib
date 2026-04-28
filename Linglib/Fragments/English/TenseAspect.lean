import Linglib.Typology.TenseAspect

/-!
# English tense-aspect profile (WALS Chs 65–69, 78)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English (Indo-European, Germanic): periphrastic perfective (simple past
    vs progressive); inflectional past (*-ed*); no inflectional future
    (uses *will*); 'have'-perfect; suffixing (*-ed*, *-ing*); no grammatical
    evidentiality. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "English", iso := "eng", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .fromPossessive, affixPosition := .suffixing
  , evidentialityCoding := some .none }

end Fragments.English
