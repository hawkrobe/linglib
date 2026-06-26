import Linglib.Morphology.TenseAspect

/-!
# Spanish tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace Spanish

/-- Spanish (Indo-European, Romance): *imperfecto*/*pretérito*; inflectional
    past and future; 'have'-perfect (*haber* + participle); suffixing. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Spanish", iso := "spa", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .fromPossessive, affixPosition := .suffixing }

end Spanish
