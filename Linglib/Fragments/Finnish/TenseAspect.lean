import Linglib.Morphology.TenseAspect

/-!
# Finnish tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace Finnish

/-- Finnish (Uralic): no grammatical perfective/imperfective; inflectional
    past (*-i*); no inflectional future (present used for future reference);
    perfect (*on* + past participle, 'be'-type); suffixing. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Finnish", iso := "fin", family := "Uralic"
  , aspect := .none, past := .marked, future := .none
  , perfect := .other, affixPosition := .suffixing }

end Finnish
