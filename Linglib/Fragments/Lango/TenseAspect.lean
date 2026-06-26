import Linglib.Morphology.TenseAspect

/-!
# Lango tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace Lango

/-- Lango (Nilotic, Eastern Sudanic): perfective/imperfective/progressive
    marked primarily by tone; past tense marking; no inflectional future;
    other perfect; tonal T/A marking. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Lango", iso := "laj", family := "Nilo-Saharan"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .other, affixPosition := .tonal }

end Lango
