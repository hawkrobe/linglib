import Linglib.Typology.TenseAspect

/-!
# Lango tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Lango

/-- Lango (Nilotic, Eastern Sudanic): perfective/imperfective/progressive
    marked primarily by tone; past tense marking; no inflectional future;
    other perfect; tonal T/A marking. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Lango", iso := "laj", family := "Nilo-Saharan"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .other, affixPosition := .tonal }

end Fragments.Lango
