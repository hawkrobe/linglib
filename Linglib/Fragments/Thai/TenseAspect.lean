import Linglib.Typology.TenseAspect

/-!
# Thai tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Thai

/-- Thai (Tai-Kadai): no grammatical perfective/imperfective; no inflectional
    past or future; no perfect. SE Asian isolating type. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Thai", iso := "tha", family := "Tai-Kadai"
  , aspect := .none, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection }

end Fragments.Thai
