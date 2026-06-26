import Linglib.Morphology.TenseAspect

/-!
# Vietnamese tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace Vietnamese

/-- Vietnamese (Austroasiatic): no grammatical perfective/imperfective; no
    inflectional past or future; no perfect. Tense-aspect via separate
    particles (*đã*, *sẽ*); part of the SE Asian isolating area. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Vietnamese", iso := "vie", family := "Austroasiatic"
  , aspect := .none, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection }

end Vietnamese
