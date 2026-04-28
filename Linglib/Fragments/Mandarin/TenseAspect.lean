import Linglib.Typology.TenseAspect

/-!
# Mandarin tense-aspect profile (WALS Chs 65–69, 78)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese (Sino-Tibetan): perfective *le*/*guo*, but these are
    particles (not inflectional); no inflectional past or future; no distinct
    perfect; no tense-aspect inflection (quintessential isolating language);
    no grammatical evidentiality. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Mandarin Chinese", iso := "cmn", family := "Sino-Tibetan"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .none, affixPosition := .noInflection
  , evidentialityCoding := some .none }

end Fragments.Mandarin
