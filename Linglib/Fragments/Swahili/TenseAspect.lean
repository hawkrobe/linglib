import Linglib.Typology.TenseAspect

/-!
# Swahili tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Swahili

/-- Swahili (Niger-Congo, Bantu): perfective/imperfective (*-li-*, *-na-*);
    past marking; no inflectional future; other perfect (*-me-*); prefixing
    (T/A markers are verbal prefixes). -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Swahili", iso := "swh", family := "Niger-Congo"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .other, affixPosition := .prefixing }

end Fragments.Swahili
