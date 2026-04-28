import Linglib.Typology.TenseAspect

/-!
# Tagalog tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog (Austronesian, Malayo-Polynesian): perfective/imperfective
    (completed vs contemplated aspect); no inflectional past or future
    (aspect-based system); no distinct perfect; prefixing
    (*mag-*, *nag-*, *-um-* etc.). -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Tagalog", iso := "tgl", family := "Austronesian"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .none, affixPosition := .prefixing }

end Fragments.Tagalog
