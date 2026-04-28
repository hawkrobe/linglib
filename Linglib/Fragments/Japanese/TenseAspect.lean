import Linglib.Typology.TenseAspect

/-!
# Japanese tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Japanese

/-- Japanese (Japonic): perfective/imperfective (*ta*-form vs *te-iru*);
    inflectional past (*-ta*, *-da*); no inflectional future; no distinct
    perfect; suffixing. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Japanese", iso := "jpn", family := "Japonic"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

end Fragments.Japanese
