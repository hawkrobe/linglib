import Linglib.Typology.TenseAspect

/-!
# Russian tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian (Indo-European, Slavic): robust perfective/imperfective (typically
    via prefixation); inflectional past; no inflectional future (periphrastic
    *budet* + infinitive for imperfective; perfective present = future); no
    perfect; suffixing (*-l*, *-la* for past). -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Russian", iso := "rus", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

end Fragments.Slavic.Russian
