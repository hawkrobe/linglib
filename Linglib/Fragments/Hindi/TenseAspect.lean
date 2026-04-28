import Linglib.Typology.TenseAspect

/-!
# Hindi tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Hindi

/-- Hindi (Indo-European, Indo-Aryan): perfective/imperfective (*-aa*,
    *-taa*); inflectional past; inflectional future (*-egaa*); other perfect;
    suffixing. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Hindi", iso := "hin", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .other, affixPosition := .suffixing }

end Fragments.Hindi
