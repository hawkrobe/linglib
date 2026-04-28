import Linglib.Typology.TenseAspect

/-!
# French tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.French

/-- French (Indo-European, Romance): *imparfait*/*passé composé* aspect
    distinction; inflectional past (*passé simple*); inflectional future
    (*-ai*, *-as*, *-a*…); 'have'-perfect (*avoir* + past participle);
    suffixing. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "French", iso := "fra", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .fromPossessive, affixPosition := .suffixing }

end Fragments.French
