import Linglib.Morphology.TenseAspect

/-!
# French tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace French

/-- French (Indo-European, Romance): *imparfait*/*passé composé* aspect
    distinction; inflectional past (*passé simple*); inflectional future
    (*-ai*, *-as*, *-a*…); 'have'-perfect (*avoir* + past participle);
    suffixing. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "French", iso := "fra", family := "Indo-European"
  , aspect := .grammatical, past := .marked, future := .inflectional
  , perfect := .fromPossessive, affixPosition := .suffixing }

end French
