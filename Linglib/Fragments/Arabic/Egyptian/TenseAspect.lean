import Linglib.Morphology.TenseAspect

/-!
# Arabic (Egyptian) tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace Arabic.Egyptian

/-- Arabic (Egyptian) (Afro-Asiatic, Semitic): perfective/imperfective
    (*katab*/*yiktib*); inflectional past (perfective form encodes past);
    no inflectional future (uses preverbal particles); no distinct perfect;
    suffixing. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Arabic (Egyptian)", iso := "arz", family := "Afro-Asiatic"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

end Arabic.Egyptian
