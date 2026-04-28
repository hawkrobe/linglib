import Linglib.Typology.TenseAspect

/-!
# Arabic (Egyptian) tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Arabic

/-- Arabic (Egyptian) (Afro-Asiatic, Semitic): perfective/imperfective
    (*katab*/*yiktib*); inflectional past (perfective form encodes past);
    no inflectional future (uses preverbal particles); no distinct perfect;
    suffixing. -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Arabic (Egyptian)", iso := "arz", family := "Afro-Asiatic"
  , aspect := .grammatical, past := .marked, future := .none
  , perfect := .none, affixPosition := .suffixing }

end Fragments.Arabic
