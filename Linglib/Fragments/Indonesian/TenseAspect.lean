import Linglib.Morphology.TenseAspect

/-!
# Indonesian tense-aspect profile (WALS Chs 65–69)
[wals-2013]
-/

namespace Indonesian

/-- Indonesian (Austronesian, Malayo-Polynesian): no grammatical aspect, no
    past marking, no inflectional future, no perfect (classic tenselessness:
    *air itu dingin* = 'the water is/was cold'). Minor repetitive suffix
    (*-i*) exists, marking it as `.suffixing` in WALS coding despite the
    overall pattern. -/
def tenseAspectProfile : Morphology.TenseAspect.TAProfile :=
  { language := "Indonesian", iso := "ind", family := "Austronesian"
  , aspect := .none, past := .none, future := .none
  , perfect := .none, affixPosition := .suffixing }

end Indonesian
