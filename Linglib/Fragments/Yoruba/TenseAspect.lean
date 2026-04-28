import Linglib.Typology.TenseAspect

/-!
# Yoruba tense-aspect profile (WALS Chs 65–69)
@cite{wals-2013}
-/

namespace Fragments.Yoruba

/-- Yoruba (Niger-Congo, Atlantic-Congo): perfective/imperfective distinction;
    no past tense marking; no inflectional future; perfect from 'already'
    (*ti*); no tense-aspect inflection (preverbal particles). -/
def tenseAspectProfile : Typology.TAProfile :=
  { language := "Yoruba", iso := "yor", family := "Niger-Congo"
  , aspect := .grammatical, past := .none, future := .none
  , perfect := .fromFinishAlready, affixPosition := .noInflection }

end Fragments.Yoruba
