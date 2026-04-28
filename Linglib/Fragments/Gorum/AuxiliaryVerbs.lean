import Linglib.Core.Morphology.MorphRule

/-!
# Gorum Auxiliary Verb Fragment
@cite{anderson-2006}

Gorum (a.k.a. Parenga or Parengi; South Munda, Austroasiatic; India) has
auxiliary verb constructions with a **doubled** inflectional pattern: both
the auxiliary verb and the lexical verb are marked for subject (person/number)
and TAM (tense, affectedness/version).

Source: Aze 1973, cited in @cite{anderson-2006}.
-/

namespace Fragments.Gorum.AuxiliaryVerbs

open Core.Morphology (InflDistribution MorphCategory)

/-- Primary AVC example form.
    *miŋ ne-gaʔ-ru ne-laʔ-ru*
    'I 1-eat-PST 1-AUX-PST'
    'I ate vigorously'
    (Aze 1973: 279, cited in @cite{anderson-2006}). -/
def form : String := "miŋ ne-gaʔ-ru ne-laʔ-ru"

def gloss : String := "I 1-eat-PST 1-AUX-PST 'I ate vigorously'"

/-- Secondary example with non-past and affectedness:
    *kula ne-giʔ-sun miŋ ne-butoŋ-tuʔ ne-i-tuʔ*
    'tiger 1-see-when I 1-fear-NPST:AFF 1-AUX-NPST:AFF'
    'when I see the tiger, I'll be afraid'
    (Aze 1973, cited in @cite{anderson-2006}). -/
def secondaryForm : String := "kula ne-giʔ-sun miŋ ne-butoŋ-tuʔ ne-i-tuʔ"

def family : String := "South Munda, Austroasiatic"
def location : String := "India"

/-- Doubled inflection distribution: both AUX and LV are marked for
    subject agreement, tense, and affectedness (version/voice). -/
def inflDistribution : InflDistribution :=
  { onAux := [.agreement, .tense, .voice]
  , onLex := [.agreement, .tense, .voice] }

end Fragments.Gorum.AuxiliaryVerbs
