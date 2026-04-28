import Linglib.Core.Morphology.MorphRule

/-!
# Doyayo Auxiliary Verb Fragment
@cite{anderson-2006}

Doyayo (Adamawa, Niger-Congo; Cameroon) has auxiliary verb constructions
with a **split** inflectional pattern: tense is marked on lexical verbs,
while the auxiliary hosts subject marking, benefactive, and object
arguments.

Source: Wiering and Wiering 1994: 75, cited in @cite{anderson-2006}.
-/

namespace Fragments.Doyayo.AuxiliaryVerbs

open Core.Morphology (InflDistribution MorphCategory)

/-- Primary AVC example form.
    *hi¹ gi²-s-i¹-mi²-ge-³ wàà⁵-ko⁵*
    'they AUX-BEN-EP-1-3 catch-PROX'
    'they will be catching him for me'
    (Wiering and Wiering 1994: 75, cited in @cite{anderson-2006}). -/
def form : String := "hi¹ gi²-s-i¹-mi²-ge-³ wàà⁵-ko⁵"

def gloss : String :=
  "they AUX-BEN-EP-1-3 catch-PROX 'they will be catching him for me'"

/-- Secondary example: *mi³ gi²-s-i-g kaa¹-ko¹*
    'I AUX-BEN-EP-3 weep-PRES' = 'I'm crying to him'
    (Wiering and Wiering 1994: 75, cited in @cite{anderson-2006}). -/
def secondaryForm : String := "mi³ gi²-s-i-g kaa¹-ko¹"

def family : String := "Adamawa, Niger-Congo"
def location : String := "Cameroon"

/-- Split inflection distribution: AUX hosts subject/object agreement and
    benefactive applicative; LV hosts tense.
    (Subject and object cross-referencing are both `.agreement`;
    benefactive is `.valence`.) -/
def inflDistribution : InflDistribution :=
  { onAux := [.agreement, .valence]
  , onLex := [.tense] }

end Fragments.Doyayo.AuxiliaryVerbs
