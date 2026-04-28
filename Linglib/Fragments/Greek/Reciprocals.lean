import Linglib.Core.Morphology.MorphRule

/-!
# Modern Greek Reciprocal Fragment
@cite{nordlinger-2023} @cite{siloni-2008}

Modern Greek marks reciprocity with nonactive voice morphology (verbal
affix strategy, monovalent). The same morphology is used for reflexives,
passives, and middles — WALS Ch 106 classifies Greek as "mixed."

CAN form discontinuous reciprocals with "me" ('with'):
"O Giannis filithike me ti Maria" ('John kissed with Maria')
@cite{nordlinger-2023} ex. 27b, 36.

Greek allows discontinuous reciprocals (@cite{nordlinger-2023} ex. 27b),
which per Siloni's analysis implies lexical formation (Dimitriadis 2004, 2008).
-/

namespace Fragments.Greek.Reciprocals

open Core.Morphology

/-- Greek nonactive voice suffix as a morphological rule.

    The nonactive suffix (various allomorphs: -ome, -omai, etc.)
    marks reciprocal, reflexive, passive, and middle voice. -/
def nonactiveVoiceSuffix : MorphRule Bool :=
  { category := .voice
  , value := "nonactive"
  , formRule := fun stem => stem ++ "ome"
  , featureRule := fun f => { f with valence := some .intransitive }
  , semEffect := id
  }

/-- The Greek nonactive suffix is a voice operation (not valence). -/
theorem nonactive_is_voice :
    nonactiveVoiceSuffix.category = .voice := rfl

end Fragments.Greek.Reciprocals
