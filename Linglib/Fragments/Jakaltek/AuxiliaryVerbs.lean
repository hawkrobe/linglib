import Linglib.Core.Morphology.MorphRule

/-!
# Jakaltek (Jacaltec) Auxiliary Verb Fragment
@cite{anderson-2006}

Jakaltek (Mayan; Guatemala) has auxiliary verb constructions with a
**split** inflectional pattern: absolutive (object) arguments are marked
on aspectual auxiliaries, while ergative (subject) arguments are marked
on lexical verbs. This is the reverse of the more common split where
subject appears on the auxiliary.

Source: Craig 1977, cited in @cite{anderson-2006}.
-/

namespace Fragments.Jakaltek.AuxiliaryVerbs

open Core.Morphology (InflDistribution MorphCategory)

/-- Primary AVC example form.
    *šk-ach w-ila*
    'COMPL-ABS2 ERG1-see'
    'I saw you'
    (Craig 1977: 60, cited in @cite{anderson-2006}). -/
def form : String := "šk-ach w-ila"

def gloss : String := "COMPL-ABS2 ERG1-see 'I saw you'"

def family : String := "Mayan"
def location : String := "Guatemala"

/-- Split inflection distribution: AUX hosts aspect and absolutive agreement
    (= object in transitive); LV hosts ergative agreement (= subject in
    transitive). Both absolutive and ergative cross-referencing are
    `.agreement` at the `MorphCategory` level; the split is within the
    agreement system (absolutive vs. ergative), not between category types. -/
def inflDistribution : InflDistribution :=
  { onAux := [.aspect, .agreement]
  , onLex := [.agreement] }

end Fragments.Jakaltek.AuxiliaryVerbs
