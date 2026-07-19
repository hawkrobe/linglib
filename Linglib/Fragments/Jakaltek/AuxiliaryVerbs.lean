
/-!
# Jakaltek (Jacaltec) Auxiliary Verb Fragment
[anderson-2006]

Jakaltek (Mayan; Guatemala) has auxiliary verb constructions with a
**split** inflectional pattern: absolutive (object) arguments are marked
on aspectual auxiliaries, while ergative (subject) arguments are marked
on lexical verbs. This is the reverse of the more common split where
subject appears on the auxiliary.

Source: Craig 1977, cited in [anderson-2006].
-/

namespace Jakaltek.AuxiliaryVerbs


/-- Primary AVC example form.
    *šk-ach w-ila*
    'COMPL-ABS2 ERG1-see'
    'I saw you'
    (Craig 1977: 60, cited in [anderson-2006]). -/
def form : String := "šk-ach w-ila"

def gloss : String := "COMPL-ABS2 ERG1-see 'I saw you'"

def family : String := "Mayan"
def location : String := "Guatemala"


end Jakaltek.AuxiliaryVerbs
