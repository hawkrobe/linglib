module

public import Linglib.Semantics.Modality.Basic

/-!
# Niuean Modal Inventory

[matthewson-2016] [matthewson-et-al-2012] [seiter-1980]

Niuean (Polynesian, ISO 639-3 `niu`) modal system. Niuean exemplifies
a typological pattern where force distinctions are encoded in the
**circumstantial** domain (separate possibility and necessity modals)
but absent in the **epistemic** domain (a single general-purpose
epistemic modal covers both force values).

## Modal inventory

| Modal   | Domain         | Force           | Source                         |
|---------|---------------|-----------------|--------------------------------|
| liga    | epistemic     | poss + nec      | [matthewson-et-al-2012]   |
| maeke   | circumstantial| possibility     | [seiter-1980] p. 140      |
| lata    | circumstantial| necessity       | [seiter-1980] p. 133      |

## Key data ([matthewson-2016] §18.5, examples 64–68)

(64) *liga kua fano tei* — 'He might have left.'
     ([matthewson-et-al-2012] p. 224)

(65) *Hí ika a Tom he aho nei ... liga malolo a ia*
     'Tom is fishing today ... he's probably well.'
     ([matthewson-et-al-2012] p. 228)

(66) *ne liga kua veli hifo e tama ke he pelapela*
     'The boy must have fallen in the mud.'
     ([seiter-1980] p. 13)

(67) *kua maeke he tama ia ke taute pasikala afi*
     'That child is able to fix motorbikes.'
     ([seiter-1980] p. 140)

(68) *lata ke ō a tautolu he aho nei ki Queen Street*
     'We should go to Queen Street today.'
     ([seiter-1980] p. 133)

## Typological significance

[matthewson-2016] §18.5: Niuean tests whether epistemic modals
are more likely to lack duals than circumstantial modals. The pattern —
general-purpose epistemic + dual circumstantial — is consistent with
Gitksan (variable-force epistemics, dual circumstantials) and with the
broader cross-linguistic tendency for force distinctions to be encoded
in the root/circumstantial domain.
-/

@[expose] public section

namespace Niuean

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

/-! ## Modal expressions -/

/-- General-purpose epistemic modal: usable in both possibility and
    necessity contexts. [matthewson-et-al-2012].
    Translatable as 'might', 'probably', 'must' depending on context. -/
def liga : ModalItem := { form := "liga", meaning := {pe, ne} }

/-- Circumstantial possibility modal ('able to', 'can').
    [seiter-1980] p. 140. -/
def maeke : ModalItem := { form := "maeke", meaning := {pc} }

/-- Circumstantial necessity modal ('should', 'must').
    [seiter-1980] p. 133. -/
def lata : ModalItem := { form := "lata", meaning := {nc} }

def modals : List ModalItem := [liga, maeke, lata]

end Niuean
