module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Semantics.Quantification.Lexicon

/-!
# English adverbs

Lexical entries for the English closed-class adverbs typed by their semantic owners: the modal
adverbs *certainly*, *definitely*, *necessarily*, *possibly*, *perhaps*, *maybe*, *probably* and
*potentially* as `Modality.ModalItem`s, with their force–flavor meanings and register, and the
adverbs of quantification *always*, *usually*, *sometimes* and *never* ([lewis-1975]) with the
force of the quantifier each lexicalizes. The modal-concord readings of *must certainly* and
*may possibly* and the situation-pronoun analysis of adverbs of quantification live in the
studies that treat them ([liu-rotter-2025], [percus-2000]).

## References

* [kratzer-1981]
* [lewis-1975]
* [percus-2000]
* [liu-rotter-2025]
-/

@[expose] public section

namespace English.Adverbs

/-! ### Modal adverbs -/

section ModalAdverbs

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def certainly : ModalItem := { form := "certainly", meaning := {ne}, register := .formal }
def definitely : ModalItem := { form := "definitely", meaning := {ne, nd} }
def necessarily : ModalItem := { form := "necessarily", meaning := {ne, nc}, register := .formal }
def possibly : ModalItem := { form := "possibly", meaning := {pe} }
def perhaps : ModalItem := { form := "perhaps", meaning := {pe}, register := .formal }
def maybe : ModalItem := { form := "maybe", meaning := {pe}, register := .informal }
def probably : ModalItem := { form := "probably", meaning := {ne} }
def potentially : ModalItem := { form := "potentially", meaning := {pc} }

def modalAdverbs : List ModalItem :=
  [certainly, definitely, necessarily, possibly, perhaps, maybe, probably, potentially]

end ModalAdverbs

/-! ### Adverbs of quantification -/

section AdverbsOfQuantification

open Quantifier.Lexicon

def always : Adverb := { form := "always", force := .universal }
def usually : Adverb := { form := "usually", force := .proportional }
def sometimes : Adverb := { form := "sometimes", force := .existential }
def never : Adverb := { form := "never", force := .negative }

end AdverbsOfQuantification

end English.Adverbs
