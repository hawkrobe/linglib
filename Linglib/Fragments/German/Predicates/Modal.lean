import Linglib.Semantics.Modality.Basic
import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# German modal verbs

Lexical entries for the German modal verbs as `Auxiliary` entries cited by their infinitives:
*können*, *dürfen*, *müssen*, *sollen*, *mögen* and *wollen*, each with a fixed force and a
contextually variable flavor in the sense of [kratzer-1981], so that every meaning is a product of
a force with a set of flavors; and the Konjunktiv II *sollte*, individuated as a separate modal on
the morphological criterion of [steinert-threlkeld-imel-guo-2023].

## References

* [kratzer-1981]
* [steinert-threlkeld-imel-guo-2023]
-/

namespace German.Predicates.Modal

open Modality (ForceFlavor ModalForce ModalFlavor)

/-! ### Modal Entries -/

/-- *können* — "can/may": epistemic + circumstantial possibility. -/
def koennen : Auxiliary where
  form := "können"
  modality := {.possibility} ×ˢ {.epistemic, .circumstantial}

/-- *dürfen* — "may/be allowed to": deontic possibility. -/
def duerfen : Auxiliary where
  form := "dürfen"
  modality := {.possibility} ×ˢ {.deontic}

/-- *müssen* — "must/have to": epistemic + deontic necessity. -/
def muessen : Auxiliary where
  form := "müssen"
  modality := {.necessity} ×ˢ {.epistemic, .deontic}

/-- *sollen* — "should/be supposed to": deontic necessity. -/
def sollen : Auxiliary where
  form := "sollen"
  modality := {.necessity} ×ˢ {.deontic}

/-- *mögen* — "may" (epistemic): epistemic possibility. -/
def moegen : Auxiliary where
  form := "mögen"
  modality := {.possibility} ×ˢ {.epistemic}

/-- *wollen* — "want to": bouletic necessity. -/
def wollen : Auxiliary where
  form := "wollen"
  modality := {.necessity} ×ˢ {.bouletic}

/-- *sollte* — Konjunktiv II of *sollen*: weak necessity across multiple flavors.
    Treated as a **separate modal** from *sollen* because it has complex
    morphology (root + Konj. II), following the morphological individuation
    criterion of [steinert-threlkeld-imel-guo-2023] §4.3.
    Both *soll* and *sollte* individually satisfy IFF. -/
def sollte : Auxiliary where
  form := "sollte"
  modality := {.weakNecessity} ×ˢ {.deontic, .epistemic, .circumstantial}

/-! ### All Modals -/

def allModals : List Auxiliary :=
  [koennen, duerfen, muessen, sollen, moegen, wollen, sollte]

/-! ### Grounding Theorems -/

/-- *sollte* has a wider flavor range than *sollen*, the morphological flavor change. -/
theorem sollen_flavors_ssubset_sollte :
    sollen.toModalItem.flavors ⊂ sollte.toModalItem.flavors := by decide

end German.Predicates.Modal
