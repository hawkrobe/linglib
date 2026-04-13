import Linglib.Core.Modality.ModalTypes

/-!
# Portuguese Modal Verb Entries @cite{ferreira-2023}

Portuguese has a tripartite modal system with lexicalized weak necessity,
unlike Spanish (where cognate *deber* is strong necessity) or English
(where *ought*/*should* are ambiguous between X-marked and unmarked readings).

The six modal forms occupy two dimensions: modal force (possibility / weak
necessity / strong necessity) × X-marking (present / past imperfect):

| Force          | Unmarked (present) | X-marked (past imperfect) |
|----------------|--------------------|---------------------------|
| Possibility    | *pode*             | *podia*                   |
| Weak necessity | *deve*             | *devia*                   |
| Strong necessity| *tem que*         | *tinha que*               |

X-marking does not change modal force — it shifts the modal parameters
(modal base or ordering source), signaling presupposition suspension.
-/

namespace Fragments.Portuguese.Modals

open Core.Modality

/-! ## Helper -/

private def cp (fos : List ModalForce) (fls : List ModalFlavor) : List ForceFlavor :=
  ForceFlavor.cartesianProduct fos fls

private def allFlavors : List ModalFlavor := ModalFlavor.all

/-! ## Present tense (unmarked) modal entries -/

/-- *pode* 'can/may' — possibility modal, all flavors. -/
def poder : ModalItem where
  form := "pode"
  meaning := cp [.possibility] allFlavors

/-- *deve* 'ought/should' — weak necessity modal, all flavors.
    Portuguese lexicalizes weak necessity as a distinct root, unlike Spanish
    *deber* (strong necessity) or English *ought* (ambiguous). -/
def dever : ModalItem where
  form := "deve"
  meaning := cp [.weakNecessity] allFlavors

/-- *tem que* 'must/have to' — strong necessity modal, all flavors. -/
def terQue : ModalItem where
  form := "tem que"
  meaning := cp [.necessity] allFlavors

/-! ## Past imperfect (X-marked) modal entries -/

/-- *podia* 'could/might' — X-marked possibility. -/
def podia : ModalItem where
  form := "podia"
  meaning := cp [.possibility] allFlavors

/-- *devia* 'ought (counterfactual)' — X-marked weak necessity.
    Signals suspension of evidence against the prejacent
    (@cite{ferreira-2023}, §3.2). -/
def devia : ModalItem where
  form := "devia"
  meaning := cp [.weakNecessity] allFlavors

/-- *tinha que* 'had to (counterfactual)' — X-marked strong necessity. -/
def tinhaQue : ModalItem where
  form := "tinha que"
  meaning := cp [.necessity] allFlavors

/-! ## Force classification theorems -/

theorem poder_is_possibility :
    (poder.meaning.head!).force = .possibility := rfl

theorem dever_is_weakNecessity :
    (dever.meaning.head!).force = .weakNecessity := rfl

theorem terQue_is_necessity :
    (terQue.meaning.head!).force = .necessity := rfl

/-! ## Entailment ordering (force) -/

/-- *tem que* is at least as strong as *deve*. -/
theorem terQue_atLeastAsStrong_dever :
    ModalForce.necessity.atLeastAsStrong .weakNecessity = true := rfl

/-- *deve* is at least as strong as *pode*. -/
theorem dever_atLeastAsStrong_poder :
    ModalForce.weakNecessity.atLeastAsStrong .possibility = true := rfl

/-- *pode* is NOT at least as strong as *deve*. -/
theorem poder_not_atLeastAsStrong_dever :
    ModalForce.possibility.atLeastAsStrong .weakNecessity = false := rfl

/-! ## X-marking preserves force -/

/-- X-marking preserves force: *deve* and *devia* share the same force. -/
theorem xMarking_preserves_wn_force :
    (dever.meaning.head!).force = (devia.meaning.head!).force := rfl

/-- X-marking preserves force: *tem que* and *tinha que* share the same force. -/
theorem xMarking_preserves_sn_force :
    (terQue.meaning.head!).force = (tinhaQue.meaning.head!).force := rfl

/-- X-marking preserves force: *pode* and *podia* share the same force. -/
theorem xMarking_preserves_pos_force :
    (poder.meaning.head!).force = (podia.meaning.head!).force := rfl

/-! ## Cross-linguistic contrast: Portuguese vs Spanish -/

/-- Portuguese *deve* is weak necessity; Spanish cognate *deber* is strong.
    This is the key typological observation of @cite{ferreira-2023} §2:
    despite shared etymology, the languages diverged in modal force. -/
theorem portuguese_dever_weaker_than_spanish :
    ModalForce.weakNecessity.atLeastAsStrong .necessity = false := rfl

end Fragments.Portuguese.Modals
