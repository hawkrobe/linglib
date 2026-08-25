import Linglib.Semantics.Modality.ModalTypes
import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# German Modal Verb Fragment

Lexical entries for German modal verbs, as `Auxiliary` entries cited by
their infinitives.

German has six core modals, each with fixed force and contextually variable
flavor. All modal meanings are Cartesian products (force × flavors), so
they all satisfy IFF.

| Modal    | 3sg  | Force       | Flavors                |
|----------|------|-------------|------------------------|
| können   | kann | possibility | epistemic, circumstantial |
| dürfen   | darf | possibility | deontic                |
| müssen   | muss | necessity   | epistemic, deontic     |
| sollen   | soll | necessity   | deontic                |
| mögen    | mag  | possibility | epistemic              |
| wollen   | will | necessity   | bouletic               |

Reference: Kratzer, A. (1981). The Notional Category of Modality.
-/

namespace German.Predicates.Modal

open Modality (ForceFlavor ModalForce ModalFlavor)

private abbrev cp := ForceFlavor.cartesianProduct

/-! ### Modal Entries -/

/-- *können* — "can/may": epistemic + circumstantial possibility. -/
def koennen : Auxiliary where
  form := "können"
  meaning := cp [.possibility] [.epistemic, .circumstantial]

/-- *dürfen* — "may/be allowed to": deontic possibility. -/
def duerfen : Auxiliary where
  form := "dürfen"
  meaning := cp [.possibility] [.deontic]

/-- *müssen* — "must/have to": epistemic + deontic necessity. -/
def muessen : Auxiliary where
  form := "müssen"
  meaning := cp [.necessity] [.epistemic, .deontic]

/-- *sollen* — "should/be supposed to": deontic necessity. -/
def sollen : Auxiliary where
  form := "sollen"
  meaning := cp [.necessity] [.deontic]

/-- *mögen* — "may" (epistemic): epistemic possibility. -/
def moegen : Auxiliary where
  form := "mögen"
  meaning := cp [.possibility] [.epistemic]

/-- *wollen* — "want to": bouletic necessity. -/
def wollen : Auxiliary where
  form := "wollen"
  meaning := cp [.necessity] [.bouletic]

/-- *sollte* — Konjunktiv II of *sollen*: weak necessity across multiple flavors.
    Treated as a **separate modal** from *sollen* because it has complex
    morphology (root + Konj. II), following the morphological individuation
    criterion of [steinert-threlkeld-imel-guo-2023] §4.3.
    Both *soll* and *sollte* individually satisfy IFF. -/
def sollte : Auxiliary where
  form := "sollte"
  meaning := cp [.weakNecessity] [.deontic, .epistemic, .circumstantial]

/-! ### All Modals -/

def allModals : List Auxiliary :=
  [koennen, duerfen, muessen, sollen, moegen, wollen, sollte]

/-! ### Grounding Theorems -/

/-- *sollte* has wider flavor range than *sollen* (morphological flavor change). -/
theorem sollte_wider_than_sollen :
    sollte.meaning.length > sollen.meaning.length := by decide

/-- Seven modals total (including *sollte* as distinct from *sollen*). -/
theorem allModals_size : allModals.length = 7 := rfl

end German.Predicates.Modal
