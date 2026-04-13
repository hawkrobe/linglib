import Linglib.Core.Logic.ModalLogic

/-!
# German Modal Verb Fragment

Lexical entries for German modal verbs, following the pattern of English
`AuxEntry` from `Fragments.English.FunctionWords`.

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

namespace Fragments.German.Predicates.Modal

open Core.Modality (ForceFlavor ModalForce ModalFlavor)

/-- German modal verb entry. -/
structure GermanModalEntry where
  /-- Infinitive form -/
  form : String
  /-- 3sg present form -/
  form3sg : String
  /-- Modal meaning as force-flavor pairs -/
  modalMeaning : List ForceFlavor
  deriving Repr, BEq

private abbrev cp := ForceFlavor.cartesianProduct

-- ============================================================================
-- § 1: Modal Entries
-- ============================================================================

/-- *können* — "can/may": epistemic + circumstantial possibility. -/
def koennen : GermanModalEntry where
  form := "können"
  form3sg := "kann"
  modalMeaning := cp [.possibility] [.epistemic, .circumstantial]

/-- *dürfen* — "may/be allowed to": deontic possibility. -/
def duerfen : GermanModalEntry where
  form := "dürfen"
  form3sg := "darf"
  modalMeaning := cp [.possibility] [.deontic]

/-- *müssen* — "must/have to": epistemic + deontic necessity. -/
def muessen : GermanModalEntry where
  form := "müssen"
  form3sg := "muss"
  modalMeaning := cp [.necessity] [.epistemic, .deontic]

/-- *sollen* — "should/be supposed to": deontic necessity. -/
def sollen : GermanModalEntry where
  form := "sollen"
  form3sg := "soll"
  modalMeaning := cp [.necessity] [.deontic]

/-- *mögen* — "may" (epistemic): epistemic possibility. -/
def moegen : GermanModalEntry where
  form := "mögen"
  form3sg := "mag"
  modalMeaning := cp [.possibility] [.epistemic]

/-- *wollen* — "want to": bouletic necessity. -/
def wollen : GermanModalEntry where
  form := "wollen"
  form3sg := "will"
  modalMeaning := cp [.necessity] [.bouletic]

/-- *sollte* — Konjunktiv II of *sollen*: weak necessity across multiple flavors.
    Treated as a **separate modal** from *sollen* because it has complex
    morphology (root + Konj. II), following the morphological individuation
    criterion of @cite{steinert-threlkeld-imel-guo-2023} §4.3.
    Both *soll* and *sollte* individually satisfy IFF. -/
def sollte : GermanModalEntry where
  form := "sollte"
  form3sg := "sollte"
  modalMeaning := cp [.weakNecessity] [.deontic, .epistemic, .circumstantial]

-- ============================================================================
-- § 2: All Modals
-- ============================================================================

def allModals : List GermanModalEntry :=
  [koennen, duerfen, muessen, sollen, moegen, wollen, sollte]

-- ============================================================================
-- § 3: Grounding Theorems
-- ============================================================================

/-- *können* is possibility. -/
theorem koennen_is_possibility :
    koennen.modalMeaning = cp [.possibility] [.epistemic, .circumstantial] := rfl

/-- *müssen* is necessity. -/
theorem muessen_is_necessity :
    muessen.modalMeaning = cp [.necessity] [.epistemic, .deontic] := rfl

/-- *dürfen* is deontic possibility only. -/
theorem duerfen_is_deontic :
    duerfen.modalMeaning = cp [.possibility] [.deontic] := rfl

/-- *sollen* is deontic necessity; *wollen* is bouletic necessity. -/
theorem sollen_deontic : sollen.modalMeaning = cp [.necessity] [.deontic] := rfl
theorem wollen_bouletic : wollen.modalMeaning = cp [.necessity] [.bouletic] := rfl

/-- *sollte* has wider flavor range than *sollen* (morphological flavor change). -/
theorem sollte_wider_than_sollen :
    sollte.modalMeaning.length > sollen.modalMeaning.length := by native_decide

/-- Seven modals total (including *sollte* as distinct from *sollen*). -/
theorem allModals_size : allModals.length = 7 := rfl

end Fragments.German.Predicates.Modal
