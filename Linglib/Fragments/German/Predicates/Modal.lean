import Linglib.Core.ModalLogic

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
| wollen   | will | necessity   | deontic                |

Note: *wollen* is bouletic, mapped to deontic in the 2×3 space per
`BouleticFlavor.flavorTag = .deontic`.

Reference: Kratzer, A. (1981). The Notional Category of Modality.
-/

namespace Fragments.German.Predicates.Modal

open Core.ModalLogic (ForceFlavor ModalForce ModalFlavor)

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

/-- *wollen* — "want to": bouletic → deontic in 2×3 space. -/
def wollen : GermanModalEntry where
  form := "wollen"
  form3sg := "will"
  modalMeaning := cp [.necessity] [.deontic]

-- ============================================================================
-- § 2: All Modals
-- ============================================================================

def allModals : List GermanModalEntry :=
  [koennen, duerfen, muessen, sollen, moegen, wollen]

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

/-- *sollen* and *wollen* both map to deontic necessity. -/
theorem sollen_wollen_deontic :
    sollen.modalMeaning = cp [.necessity] [.deontic] ∧
    wollen.modalMeaning = cp [.necessity] [.deontic] := ⟨rfl, rfl⟩

/-- Six modals total. -/
theorem allModals_size : allModals.length = 6 := rfl

end Fragments.German.Predicates.Modal
