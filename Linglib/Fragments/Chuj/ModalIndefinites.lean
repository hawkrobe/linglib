import Linglib.Features.ModalIndefinite

/-!
# Chuj Modal Indefinite Fragment
@cite{alonso-ovalle-royer-2021} @cite{alonso-ovalle-royer-2024}

Lexical entries for Chuj modal indefinites *yalnhej* (singular) and
*komon* (mass/plural), following @cite{alonso-ovalle-royer-2024}.

## Connection to VerbBuilding.lean

The Chuj voice system (@cite{coon-2019}, formalized in `VerbBuilding.lean`)
determines whether a *yalnhej* DP is in external or internal argument
position, which in turn constrains the available modal flavor:

- vØ (active transitive): agent = external → epistemic only
- v_ch (passive): theme promoted, agent implicit → both flavors available
- v_w (agentive intransitive): agent = external → epistemic only
- v_j (agentless passive): no agent → internal argument → both flavors

This connection is proved in `Phenomena/ModalIndefinites/Studies/AlonsoOvalleRoyer2024.lean`.

-/

set_option autoImplicit false

namespace Fragments.Chuj.ModalIndefinites

open Features.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entries
-- ════════════════════════════════════════════════════

/-- *yalnhej*: singular modal indefinite.
    At-issue, epistemic + random choice, not upper-bounded. -/
def yalnhejEntry : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "yalnhej"
  gloss := "MODAL.INDEF.SG"
  status := .atIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  positionSensitive := true
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted
  numberNeutral := true
  source := "Alonso-Ovalle & Royer 2024"

/-- *komon*: mass/plural modal modifier.
    At-issue, random choice only, not upper-bounded. -/
def komonEntry : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "komon"
  gloss := "MODAL.INDEF.MASS"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true
  anchorConstraint := some .unrestricted
  source := "Alonso-Ovalle & Royer 2021"

/-- The Chuj modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [yalnhejEntry, komonEntry]


-- ════════════════════════════════════════════════════
-- § 2. Cross-Entry Contrast
-- ════════════════════════════════════════════════════

/-- *yalnhej* and *komon* differ in flavor inventory: *yalnhej* has
    epistemic + RC, *komon* has RC only. -/
theorem yalnhej_komon_flavor_difference :
    yalnhejEntry.hasFlavor .epistemic ∧ ¬ komonEntry.hasFlavor .epistemic := by
  refine ⟨?_, ?_⟩ <;> decide


end Fragments.Chuj.ModalIndefinites
