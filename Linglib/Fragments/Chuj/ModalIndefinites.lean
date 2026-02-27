import Linglib.Core.ModalIndefinite

/-!
# Chuj Modal Indefinite Fragment

Lexical entries for Chuj modal indefinites *yalnhej* (singular) and
*komon* (mass/plural), following Alonso-Ovalle & Royer (2024).

These entries reuse the `ModalIndefiniteEntry` type from
`Core/ModalIndefinite.lean`, instantiating the three-dimensional
typological profile for Chuj.

## Connection to VerbBuilding.lean

The Chuj voice system (Coon 2019, formalized in `VerbBuilding.lean`)
determines whether a *yalnhej* DP is in external or internal argument
position, which in turn constrains the available modal flavor:

- vØ (active transitive): agent = external → epistemic only
- v_ch (passive): theme promoted, agent implicit → both flavors available
- v_w (agentive intransitive): agent = external → epistemic only
- v_j (agentless passive): no agent → internal argument → both flavors

This connection is proved in `Phenomena/ModalIndefinites/Bridge/KratzerAnchoring.lean`.

## References

- Alonso-Ovalle, L. & Royer, J. (2024). Modal indefinites: Lessons from
  Chuj. Linguistics and Philosophy.
- Alonso-Ovalle, L. & Royer, J. (2021). On Chuj modal indefinites.
-/

namespace Fragments.Chuj.ModalIndefinites

open Core.ModalIndefinite
open Core.ModalLogic (ModalFlavor)


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
  source := "Alonso-Ovalle & Royer 2021"


-- ════════════════════════════════════════════════════
-- § 2. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem yalnhej_at_issue : yalnhejEntry.status = .atIssue := rfl
theorem yalnhej_has_epistemic : yalnhejEntry.hasEpistemic = true := by native_decide
theorem yalnhej_has_rc : yalnhejEntry.hasCircumstantial = true := by native_decide
theorem yalnhej_not_ub : yalnhejEntry.upperBounded = false := rfl
theorem yalnhej_pos_sensitive : yalnhejEntry.positionSensitive = true := rfl

theorem komon_at_issue : komonEntry.status = .atIssue := rfl
theorem komon_rc_only : komonEntry.hasEpistemic = false ∧ komonEntry.hasCircumstantial = true := by
  constructor <;> native_decide
theorem komon_not_ub : komonEntry.upperBounded = false := rfl

/-- *yalnhej* and *komon* differ in flavor inventory: *yalnhej* has
    epistemic + RC, *komon* has RC only. -/
theorem yalnhej_komon_flavor_difference :
    yalnhejEntry.hasEpistemic = true ∧ komonEntry.hasEpistemic = false := by
  constructor <;> native_decide


end Fragments.Chuj.ModalIndefinites
