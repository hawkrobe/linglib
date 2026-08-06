import Linglib.Features.ModalIndefinite

/-!
# Chuj Modal Indefinite Fragment

Lexical entries for Chuj *yalnhej* ([alonso-ovalle-royer-2024]) and
*komon* ([alonso-ovalle-royer-2021]).

The modal flavor a *yalnhej* DP contributes depends on its structural
position and the predicate's volitionality ([alonso-ovalle-royer-2024],
§3.4): as an external argument it contributes epistemic modality only;
as an internal argument (object or passive subject) or adjunct of a
volitional predicate it contributes either epistemic or random-choice
modality. Voice morphology ([coon-2019], voice heads in
`Studies/Coon2019.lean`) bears on this only by fixing where the DP
sits and whether an agent's decision subevent exists — the derivation
is formalized in `Studies/AlonsoOvalleRoyer2024.lean` (`rcAvailable`,
`predictedMIFlavors`).
-/

set_option autoImplicit false

namespace Chuj.ModalIndefinites

open Features.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entries
-- ════════════════════════════════════════════════════

/-- *yalnhej*: number-neutral modal indefinite ([alonso-ovalle-royer-2024],
    §3.1, §4.2). At-issue, epistemic + random choice, not upper-bounded. -/
def yalnhejEntry : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "yalnhej"
  gloss := "yalnhej"
  status := .atIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  positionSensitive := true
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted
  numberNeutral := true
  source := "Alonso-Ovalle & Royer 2024"

/-- *komon*: modal modifier conveying random-choice (circumstantial)
    modality ([alonso-ovalle-royer-2021]); never epistemic.

    Caveats: `hasUnremarkableReading` holds of NP-*komon* only
    ([alonso-ovalle-royer-2024], §5); `upperBounded := false` and
    `numberNeutral := false` are inapplicable rather than substantive —
    *komon*-DPs are headed by the singular indefinite *jun*, so those
    dimensions belong to the determiner; `anchorConstraint := none`
    because *komon* fits neither constructor (never epistemic, yet fine
    with non-volitional predicates) — the projection-function variation
    [alonso-ovalle-royer-2024] §6.2 leaves open. -/
def komonEntry : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "komon"
  gloss := "komon"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true
  anchorConstraint := none
  source := "Alonso-Ovalle & Royer 2021"

/-- The Chuj entries. The papers themselves decline to classify *komon*
    as a modal indefinite: [alonso-ovalle-royer-2021] analyzes it as a
    modal *modifier* (vP-, D-, or NP-level), not a determiner. -/
def paradigm : List ModalIndefiniteEntry := [yalnhejEntry, komonEntry]


-- ════════════════════════════════════════════════════
-- § 2. Cross-Entry Contrast
-- ════════════════════════════════════════════════════

/-- *yalnhej* and *komon* differ in flavor inventory: *yalnhej* has
    epistemic + RC, *komon* has RC only. -/
theorem yalnhej_komon_flavor_difference :
    yalnhejEntry.hasFlavor .epistemic ∧ ¬ komonEntry.hasFlavor .epistemic := by
  refine ⟨?_, ?_⟩ <;> decide


end Chuj.ModalIndefinites
