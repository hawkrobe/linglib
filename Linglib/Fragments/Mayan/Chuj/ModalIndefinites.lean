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

namespace Chuj.ModalIndefinites

open Features.ModalIndefinite

/-- *yalnhej*: number-neutral modal indefinite ([alonso-ovalle-royer-2024],
    §3.1, §4.2). At-issue, epistemic + random choice, not upper-bounded. -/
def yalnhejEntry : ModalIndefiniteEntry where
  form := "yalnhej"
  status := .atIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted
  numberNeutral := true

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
  form := "komon"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true
  anchorConstraint := none

/-- The Chuj entries. The papers themselves decline to classify *komon*
    as a modal indefinite: [alonso-ovalle-royer-2021] analyzes it as a
    modal *modifier* (vP-, D-, or NP-level), not a determiner. -/
def paradigm : List ModalIndefiniteEntry := [yalnhejEntry, komonEntry]

end Chuj.ModalIndefinites
