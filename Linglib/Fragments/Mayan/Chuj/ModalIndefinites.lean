import Linglib.Syntax.Category.Determiner.ModalIndefinite

/-!
# Chuj modal indefinites

Lexical entries for Chuj *yalnhej* ([alonso-ovalle-royer-2024]) and *komon*
([alonso-ovalle-royer-2021]). The flavor a *yalnhej* DP contributes depends on its structural
position and the predicate's volitionality ([alonso-ovalle-royer-2024], §3.4): as an external
argument it contributes epistemic modality only; as an internal argument or adjunct of a
volitional predicate it contributes either epistemic or random-choice modality. The
derivation lives in `Studies/AlonsoOvalleRoyer2024.lean`.
-/

namespace Chuj.ModalIndefinites

/-- *yalnhej*: number-neutral, at-issue, epistemic or random choice, not upper-bounded,
projecting from any anchor ([alonso-ovalle-royer-2024], §3.1, §4.2). -/
def yalnhej : ModalIndefinite where
  form := "yalnhej"
  status := .atIssue
  flavors := {.epistemic, .circumstantial}
  upperBounded := false
  anchorConstraint := some .unrestricted
  numberNeutral := true

/-- *komon*: a modal modifier conveying random-choice modality, never epistemic
([alonso-ovalle-royer-2021]); the unremarkable reading holds of NP-*komon* only
([alonso-ovalle-royer-2024], §5). `upperBounded`, `numberNeutral`, and `anchorConstraint`
are inapplicable — *komon* DPs are headed by the indefinite *jun*, and *komon* fits neither
anchor constraint (never epistemic, yet fine with non-volitional predicates). -/
def komon : ModalIndefinite where
  form := "komon"
  status := .atIssue
  flavors := {.circumstantial}
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true

/-- The Chuj entries; [alonso-ovalle-royer-2021] analyzes *komon* as a modal modifier
rather than a determiner. -/
def paradigm : List ModalIndefinite := [yalnhej, komon]

end Chuj.ModalIndefinites
