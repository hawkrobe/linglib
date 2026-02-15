import Linglib.Phenomena.Modality.Studies.Khoo2015
import Linglib.Theories.DynamicSemantics.Effects.Epistemic.Basic

/-!
# Bridge: Khoo (2015) × Neo-Stalnakerian Framework

Connects the modal disagreement data in `Phenomena.Modality.Studies.Khoo2015`
to predictions from Rudin's (2025) Neo-Stalnakerian Framework formalized in
`Theories.DynamicSemantics.Effects.Epistemic.Basic`.

## Predictions verified

- `nsf_predicts_khoo_pattern`: The NSF correctly predicts the dissociation
  between rejection and falsity for epistemic might-claims

## Known gaps

- No formalization of Khoo's own proposed semantics for comparison
-/

namespace Phenomena.Modality.Studies.Khoo2015.Bridge

open DynamicSemantics.NeoStalnakerian

/-- The Mobster scenario has the structure predicted by the NSF:
    Smith (assertor) has examined evidence consistent with Fat Tony being dead,
    so his epistemic state contains p-worlds (p = "Fat Tony is dead").
    Beth (rejector) knows Fat Tony is alive, so her epistemic state has no p-worlds.

    The NSF predicts:
    1. Smith's assertion is true (his state is in MI(might-p))
    2. Beth's rejection is licensed (her state is not might-p-compatible)

    This matches Khoo's finding: speakers reject the might-claim without
    judging it false. -/
theorem nsf_predicts_khoo_pattern
    {W : Type*} (p : BProp W) (smith beth : List W)
    (h_smith : smith.any p = true)
    (h_beth : beth.any p = false) :
    MI (mightSimple p) smith ∧ rejectionLicensed (mightSimple p) beth :=
  might_truth_acceptance_dissociate p smith beth h_smith h_beth

end Phenomena.Modality.Studies.Khoo2015.Bridge
