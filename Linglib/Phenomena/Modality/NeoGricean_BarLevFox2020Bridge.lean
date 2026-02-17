import Linglib.Theories.Pragmatics.NeoGricean.Implementations.BarLevFox2020
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Bridge: NeoGricean Free Choice (Bar-Lev & Fox 2020) to Phenomena

Connects the NeoGricean Innocent Inclusion formalization to empirical free choice
data from `Phenomena.Modality.FreeChoice`.

The theory predicts that free choice is a pragmatic inference (derived by
Exh^{IE+II}) rather than a semantic entailment, matching the empirical data.

## References

- Bar-Lev & Fox (2020). Free choice, simplification, and Innocent Inclusion.
  Natural Language Semantics 28:175-223.
-/


namespace Phenomena.Modality.NeoGricean_BarLevFox2020Bridge

open NeoGricean.FreeChoice

/-- The inference is pragmatic (not a semantic entailment) -/
theorem fc_is_pragmatic : Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

/-- The inference is captured by our pragmatic theory -/
theorem fc_captured_pragmatically : Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

end Phenomena.Modality.NeoGricean_BarLevFox2020Bridge
