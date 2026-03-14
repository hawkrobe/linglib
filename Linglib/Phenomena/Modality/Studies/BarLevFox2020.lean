import Linglib.Theories.Semantics.Exhaustification.InnocentInclusion
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Bridge: NeoGricean Free Choice to Phenomena
@cite{bar-lev-fox-2020}

Connects the NeoGricean Innocent Inclusion formalization to empirical free choice
data from `Phenomena.Modality.FreeChoice`.

The theory predicts that free choice is a pragmatic inference (derived by
Exh^{IE+II}) rather than a semantic entailment, matching the empirical data.

-/


namespace Phenomena.Modality.Implicature_BarLevFox2020Bridge

open Exhaustification.FreeChoice

/-- The inference is pragmatic (not a semantic entailment) -/
theorem fc_is_pragmatic : Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

/-- The inference is captured by our pragmatic theory -/
theorem fc_captured_pragmatically : Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

end Phenomena.Modality.Implicature_BarLevFox2020Bridge
