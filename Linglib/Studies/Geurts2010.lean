import Linglib.Studies.GeurtsPouscoulous2009

/-!
# Geurts (2010): Quantity Implicatures

This file records the pattern [geurts-2010]'s textbook takes over from
[geurts-pouscoulous-2009]: scalar inferences embedded under a quantifier are available in an
upward-entailing scope and blocked in a downward-entailing one. The pattern is the conventionalist
prediction the earlier paper tests, stated there as `PredictsLocalSIWeak` and `PredictsLocalSI`
over the scope monotonicity of the embedding quantifier; the textbook's own account of
implicature is not formalized here.

## References

* [geurts-2010]
* [geurts-pouscoulous-2009]
-/

namespace Geurts2010

open Quantification GeurtsPouscoulous2009

variable {α : Type*}

/-- The upward-entailing scope of *all* admits a local inference and the downward-entailing scope
of *not all* excludes one on either version of the prediction. -/
theorem ue_de_pattern :
    PredictsLocalSIWeak (every_sem : GQ α) ∧ ¬ PredictsLocalSI (outerNeg (every_sem : GQ α)) :=
  ⟨every_scope_up, not_not.mpr (outerNeg_up_to_down _ every_scope_up)⟩

end Geurts2010
