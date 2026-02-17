/-
# Cremers, Wilcox & Spector (2023): RSA Exhaustivity Models

RSA models for exhaustivity and anti-exhaustivity. Baseline RSA predicts anti-exhaustivity
under biased priors, which contradicts human behavior. EXH-LU blocks this via exhaustification.

## Main definitions

`baselineL1`, `exhL1`, `freeLU_L1`, `svRSA_L1`, `exhLU_L1`, `wRSA_L1`, `bwRSA_L1`,
`rsaLI_uniform_L1`, `rsaLI_biased_L1`

## References

Cremers, A., Wilcox, E., & Spector, B. (2023). Exhaustivity and Anti-Exhaustivity
in the RSA Framework. Semantics & Pragmatics.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval

namespace RSA.Implementations.CremersWilcoxSpector2023

/-!
This file previously contained the full CWS2023 RSA implementation.
All definitions and theorems depend on Phenomena types (CWSConfig, CWSWorld,
CWSUtterance, etc.) and have been moved to
`Linglib.Phenomena.ScalarImplicatures.RSA_CremersWilcoxSpector2023Bridge`.
-/

end RSA.Implementations.CremersWilcoxSpector2023
