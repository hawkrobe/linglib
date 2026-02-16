/-
# Yoon et al. (2020): Polite Speech RSA Model

"Polite Speech Emerges From Competing Social Goals"

## Innovation

This model has two speaker levels with different utility structures:
- **S1**: Balances informational + social utilities (weighted by φ)
- **S2**: Balances informational + social + presentational utilities (ω weights)

The presentational utility captures the speaker's desire to *appear* both
kind and honest, which uniquely drives preference for indirect speech.

## Model Structure

```
L0: Literal listener (soft semantics)
     ↑
S1: First-order speaker (φ-weighted info + social)
     ↑
L1: Pragmatic listener (jointly infers state s and goal φ)
     ↑
S2: Second-order speaker (ω-weighted info + social + presentational)
```

## Reference

Yoon, E. J., Tessler, M. H., Goodman, N. D., & Frank, M. C. (2020).
Polite Speech Emerges From Competing Social Goals.
Open Mind: Discoveries in Cognitive Science, 4, 71-87.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Linglib.Core.MeasurementScale
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Proposition

namespace RSA.Implementations.YoonEtAl2020

/-!
This file previously contained the full Yoon et al. (2020) RSA implementation.
All definitions and theorems depend on Phenomena types (HeartState, Utterance, SoftProp,
adjMeaning, utteranceSemantics, PolitenessConfig, InferredWeights, GoalCondition, etc.)
and have been moved to
`Linglib.Phenomena.Politeness.Bridge_RSA_YoonEtAl2020`.
-/

end RSA.Implementations.YoonEtAl2020
