/-
# Yoon et al. (2020): Polite Speech RSA Model

"Polite Speech Emerges From Competing Social Goals"

## Innovation

This model has two speaker levels with different utility structures:
- **S1**: Balances informational + social utilities (weighted by phi)
- **S2**: Balances informational + social + presentational utilities (omega weights)

The presentational utility captures the speaker's desire to *appear* both
kind and honest, which uniquely drives preference for indirect speech.

## Model Structure

```
L0: Literal listener (soft semantics)
     |
S1: First-order speaker (phi-weighted info + social)
     |
L1: Pragmatic listener (jointly infers state s and goal phi)
     |
S2: Second-order speaker (omega-weighted info + social + presentational)
```

## Reference

Yoon, E. J., Tessler, M. H., Goodman, N. D., & Frank, M. C. (2020).
Polite Speech Emerges From Competing Social Goals.
Open Mind: Discoveries in Cognitive Science, 4, 71-87.
-/

import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Proposition

namespace RSA.Implementations.YoonEtAl2020

/-!
This file previously contained the full Yoon et al. (2020) RSA implementation.
All definitions and theorems depend on Phenomena types (HeartState, Utterance, SoftProp,
adjMeaning, utteranceSemantics, PolitenessConfig, InferredWeights, GoalCondition, etc.)
and have been moved to
`Linglib.Phenomena.Politeness.RSA_YoonEtAl2020Bridge`.
-/

end RSA.Implementations.YoonEtAl2020
