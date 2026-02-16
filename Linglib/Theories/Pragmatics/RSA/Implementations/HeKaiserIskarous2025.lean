/-
# He, Kaiser & Iskarous (2025): RSA Models for Polarity Asymmetries

Implementation of RSA models for sentence polarity asymmetries.

## Models Implemented

| Model | Description |
|-------|-------------|
| Standard RSA | Baseline with Boolean semantics and costs |
| fuzzyRSA | Soft semantics with polarity-specific interpretation |
| wonkyRSA | Complex prior for common ground update |
| funkyRSA | Combination of fuzzy + wonky |

## Insight

The paper shows that standard RSA fails to capture:
1. The interaction between state prior and polarity on utterance likelihood
2. Common ground update / typicality inferences

Extended models (fuzzyRSA, wonkyRSA) address these by:
- fuzzyRSA: Different soft-semantics functions for each polarity
- wonkyRSA: Joint inference over state and world wonkiness

## Reference

He, M., Kaiser, E., & Iskarous, K. (2025). "Modeling sentence polarity asymmetries:
Fuzzy interpretations in a possibly wonky world". SCiL 2025.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Core.Proposition
import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Entailment.Polarity

namespace RSA.Implementations.HeKaiserIskarous2025

/-!
This file previously contained the full He, Kaiser & Iskarous (2025) RSA implementation.
All definitions and theorems depend on Phenomena types (HKIConfig, HKIState, HKIUtterance,
literalTruth, utteranceCost, FuzzyParams, WorldType, Polarity, etc.) and have been moved to
`Linglib.Phenomena.Presupposition.Bridge_RSA_HeKaiserIskarous2025`.
-/

end RSA.Implementations.HeKaiserIskarous2025
