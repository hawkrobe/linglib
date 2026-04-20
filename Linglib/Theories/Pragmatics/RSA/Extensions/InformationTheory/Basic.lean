import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.InformationTheory

/-!
# Information-Theoretic Foundations of RSA
@cite{cover-thomas-2006} @cite{frank-goodman-2012} @cite{zaslavsky-hu-levy-2020}

Re-exports domain-agnostic information-theoretic primitives from
`Core.InformationTheory` into the `RSA.InformationTheory` namespace,
and adds RSA-specific definitions (`RSALevel`).

The ℚ-based RSA evaluation infrastructure (RSAScenarioQ, RSA.Eval, RSA.Q) has been
removed. This file retains the re-exported information-theoretic definitions
(entropy, KL divergence, log2Approx) that are used by other modules
(e.g., ArgumentativeStrength), but all RSAScenarioQ-dependent computations
and dynamics have been removed.

## Original Results (To Be Re-derived with RSAConfig)

1. RSA as alternating maximization: RSA optimizes G_α = H_S(U|M) + α·E[V_L]
2. G_α monotonicity: G_α(S_t, L_t) ≤ G_α(S_{t+1}, L_{t+1})
3. Critical α = 1: Phase transition at α = 1
4. Utility non-monotonicity: E[V_L] can decrease even as G_α increases

-/

namespace RSA.InformationTheory

-- Re-export core information-theoretic definitions so that all existing
-- downstream code using `RSA.InformationTheory.entropy` etc. continues to work.
export Core.InformationTheory (log2Approx entropy conditionalEntropy mutualInformation
  jsdOf deltaP deltaPCounts)

end RSA.InformationTheory
