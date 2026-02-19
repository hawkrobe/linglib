import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.InformationTheory

/-!
# Information-Theoretic Foundations of RSA

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

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human pragmatic
  reasoning. arXiv:2005.06641.
- Frank, M. C. & Goodman, N. D. (2012). Predicting pragmatic reasoning in language games.
- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory.
-/

namespace RSA.InformationTheory

-- Re-export core information-theoretic definitions so that all existing
-- downstream code using `RSA.InformationTheory.entropy` etc. continues to work.
export Core.InformationTheory (log2Approx entropy conditionalEntropy mutualInformation)

/--
RSA iteration level.

Track the depth of pragmatic reasoning:
- L0 = literal listener
- S1 = pragmatic speaker (responds to L0)
- L1 = pragmatic listener (responds to S1)
- S2 = second-order speaker (responds to L1)
- etc.
-/
inductive RSALevel where
  | L : Nat → RSALevel  -- Listener level n
  | S : Nat → RSALevel  -- Speaker level n
  deriving DecidableEq, BEq, Repr

end RSA.InformationTheory
