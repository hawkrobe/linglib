import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Information-Theoretic Foundations of RSA (Stub)

The ℚ-based RSA evaluation infrastructure (RSAScenarioQ, RSA.Eval, RSA.Q) has been
removed. This file retains the information-theoretic definitions (entropy, KL divergence,
log2Approx) that are used by other modules (e.g., ArgumentativeStrength), but all
RSAScenarioQ-dependent computations and dynamics have been removed.

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

/--
Natural logarithm approximated as a rational (for decidable proofs).

We use a simple linear approximation log2(x) ≈ (x - 1) / (x + 1) * 2.885
This is only used for concrete computations; proofs use abstract properties.
For exact proofs about limiting behavior, we would need Mathlib.Analysis.
-/
def log2Approx (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else
    -- Linear approximation around x=1: log2(x) ≈ 2.885 * (x-1)/(x+1)
    -- Reasonably accurate for 0.5 < x < 2
    let ratio := (x - 1) / (x + 1)
    -- 2.885 ≈ 2/ln(2) but we use 3 for simplicity
    3 * ratio

/--
Shannon entropy of a distribution (in bits).

H(X) = -Σ_x P(x) log P(x)

Note: 0 log 0 is defined as 0 (standard convention).
-/
def entropy {α : Type} [BEq α] (dist : List (α × ℚ)) : ℚ :=
  let terms := dist.map λ (_, p) =>
    if p ≤ 0 then 0
    else -p * log2Approx p
  terms.foldl (· + ·) 0

/--
Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y).

Alternative: I(X;Y) = H(X) - H(X|Y) = H(Y) - H(Y|X)
-/
def mutualInformation {α β : Type} [BEq α] [BEq β]
    (joint : List ((α × β) × ℚ))
    (marginalX : List (α × ℚ))
    (marginalY : List (β × ℚ)) : ℚ :=
  entropy marginalX + entropy marginalY - entropy joint

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

/--
Conditional entropy H(Y|X) = H(X,Y) - H(X).

Used by MemorySurprisal for computing average surprisal S_M = H(W_t | M_t).
-/
def conditionalEntropy {α β : Type} [BEq α] [BEq β]
    (joint : List ((α × β) × ℚ))
    (marginalX : List (α × ℚ)) : ℚ :=
  entropy joint - entropy marginalX

end RSA.InformationTheory
