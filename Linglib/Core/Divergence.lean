import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Statistical Divergence Measures
@cite{herbstritt-franke-2019} @cite{goodman-stuhlmuller-2013} @cite{frank-goodman-2012}

Divergence measures between finite distributions, used as RSA speaker
utility functions. The choice of divergence measure is not neutral — it
determines which messages the speaker can consider:

| Divergence | Used by | Key property |
|------------|---------|-------------|
| KL | @cite{goodman-stuhlmuller-2013}, @cite{frank-goodman-2012} | D_KL = +∞ when Q(s) = 0 but P(s) > 0 |
| Hellinger | @cite{herbstritt-franke-2019} | Always finite, 0 ≤ HD ≤ 1 |

@cite{herbstritt-franke-2019} argues that Hellinger distance is necessary for
probability expressions because KL-divergence assigns infinite disutility to
messages whose literal interpretation assigns zero probability to states the
speaker considers possible. This means a KL-based speaker can never utter
"certainly" when there is any residual uncertainty — even when "certainly" is
the pragmatically correct choice.

Hellinger distance avoids this by measuring distributional overlap via
square roots, making it tolerant of "true enough" messages.

## Definitions

- `hellingerDistSq`: Squared Hellinger distance H²(P, Q) = 1 - BC(P, Q)
- `hellingerDist`: Hellinger distance HD(P, Q) = √H²(P, Q)
- `klDivergence`: KL divergence D_KL(P ∥ Q) = Σ_i P_i · ln(P_i / Q_i)
- `negHellingerDist`: Speaker utility = −HD (for softmax optimization)
-/

set_option autoImplicit false

namespace Core.Divergence

open Finset BigOperators Real

-- ============================================================================
-- §1. Bhattacharyya Coefficient
-- ============================================================================

/-- Bhattacharyya coefficient: BC(P, Q) = Σ_i √(P_i · Q_i).

    Measures distributional overlap. BC = 1 iff P = Q (for distributions),
    BC = 0 iff P and Q have disjoint support. -/
noncomputable def bhattacharyyaCoeff {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) : ℝ :=
  ∑ i : ι, √(P i * Q i)

-- ============================================================================
-- §2. Hellinger Distance
-- ============================================================================

/-- Squared Hellinger distance: H²(P, Q) = 1 − BC(P, Q).

    Ranges from 0 (identical distributions) to 1 (disjoint support).
    Avoids square roots in the outer computation, useful when only
    the ordering of distances matters (e.g., softmax speaker choice). -/
noncomputable def hellingerDistSq {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) : ℝ :=
  1 - bhattacharyyaCoeff P Q

/-- Hellinger distance: HD(P, Q) = √(H²(P, Q)).

    Satisfies 0 ≤ HD ≤ 1 for probability distributions. Unlike KL
    divergence, Hellinger distance is always finite and is a proper
    metric (symmetric, satisfies triangle inequality). -/
noncomputable def hellingerDist {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) : ℝ :=
  √(hellingerDistSq P Q)

/-- Negative Hellinger distance: the speaker utility in
    @cite{herbstritt-franke-2019}.

    EU(m, o, a) = −HD[P_rat.bel(·|o,a), P_LL(·|m)]

    The speaker maximizes this by choosing messages whose literal
    interpretation is closest (in Hellinger distance) to her beliefs. -/
noncomputable def negHellingerDist {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) : ℝ :=
  -hellingerDist P Q

-- ============================================================================
-- §3. KL Divergence
-- ============================================================================

/-- KL divergence: D_KL(P ∥ Q) = Σ_i P_i · ln(P_i / Q_i).

    NOT symmetric. Can be +∞ when Q_i = 0 and P_i > 0 (but
    `Real.log 0 = 0` in Lean/Mathlib, so this returns a finite but
    incorrect value — the caller must guard against this case).

    Used by @cite{frank-goodman-2012} and @cite{goodman-stuhlmuller-2013}
    as the basis for informativity: U(w; s) = ln P_lex(s|w). -/
noncomputable def klDivergence {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) : ℝ :=
  ∑ i : ι, P i * log (P i / Q i)

-- ============================================================================
-- §4. Properties
-- ============================================================================

/-- Squared Hellinger distance is non-negative when both distributions
    are non-negative and BC ≤ 1.

    For normalized distributions (Σ P_i = 1, Σ Q_i = 1), the
    Cauchy-Schwarz inequality gives BC(P,Q) ≤ 1, hence H² ≥ 0. -/
theorem hellingerDistSq_nonneg_of_bc_le_one {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) (h : bhattacharyyaCoeff P Q ≤ 1) :
    0 ≤ hellingerDistSq P Q := by
  unfold hellingerDistSq
  linarith

-- ============================================================================
-- §5. Relationship between KL and Hellinger
-- ============================================================================

/-!
### KL vs Hellinger: Theoretical Comparison

The two divergences are related by the inequality:

    H²(P, Q) ≤ D_KL(P ∥ Q)

This means KL-divergence is always at least as large as squared Hellinger
distance. The critical difference for RSA is at the boundary: when Q has
zero probability on a state that P considers possible:

- **KL**: D_KL = +∞ (message is impossible for the speaker to choose)
- **Hellinger**: HD < 1 (message has finite, bounded disutility)

This is why @cite{herbstritt-franke-2019} uses Hellinger: a speaker who is
95% sure of RED can still say "certainly RED" even though the literal
interpretation assigns 0 probability to some states the speaker considers
possible (with 5% residual uncertainty).
-/

-- ============================================================================
-- §6. KL Divergence → Speaker Utility Derivation
-- ============================================================================

/-!
### From KL Divergence to RSA Speaker Utility

The RSA speaker utility `U(u; s) = log L0(s | u)` arises from negative
KL divergence between the speaker's belief and the literal listener's
posterior. This derivation follows
[Scontras, Tessler & Franke (2025)](https://social-interaction-lab.org/problang-v2/chapters/app-02-bayesian-inference.html)
(Appendix: Bayesian inference and RSA).

**Step 1: Certain speaker.** When the speaker knows the true state s*,
her belief is a point mass δ_{s*}. The negative KL divergence is:

    −D_KL(δ_{s*} ∥ L0(·|u)) = −(1 · log(1/L0(s*|u))) = log L0(s*|u)

This is just surprisal — the standard RSA utility.

**Step 2: Uncertain speaker.** When the speaker has uncertain beliefs
P(s|O) (from partial observation O), the expected utility is:

    E_P[U(u; ·)] = Σ_s P(s|O) · log L0(s|u)

This decomposes as:

    E_P[U(u; ·)] = −D_KL(P ∥ L0(·|u)) + H(P)

where H(P) = −Σ_s P(s) log P(s) is the speaker's entropy.

**Step 3: Normalization.** Since H(P) is independent of the utterance u,
it cancels in the softmax:

    S1(u|O) ∝ exp(α · E_P[U(u; ·)]) ∝ exp(−α · D_KL(P ∥ L0(·|u)))

This is exactly the form used by @cite{goodman-stuhlmuller-2013}: the
speaker soft-maximizes expected log-likelihood under her beliefs.
-/

/-- Point mass distribution: probability 1 at state `s`, 0 elsewhere. -/
noncomputable def pointMass {ι : Type*} [DecidableEq ι] (s : ι) : ι → ℝ :=
  fun i => if i = s then 1 else 0

/-- KL divergence with a point mass reduces to negative log-probability
    (= surprisal). This is why the RSA speaker utility is `log L0(s|u)`.

    D_KL(δ_{s*} ∥ Q) = −log Q(s*)

    Proof: only the i = s* term survives (others are 0 · log(...) = 0),
    and the surviving term is 1 · log(1 / Q(s*)) = −log Q(s*). -/
theorem kl_pointMass_eq_neg_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι) (Q : ι → ℝ) (hQ : Q s > 0) :
    klDivergence (pointMass s) Q = -log (Q s) := by
  unfold klDivergence pointMass
  have key : ∀ i : ι, (if i = s then (1 : ℝ) else 0) * log ((if i = s then 1 else 0) / Q i) =
    if i = s then -log (Q s) else 0 := by
    intro i
    split
    · next h => subst h; simp [one_div, log_inv]
    · simp
  simp_rw [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Decomposition of KL divergence into cross-entropy and entropy:

    D_KL(P ∥ Q) = −E_P[log Q] + E_P[log P]
                 = −(Σ P_i log Q_i) + (Σ P_i log P_i)

    The second term (Σ P_i log P_i = −H(P)) is constant in Q, so it
    cancels in softmax normalization over utterances. This is why the
    RSA speaker with uncertain beliefs soft-maximizes
    E_P[log L0(s|u)] rather than −D_KL(P ∥ L0(·|u)). -/
theorem kl_eq_neg_crossEntropy_plus_negEntropy {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    klDivergence P Q =
    (∑ i : ι, P i * log (P i)) - (∑ i : ι, P i * log (Q i)) := by
  unfold klDivergence
  rw [show (∑ i : ι, P i * log (P i / Q i)) =
    ∑ i : ι, (P i * log (P i) - P i * log (Q i)) from by
    congr 1; ext i
    by_cases hPi : P i = 0
    · simp [hPi]
    · rw [log_div hPi (ne_of_gt (hQ i)), mul_sub]]
  simp only [← Finset.sum_sub_distrib]

/-- The expected log-likelihood under uncertain beliefs equals the
    negative KL divergence plus the speaker's entropy:

    Σ_s P(s) · log Q(s) = −D_KL(P ∥ Q) − H(P)

    In RSA: E_P[log L0(s|u)] = −D_KL(P ∥ L0(·|u)) + H(P).
    Since H(P) doesn't depend on u, softmax over u gives:
    S1(u|O) ∝ exp(α · E_P[log L0(·|u)]) ∝ exp(−α · D_KL(P ∥ L0(·|u))). -/
theorem expected_loglik_eq_neg_kl_plus_entropy {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    (∑ i : ι, P i * log (Q i)) =
    -klDivergence P Q + (∑ i : ι, P i * log (P i)) := by
  rw [kl_eq_neg_crossEntropy_plus_negEntropy P Q hQ]
  ring

end Core.Divergence
