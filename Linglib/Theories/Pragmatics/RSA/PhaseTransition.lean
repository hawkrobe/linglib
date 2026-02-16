import Linglib.Theories.Pragmatics.RSA.Extensions.InformationTheory.Basic

/-!
# Rate-Distortion View of RSA

Formalizes the main results from Zaslavsky, Hu & Levy (2020),
"A Rate-Distortion view of human pragmatic reasoning" (arXiv:2005.06641).

## Results

1. **Proposition 1** (SM §B, Eq. 7–9): RSA dynamics implement alternating
   maximization of G_α. Each step is an argmax, so G_α is monotonically
   non-decreasing across iterations.

2. **Proposition 2** (main text p.3): E[V_L] can decrease even as G_α
   increases — disconfirming the conjecture that RSA maximizes expected
   listener utility.

3. **Proposition 3** (SM §C): Phase transition at α = 1.
   For α ∈ [0,1], the global optimum is non-informative:
   S*(u|m) = 1/|U|, L*(m|u) = P(m).
   For α ≥ 1, the optimum is a deterministic bijection.
   G*_α = max{(1−α) log K, 0} where K = min(|U|, |M|).

## The G_α Objective (Eq. 6)

G_α(S, L) = H_S(U|M) + α · E_S[V_L]

where H_S is speaker conditional entropy and V_L = log L(m|u).

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. arXiv:2005.06641.
- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory.
-/

namespace RSA.InformationTheory

-- ============================================================================
-- Eq. 6: G_α Decomposition
-- ============================================================================

/-- At α = 1, G_α reduces to the negative rate-distortion functional (Eq. 6).

G_1(S, L) = H_S(U|M) + E_S[V_L] = H_S(U|M) + E_S[log L(M|U)]

When L is deterministic this equals -I(U;M) = -R[D], connecting
pragmatic reasoning to optimal lossy compression. -/
theorem alpha_one_is_rate_distortion (S : RSA.RSAScenarioQ) (h : S.α = 1) :
    ∀ d : RSADynamicsQ S,
    G_alpha_at_Q S d = H_S_at_Q S d + E_VL_at_Q S d := by
  intro d
  simp only [G_alpha_at_Q, H_S_at_Q, E_VL_at_Q, h]
  ring

-- ============================================================================
-- Proposition 1: Alternating Maximization (SM §B, Eq. 7–9)
-- ============================================================================

/-!
## Alternating Maximization (Proposition 1)

RSA dynamics implement alternating maximization of G_α:

1. **Speaker update** (Eq. 7): S_t = argmax_S G_α[S, L_{t-1}]
   The softmax speaker is the unique maximizer of G_α for fixed L.

2. **Listener update** (Eq. 8): L_t = argmax_L G_α[S_t, L]
   The Bayesian listener is the unique maximizer of G_α for fixed S.

Combined (Eq. 9): G_α[S_t, L_{t-1}] ≤ G_α[S_t, L_t] ≤ G_α[S_{t+1}, L_t]

This is analogous to the EM algorithm: each half-step optimizes
G_α over one variable while holding the other fixed.
-/

/-- G_α is non-decreasing under RSA dynamics (Proposition 1, Eq. 9).

Each iteration of `stepDynamicsQ` performs a speaker update followed by a
listener update. Since each half-step is an argmax of G_α over the
updated variable, the combined step cannot decrease G_α.

TODO: Requires showing that (1) softmax is the argmax of H_S + α·E[V_L]
over S for fixed L (Lagrangian + KKT), and (2) Bayesian update is the
argmax of E[V_L] over L for fixed S (information projection). -/
theorem g_alpha_monotone_step (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S) :
    G_alpha_at_Q S d ≤ G_alpha_at_Q S (stepDynamicsQ S d) := by
  sorry

/-- Iterated RSA dynamics produce a non-decreasing G_α sequence.

Corollary of `g_alpha_monotone_step`: G_α(d_0) ≤ G_α(d_1) ≤ ··· -/
theorem g_alpha_monotone_iterated (S : RSA.RSAScenarioQ) (n : Nat) :
    G_alpha_at_Q S (runDynamicsQ S n) ≤
    G_alpha_at_Q S (runDynamicsQ S (n + 1)) := by
  sorry -- Follows from g_alpha_monotone_step by unfolding runDynamicsQ

-- ============================================================================
-- Proposition 2: Utility Non-Monotonicity (main text p.3)
-- ============================================================================

/-!
## Utility Non-Monotonicity (Proposition 2)

The paper's central negative result: E[V_L] is NOT guaranteed to increase
across RSA iterations, even though G_α is. The "expected utility"
conjecture (that RSA maximizes listener accuracy) is false.

> "We disconfirm Conjecture 1: ... the expected value of V_L is not
> guaranteed to increase across RSA recursion levels." (p.3)

This happens because G_α = H_S + α·E[V_L], and an increase in speaker
entropy H_S can outweigh a decrease in E[V_L], yielding a net G_α increase.

The counterexample requires initialization from the lexicon (not maximal
entropy), because maximal-entropy initialization gives S_0 = uniform,
which has maximal H_S — subsequent steps can only decrease H_S, so any
G_α increase must come from E[V_L] increases.
-/

/-- E[V_L] can decrease even as G_α increases (Proposition 2).

There exists an RSA scenario and dynamics state where a single step
of RSA dynamics increases G_α but decreases expected listener utility.

TODO: Construct the 3×3 counterexample from Figure 3 of the paper and
verify computationally. The scenario requires lexicon initialization
(not maximal entropy) and α < 1. -/
theorem utility_can_decrease :
    ∃ (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S),
      G_alpha_at_Q S d ≤ G_alpha_at_Q S (stepDynamicsQ S d) ∧
      E_VL_at_Q S (stepDynamicsQ S d) < E_VL_at_Q S d := by
  sorry

-- ============================================================================
-- Proposition 3: Phase Transition at α = 1 (SM §C)
-- ============================================================================

/-!
## Phase Transition (Proposition 3)

The global optimum of G_α exhibits a phase transition at α = 1:

**Sub-critical (α < 1)**: The unique global maximum is the non-informative
solution: S*(u|m) = 1/|U| for all u,m and L*(m|u) = P(m) for all m,u.
The speaker ignores the meaning entirely, and the listener falls back
to the prior. G*_α = (1-α) log |U| > 0.

**Super-critical (α > 1)**: The global maximum is achieved by a
deterministic bijection between meanings and utterances. Communication
is fully informative. G*_α = 0.

**Critical (α = 1)**: Both solutions achieve G*_1 = 0. This is the
phase transition point where informative communication becomes optimal.

The transition is sharp: for any ε > 0, the non-informative solution is
strictly suboptimal at α = 1 + ε.
-/

/-- Below the critical point, the non-informative solution is optimal
(Proposition 3, part 1).

For α < 1, the speaker who says each utterance with equal probability
regardless of the world achieves the global maximum of G_α. Informative
communication is suboptimal because the entropy bonus outweighs the
informativity gain.

TODO: Requires showing G_α(S_uniform, L_prior) ≥ G_α(S, L) for all S, L
when α < 1. The proof uses concavity of G_α in S and the fact that
uniform S maximizes H_S. -/
theorem subcritical_noninformative_optimal (S : RSA.RSAScenarioQ)
    (hα : S.α < 1) (d : RSADynamicsQ S) :
    G_alpha_at_Q S d ≤ G_alpha_at_Q S (initDynamicsQ S) := by
  sorry

/-- Above the critical point, deterministic communication is optimal
(Proposition 3, part 2).

For α > 1, the optimal speaker-listener pair is a deterministic bijection:
each meaning maps to exactly one utterance, and the listener perfectly
recovers the meaning. G*_α = 0.

TODO: Requires showing that for α > 1, H_S(S*) = 0 and E[V_L(S*, L*)] = 0
at the deterministic optimum, and that G_α(S*, L*) = 0 ≥ G_α(S, L)
for all S, L when α > 1. -/
theorem supercritical_deterministic_optimal (S : RSA.RSAScenarioQ)
    (hα : S.α > 1) :
    ∃ d : RSADynamicsQ S, G_alpha_at_Q S d = 0 := by
  sorry

-- ============================================================================
-- Concrete Verification
-- ============================================================================

/-- A 2×2 reference game for testing phase transition properties. -/
def phaseTestScenario (α : ℚ) (α_nonneg : 0 ≤ α := by norm_num) :
    RSA.RSAScenarioQ :=
  RSA.RSAScenarioQ.basicBool
    [true, false]  -- Two utterances
    [true, false]  -- Two worlds
    (λ w u => w == u)  -- Perfect alignment
    (α := α)
    (α_nonneg := α_nonneg)

/-- G_α is monotone for the 2×2 reference game at α = 1 (5 iterations). -/
theorem phase_test_monotone_at_alpha_one :
    isMonotoneG_alpha_Q (phaseTestScenario 1) 5 = true := by
  native_decide

/-- G_α is monotone for the 2×2 reference game at α = 2 (5 iterations). -/
theorem phase_test_monotone_at_alpha_two :
    isMonotoneG_alpha_Q (phaseTestScenario 2) 5 = true := by
  native_decide

-- ============================================================================
-- Utility Definitions
-- ============================================================================

/-- Whether α is at the rate-distortion critical point. -/
def isRateDistortionPoint (S : RSA.RSAScenarioQ) : Bool := S.α == 1

/-- Whether G_α has stabilized within ε of the previous step. -/
def hasConverged (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S) (ε : ℚ) :
    Bool :=
  let d' := stepDynamicsQ S d
  let g1 := G_alpha_at_Q S d
  let g2 := G_alpha_at_Q S d'
  (g2 - g1) < ε

/-- Number of iterations until G_α stabilizes within ε. -/
def convergenceIterations (S : RSA.RSAScenarioQ) (ε : ℚ)
    (maxIter : Nat) : Nat :=
  let iterations := List.range maxIter
  match iterations.find? (λ n => hasConverged S (runDynamicsQ S n) ε) with
  | some n => n
  | none => maxIter

end RSA.InformationTheory
