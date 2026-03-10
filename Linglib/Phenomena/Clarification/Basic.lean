import Linglib.Core.Agent.DecisionTheory

/-!
# Clarification: When to Ask vs. When to Act
@cite{raiffa-schlaifer-1961}

When agents face uncertainty about an interlocutor's goals, they choose
between acting under uncertainty and asking clarification questions (CQs).
Both @cite{tsvilodub-etal-2026} and @cite{dong-etal-2026} find that this
choice is governed by the **expected value of perfect information** (EVPI):
agents clarify when EVPI exceeds communication cost.

EVPI captures the interaction of uncertainty and stakes — it is high when
(a) uncertainty is high AND (b) acting incorrectly is costly. This
interaction is the core empirical finding shared by both papers.

## Connection to existing infrastructure

EVPI is the maximum possible `questionUtility` (@cite{van-rooy-2003}):
it equals `questionUtility` on the identity partition, where each world
is its own cell. Any specific clarification question yields at most EVPI.
-/

namespace Phenomena.Clarification

open Core.DecisionTheory BigOperators

/-- Maximum utility achievable at world `w` across actions. -/
def bestUtilityAt {W A : Type*} (dp : DecisionProblem W A)
    (actions : List A) (w : W) : ℚ :=
  actions.foldl (λ best a => max best (dp.utility w a)) 0

/-- Oracle value: expected utility under perfect information.
    `Σ_w P(w) · max_a U(w, a)` -/
def oracleValue {W A : Type*} [Fintype W] (dp : DecisionProblem W A)
    (actions : List A) : ℚ :=
  ∑ w : W, dp.prior w * bestUtilityAt dp actions w

/-- Expected value of perfect information (EVPI).

    EVPI = oracleValue − dpValue
         = Σ_w P(w) · max_a U(w,a) − max_a Σ_w P(w) · U(w,a)

    Equivalently, the expected regret of the current best action
    (@cite{tsvilodub-etal-2026}), or the upper bound on VoI for any
    question (@cite{dong-etal-2026}).

    @cite{raiffa-schlaifer-1961} -/
def evpi {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) : ℚ :=
  oracleValue dp actions - dpValue dp actions

/-- EVPI is non-negative: acting with perfect information is at least
    as good as acting without.

    TODO: prove via Jensen's inequality (max is convex) and the law of
    total expectation. The ℝ-valued analog is `eig_nonneg_of_convex`
    in `Core.Agent.ExperimentDesign`. -/
theorem evpi_nonneg {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (_hprior : ∀ w, 0 ≤ dp.prior w) (_hne : actions ≠ []) :
    0 ≤ evpi dp actions := by
  sorry

end Phenomena.Clarification
