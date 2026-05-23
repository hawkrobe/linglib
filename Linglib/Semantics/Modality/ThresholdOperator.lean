import Linglib.Core.Probability.Finite

/-!
# Threshold-operator substrate for PMF-based modal/attitudinal accounts

A tiny substrate of combinators and one property predicate that
factors the "must-style vs ought-style alternatives clause" distinction
*independently* of the "what eval function" distinction. Each modal /
attitudinal operator in linglib that lives on `PMF W → Set W → ℝ≥0∞`
substrate (currently: `mustCM`, `oughtCM`, `mightCM`, `mustPosterior`)
factors as `combinator eval p φ alts θ`, with `combinator` ∈
{`thresholdedExhaust`, `thresholdedDominance`, ...} and `eval` ∈
{`mustCMEval`, `posteriorEval`, ...}.

The headline divergence theorem `subsetFallacy_blocked_by_monotone`
is then stated *once*, parameterized over any posterior-monotone eval,
rather than copy-pasted per operator pair. The substantive empirical
claim of @cite{chung-mascarenhas-2024} that the modal conjunction
fallacy is rational under their operator is reframed structurally:
`mustCMEval` is *not* posterior-monotone — no posterior-monotone eval
can predict the fallacy direction.

## Out of scope

ℚ-valued operators (Lassiter's `want` family in
`Semantics/Attitudes/Desire.lean`) are a parallel substrate
with different parameter shape; their existing structure
`BeliefBasedDesireSemantics` explicitly excludes Lassiter
(`outside_belief_based_family`). Don't try to merge.

## Mathlib convention

We mirror the mathlib pattern `def Monotone (f) : Prop := ...` (a
property predicate on functions, not a typeclass): `IsPosteriorMonotone`
is a `Prop` on `EvalFn W`, not a `class`. Property-on-function is the
standard mathlib idiom for "this function satisfies P" reasoning.
-/

namespace Semantics.Modality.ThresholdOperator

open PMF
open scoped ENNReal

/-- A threshold-operator eval function: maps a PMF and a proposition
to a degree (expected utility for `mustCMEval`, posterior probability
for `posteriorEval`, etc.). The common shape across all PMF-ENNReal
threshold modal operators. -/
abbrev EvalFn (W : Type*) [Fintype W] : Type _ := PMF W → Set W → ℝ≥0∞

variable {W : Type*} [Fintype W]

/-- An eval function is *posterior-monotone* if it satisfies the same
monotonicity-in-conjunction property as a probability measure:
`sub ⊆ super → eval p sub ≤ eval p super`. The central empirical
claim of @cite{chung-mascarenhas-2024} is that this property is *false*
for `mustCMEval`; the central structural property of any posterior-
based account is that it *is* true. -/
def IsPosteriorMonotone (eval : EvalFn W) : Prop :=
  ∀ (p : PMF W) {sub super : Set W}, sub ⊆ super → eval p sub ≤ eval p super

/-- Must-style operator combinator: threshold clause plus exhaustification.
`thresholdedExhaust eval p φ alts θ` ↔ `eval p φ > θ ∧ ∀ψ ∈ alts. eval p ψ ≤ θ`.
Used by `mustCM` (with `eval = mustCMEval`) and `mustPosterior`
(degenerate, with empty alts). -/
def thresholdedExhaust (eval : EvalFn W)
    (p : PMF W) (φ : Set W) (alts : Finset (Set W)) (θ : ℝ≥0∞) : Prop :=
  eval p φ > θ ∧ ∀ ψ ∈ alts, eval p ψ ≤ θ

/-- Ought-style operator combinator: threshold clause plus strict-dominance
over alternatives. `thresholdedDominance eval p φ alts θ` ↔
`eval p φ > θ ∧ ∀ψ ∈ alts. eval p φ > eval p ψ`. Used by `oughtCM`
(@cite{chung-mascarenhas-2024} eq. (17)). -/
def thresholdedDominance (eval : EvalFn W)
    (p : PMF W) (φ : Set W) (alts : Finset (Set W)) (θ : ℝ≥0∞) : Prop :=
  eval p φ > θ ∧ ∀ ψ ∈ alts, eval p φ > eval p ψ

/-- **Headline divergence theorem.** Any posterior-monotone eval cannot
predict the *subsumption-fallacy direction*: there is no threshold at
which a strict-subset proposition exceeds the threshold while the
superset does not. The C&M operator `mustCMEval` predicts exactly this
direction (their modal-Linda eq. 32→34) — therefore `mustCMEval` is
*not* posterior-monotone, and any monotone competitor (e.g.
`posteriorEval`) makes the opposite prediction for free.

Pure consequence of monotonicity; the modal framing is just packaging. -/
theorem subsetFallacy_blocked_by_monotone
    {eval : EvalFn W} (hMono : IsPosteriorMonotone eval)
    (p : PMF W) {sub super : Set W} (hSub : sub ⊆ super) (θ : ℝ≥0∞) :
    ¬ (eval p sub > θ ∧ ¬ (eval p super > θ)) := by
  rintro ⟨hSub_gt, hSuper_not_gt⟩
  exact absurd hSub_gt
    (not_lt.mpr (le_trans (hMono p hSub) (not_lt.mp hSuper_not_gt)))

end Semantics.Modality.ThresholdOperator
