import Linglib.Theories.Semantics.Modality.Kratzer

/-!
# Probability-Ordering Bridge — Kratzer 2012 §2.4

Connects probability assignments to Kratzer ordering sources.

A probability assignment P over worlds induces an ordering source where
more probable worlds are ranked higher. For each world v, the ordering
source generates the proposition "at least as probable as v":
  λ w => decide (P(w) ≥ P(v))

This means w ≥_A z iff every probability threshold that z meets, w also meets,
which reduces to P(w) ≥ P(z).

## Key result

When the probability assignment is uniform, the induced ordering is trivial
(all worlds equivalent). When skewed, the best worlds are those with
maximal probability.

Reference: Kratzer, A. (2012). Modals and Conditionals. OUP. Ch. 2 §2.4.
-/

namespace IntensionalSemantics.Modal.ProbabilityOrdering

open IntensionalSemantics.Attitude.Intensional (World allWorlds)
open IntensionalSemantics.Modal.Kratzer

/-! ## Probability assignment -/

/-- A probability assignment maps worlds to rational probabilities. -/
abbrev ProbAssignment := World → ℚ

/-- Convert a probability assignment to a Kratzer ordering source.

    For each world v, generate the proposition "at least as probable as v":
    w satisfies this iff P(w) ≥ P(v). The resulting ordering ranks worlds
    by probability: w ≥_A z iff P(w) ≥ P(z). -/
def probToOrdering (prob : ProbAssignment) : OrderingSource := λ _ =>
  allWorlds.map λ v => (λ w => decide (prob w ≥ prob v))

/-! ## Concrete example -/

/-- A skewed probability assignment: P(w0) > P(w1) > P(w2) > P(w3). -/
def skewedProb : ProbAssignment := λ w =>
  match w with | .w0 => 4/10 | .w1 => 3/10 | .w2 => 2/10 | .w3 => 1/10

/-- A uniform probability assignment: P(w) = 1/4 for all w. -/
def uniformProb : ProbAssignment := λ _ => 1/4

/-! ## Theorems -/

/-- **Uniform probability makes all worlds equivalent under the ordering.**
    Every world satisfies the same set of ordering propositions (all of them). -/
theorem uniform_all_equivalent (w z : World) :
    atLeastAsGoodAs ((probToOrdering uniformProb) .w0) w z = true := by
  cases w <;> cases z <;> native_decide

/-- **Under skewed P, best worlds (from universal base) = {w0}.**
    w0 has the highest probability and dominates all others. -/
theorem prob_ordering_best_w0 (w : World) :
    bestWorlds emptyBackground (probToOrdering skewedProb) w = [.w0] := by
  cases w <;> native_decide

/-- **Probability ordering preserves ranking**: w0 ≥ w1 ≥ w2 ≥ w3. -/
theorem prob_ordering_w0_ge_w1 :
    atLeastAsGoodAs ((probToOrdering skewedProb) .w0) .w0 .w1 = true := by
  native_decide

theorem prob_ordering_w1_ge_w2 :
    atLeastAsGoodAs ((probToOrdering skewedProb) .w0) .w1 .w2 = true := by
  native_decide

theorem prob_ordering_w2_ge_w3 :
    atLeastAsGoodAs ((probToOrdering skewedProb) .w0) .w2 .w3 = true := by
  native_decide

/-- **Strict ordering**: w0 > w1 (w0 beats w1 but not vice versa). -/
theorem prob_ordering_w0_strict_w1 :
    strictlyBetter ((probToOrdering skewedProb) .w0) .w0 .w1 = true := by
  native_decide

/-- **Necessity under probability ordering**: with skewed P and universal base,
    any proposition true at w0 is necessary (since best = {w0}). -/
theorem prob_necessity_at_best (p : BProp World) (w : World)
    (hp : p .w0 = true) :
    necessity emptyBackground (probToOrdering skewedProb) p w = true := by
  unfold necessity
  rw [prob_ordering_best_w0]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact hp

end IntensionalSemantics.Modal.ProbabilityOrdering
