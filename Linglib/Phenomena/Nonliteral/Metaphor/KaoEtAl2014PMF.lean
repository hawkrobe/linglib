import Linglib.Core.Probability.PMFPosterior
import Linglib.Phenomena.Nonliteral.Metaphor.KaoEtAl2014
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# @cite{kao-etal-2014-metaphor} on mathlib `PMF` (Phase 2 stress test)
@cite{kao-etal-2014-hyperbole} @cite{kao-etal-2014-metaphor}

Stress test for the Phase-2 architecture: the metaphor model differs from
@cite{frank-goodman-2012} on **every** axis that mattered for the FG2012
pilot — α = 3 not 1, weighted (non-uniform) world prior, latent QUDs that
project the speaker's utility, predicate-marginal predictions.

Where FG2012 collapsed onto `PMF.uniformOfFinset` (because Eq. S3 of its
supplement IS uniform-on-extension), this model has real-valued meaning
(the feature prior baked into L0), so we keep `PMF.normalize`. The PMF
machinery still carries the construction:

* `PMF.normalize` for S1 at each `(g, w)` — Eq. 5 of @cite{kao-etal-2014-hyperbole}
  with α = 3, no utterance cost.
* `PMF.bind` against a goal prior to marginalise over QUDs — the key
  payoff over the FG2012 pilot, which had no latent variable.
* `PMF.posterior` for L1 — Bayesian inversion against the world prior.

All positivity bookkeeping flows from one fact: every world's own category
gives a nonzero meaning value (the feature prior is strictly positive on
all 16 cells). That single witness drives all four `≠ 0` hypotheses
(`projectedMeaning > 0`, `S1g support`, marginal speaker support, L1
marginal positivity).

## Reused from `KaoEtAl2014.lean`

* `Cat`, `Goal`, `World`, `featurePrior`, `catPrior`, `project` — the
  empirical priors and QUD projection.
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Metaphor.KaoEtAl2014.PMF

open scoped ENNReal
open Phenomena.Nonliteral.Metaphor.KaoEtAl2014

instance : Fintype World := by unfold World; infer_instance
instance : Nonempty World := ⟨(.whale, false, false, false)⟩

/-! ## §1. Lifted priors -/

/-- ENNReal lift of `featurePrior`. -/
noncomputable def featurePriorE (c : Cat) (large graceful majestic : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (featurePrior c large graceful majestic)

/-- ENNReal lift of `catPrior`. -/
noncomputable def catPriorE : Cat → ℝ≥0∞
  | .whale => 1
  | .person => 99

/-- The unnormalised joint world prior `P(cat) · P(features | cat)`. -/
noncomputable def worldPriorRaw (w : World) : ℝ≥0∞ :=
  catPriorE w.1 * featurePriorE w.1 w.2.1 w.2.2.1 w.2.2.2

/-! ## §2. Meaning function

@cite{kao-etal-2014-metaphor}'s `meaning` bakes the feature prior into L0:
`meaning(u, w) = featurePrior(w) if u = w.cat else 0`. -/

noncomputable def meaningE (u : Cat) (w : World) : ℝ≥0∞ :=
  if u = w.1 then featurePriorE w.1 w.2.1 w.2.2.1 w.2.2.2 else 0

/-! ## §3. Coverage — the witness that drives every positivity proof

The metaphor analogue of @cite{frank-goodman-2012}'s `covering` lemma:
every world's own category gives positive meaning at that world. -/

/-- Every entry of `featurePrior` is strictly positive. Verified per cell. -/
theorem featurePriorE_pos (c : Cat) (a b d : Bool) : featurePriorE c a b d ≠ 0 := by
  unfold featurePriorE
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  cases c <;> cases a <;> cases b <;> cases d <;>
    (unfold featurePrior; norm_num)

/-- Coverage: the speaker can always describe a world by its own category. -/
theorem meaningE_self_ne_zero (w : World) : meaningE w.1 w ≠ 0 := by
  unfold meaningE; simp [featurePriorE_pos]

/-! ## §4. QUD projection -/

/-- Equivalence class of `w` under goal `g` — the worlds matching on the
QUD-relevant feature. -/
def qudClass (g : Goal) (w : World) : Finset World :=
  (Finset.univ : Finset World).filter (fun w' => project w' g = project w g)

theorem self_mem_qudClass (g : Goal) (w : World) : w ∈ qudClass g w := by
  simp [qudClass]

/-- Sum of meaning over the QUD-equivalence class — the input to S1's rpow. -/
noncomputable def projectedMeaning (g : Goal) (u : Cat) (w : World) : ℝ≥0∞ :=
  (qudClass g w).sum (fun w' => meaningE u w')

/-- Coverage at the projection level: at least one term in the sum is positive. -/
theorem projectedMeaning_self_ne_zero (g : Goal) (w : World) :
    projectedMeaning g w.1 w ≠ 0 := by
  refine fun h => meaningE_self_ne_zero w ?_
  have hle : meaningE w.1 w ≤ projectedMeaning g w.1 w :=
    Finset.single_le_sum (f := fun w' => meaningE w.1 w')
      (fun _ _ => zero_le _) (self_mem_qudClass g w)
  exact le_antisymm (h ▸ hle) (zero_le _)

/-! ## §5. Speaker (Eq. 5 of @cite{kao-etal-2014-hyperbole}, no cost)

Goal-conditioned speaker `S1(u | g, w) ∝ projectedMeaning(g, u, w)^α`.
With `α > 0` the rpow preserves the positivity witness, so both
hypotheses to `PMF.normalize` are derivable from `projectedMeaning_self_ne_zero`. -/

theorem projectedMeaning_rpow_tsum_ne_zero {α : ℝ} (hα : 0 < α) (g : Goal) (w : World) :
    ∑' u, projectedMeaning g u w ^ α ≠ 0 := by
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨w.1, ?_⟩
  exact (not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)).mpr (projectedMeaning_self_ne_zero g w)

theorem meaningE_ne_top (u : Cat) (w : World) : meaningE u w ≠ ∞ := by
  unfold meaningE; split
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

theorem projectedMeaning_ne_top (g : Goal) (u : Cat) (w : World) :
    projectedMeaning g u w ≠ ∞ :=
  ENNReal.sum_ne_top.mpr fun w' _ => meaningE_ne_top u w'

theorem projectedMeaning_rpow_tsum_ne_top {α : ℝ} (hα : 0 ≤ α) (g : Goal) (w : World) :
    ∑' u, projectedMeaning g u w ^ α ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u =>
    ENNReal.rpow_ne_top_of_nonneg hα (projectedMeaning_ne_top g u w)

/-- Goal-conditioned speaker as a PMF (one normalisation per `(g, w)`). -/
noncomputable def S1g (α : ℝ) (hα : 0 < α) (g : Goal) (w : World) : PMF Cat :=
  PMF.normalize (fun u => projectedMeaning g u w ^ α)
    (projectedMeaning_rpow_tsum_ne_zero hα g w)
    (projectedMeaning_rpow_tsum_ne_top hα.le g w)

theorem mem_support_S1g_iff {α : ℝ} (hα : 0 < α) (g : Goal) (w : World) (u : Cat) :
    u ∈ (S1g α hα g w).support ↔ projectedMeaning g u w ≠ 0 := by
  rw [S1g, PMF.mem_support_normalize_iff]
  exact not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)

/-! ## §6. Goal-marginalised speaker via `PMF.bind` -/

/-- Marginalised speaker: bind `S1g` over the goal prior. The kernel input
to L1 is `marginalSpeaker w u = Σ_g goalPrior(g) · S1g(u | g, w)` — exactly
`goalPrior.bind (fun g => S1g α hα g w)`. -/
noncomputable def marginalSpeaker (α : ℝ) (hα : 0 < α) (goalPrior : PMF Goal)
    (w : World) : PMF Cat :=
  goalPrior.bind (fun g => S1g α hα g w)

theorem marginalSpeaker_self_ne_zero {α : ℝ} (hα : 0 < α)
    {goalPrior : PMF Goal} {g : Goal} (hg : goalPrior g ≠ 0) (w : World) :
    marginalSpeaker α hα goalPrior w w.1 ≠ 0 := by
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨g, mul_ne_zero hg ?_⟩
  rw [← PMF.mem_support_iff, mem_support_S1g_iff]
  exact projectedMeaning_self_ne_zero g w

/-! ## §7. World prior as PMF -/

theorem worldPriorRaw_tsum_ne_zero : ∑' w, worldPriorRaw w ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr
    ⟨(.whale, true, true, true), by
      unfold worldPriorRaw catPriorE
      exact mul_ne_zero one_ne_zero (featurePriorE_pos _ _ _ _)⟩

theorem worldPriorRaw_tsum_ne_top : ∑' w, worldPriorRaw w ≠ ∞ := by
  refine ENNReal.tsum_ne_top_of_fintype fun w => ?_
  unfold worldPriorRaw catPriorE
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  cases w.1 <;> simp

noncomputable def worldPrior : PMF World :=
  PMF.normalize worldPriorRaw worldPriorRaw_tsum_ne_zero worldPriorRaw_tsum_ne_top

theorem worldPrior_ne_zero (w : World) : worldPrior w ≠ 0 := by
  rw [worldPrior, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]
  unfold worldPriorRaw catPriorE
  refine mul_ne_zero ?_ (featurePriorE_pos _ _ _ _)
  cases w.1 <;> simp

/-! ## §8. L1 — Bayesian inversion -/

theorem L1_marginal_ne_zero {α : ℝ} (hα : 0 < α)
    {goalPrior : PMF Goal} {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat) :
    PMF.marginal (marginalSpeaker α hα goalPrior) worldPrior u ≠ 0 := by
  -- Witness: pick any world with `u = w.1`. For `u = .whale`, take `(.whale, …)`;
  -- for `u = .person`, take `(.person, …)`.
  refine PMF.marginal_ne_zero _ worldPrior u
    (worldPrior_ne_zero (u, true, true, true)) ?_
  -- `marginalSpeaker` at world `(u, …)` is nonzero on `u` because `u = w.1`.
  have h := marginalSpeaker_self_ne_zero hα hg (u, true, true, true)
  exact h

/-- Pragmatic listener: `PMF.posterior` of the goal-marginalised speaker
against the world prior. The "L1 = Bayesian inversion" claim is true by
construction. -/
noncomputable def L1 {α : ℝ} (hα : 0 < α)
    {goalPrior : PMF Goal} {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat) : PMF World :=
  PMF.posterior (marginalSpeaker α hα goalPrior) worldPrior u
    (L1_marginal_ne_zero hα hg u)

end Phenomena.Nonliteral.Metaphor.KaoEtAl2014.PMF
