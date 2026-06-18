import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Posterior
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Linglib.Core.Probability.GibbsVariational

/-!
# The RSA speaker as a Gibbs (exponentially-tilted) measure
[frank-goodman-2012] [goodman-stuhlmuller-2013]

Layer 1 of the analytic theory of RSA (Measure/Kernel-native foundation). The
pragmatic speaker `S1(· | w)` is the **exponential tilting** of a base
utterance measure by the rationality-scaled utility
`score w u = α · (log L0(w | u) − cost u)`:

  `S1(· | w) = base.tilted (score w)`

i.e. the speaker is a **Gibbs measure** in mathlib's sense
(`MeasureTheory.Measure.tilted`). This grounds the RSA speaker in mathlib's
exponential-family machinery rather than a bespoke `PMF.normalize ∘ exp`
reimplementation, and is the object on which the variational (free-energy /
`klDiv`) characterization will be built (Layer 0 keystone, to follow).

## Main statements

* `speaker_count_singleton` — closed form of the speaker mass at an utterance,
  for the counting base: `ofReal (exp (score u) / ∑ u', exp (score u'))`.
* `speaker_count_lt_iff_score_lt` — **monotonicity in informativity**: the
  speaker prefers `u₂` over `u₁` iff its utility is higher. The partition
  function cancels; reduces to strict monotonicity of `Real.exp`.
-/

open MeasureTheory Real
open scoped ENNReal

namespace RSA.Gibbs

variable {U : Type*}

/-- The RSA pragmatic speaker as an exponentially-tilted (Gibbs) measure: the
base utterance measure tilted by the utility `score`. With `score u =
α · (log L0(w|u) − cost u)` this is `S1(· | w) ∝ L0(w|u)^α · exp(−α·cost)`. -/
noncomputable def speaker [MeasurableSpace U] (base : Measure U) (score : U → ℝ) :
    Measure U :=
  base.tilted score

/-- Closed form of the speaker mass at a single utterance, for the counting
base: `ofReal (exp (score u) / Z)` with partition `Z = ∑ u', exp (score u')`. -/
theorem speaker_count_singleton [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (score : U → ℝ) (a : U) :
    speaker (Measure.count : Measure U) score {a}
      = ENNReal.ofReal (Real.exp (score a) / ∑ u, Real.exp (score u)) := by
  rw [speaker, tilted_apply, lintegral_singleton, Measure.count_singleton, mul_one,
      integral_count]

/-- **Speaker monotonicity in informativity**: at a fixed world, the speaker
assigns more mass to `b` than to `a` iff `b` has the higher utility. The
partition function cancels exactly; the comparison reduces to the strict
monotonicity of `Real.exp`. The RSA "speaker prefers the more informative
utterance" fact, as a theorem about the Gibbs measure. -/
theorem speaker_count_lt_iff_score_lt [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (score : U → ℝ) (a b : U) :
    speaker (Measure.count : Measure U) score {a}
        < speaker (Measure.count : Measure U) score {b}
      ↔ score a < score b := by
  rw [speaker_count_singleton, speaker_count_singleton]
  have hZ : 0 < ∑ u, Real.exp (score u) :=
    Finset.sum_pos (fun u _ => Real.exp_pos _) ⟨a, Finset.mem_univ a⟩
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity),
      div_lt_div_iff_of_pos_right hZ, Real.exp_lt_exp]

/-! ### The pragmatic listener as a Bayesian posterior (measure-native)

The pragmatic listener `L1` is the **Bayesian posterior** of the speaker kernel
`S1 : Kernel World Utterance` against the world prior — mathlib's
`ProbabilityTheory.posterior`, `S1 † prior : Kernel Utterance World`. This is
the listener stated *measure-natively*: it is a kernel/measure, characterized by
Bayes-consistency rather than by pointwise singleton values, so it is uniform
across discrete and continuous distribution classes (where singletons are null
and a pointwise reading is unavailable). -/

open ProbabilityTheory

/-- The RSA pragmatic listener: the Bayesian posterior `S1 † prior` of the
speaker kernel against the world prior. -/
noncomputable def listener {W U : Type*} [MeasurableSpace W] [MeasurableSpace U]
    [StandardBorelSpace W] [Nonempty W]
    (S1 : Kernel W U) (prior : Measure W) [IsFiniteMeasure prior] [IsFiniteKernel S1] :
    Kernel U W :=
  S1 † prior

/-- **Listener–speaker consistency** (measure-native): averaging the listener
over the speaker's marginal of the prior recovers the prior,
`L1 ∘ₘ (S1 ∘ₘ prior) = prior`. The Bayesian-coherence identity for RSA, as an
equality of measures — no singletons, any distribution class. -/
theorem listener_comp_speaker_marginal {W U : Type*} [MeasurableSpace W]
    [MeasurableSpace U] [StandardBorelSpace W] [Nonempty W]
    (S1 : Kernel W U) (prior : Measure W) [IsFiniteMeasure prior] [IsMarkovKernel S1] :
    listener S1 prior ∘ₘ (S1 ∘ₘ prior) = prior := by
  unfold listener; exact posterior_comp_self

/-! ### Bayes' theorem and region inference (measure-native) -/

/-- **Bayes' theorem for the RSA listener**: for almost every utterance `u`, the
listener is the prior **reweighted by the per-world speaker likelihood-ratio**,
`L1 u = prior.withDensity (fun w ↦ (S1 w).rnDeriv (S1 ∘ₘ prior) u)`. The posterior
is the prior tilted by how diagnostic each world is for `u`. For countable worlds
the absolute-continuity side condition is automatic. -/
theorem listener_eq_withDensity {W U : Type*} [MeasurableSpace W] [MeasurableSpace U]
    [Countable W] [StandardBorelSpace W] [Nonempty W]
    (S1 : Kernel W U) (prior : Measure W) [IsFiniteMeasure prior] [IsFiniteKernel S1] :
    ∀ᵐ u ∂(S1 ∘ₘ prior),
      listener S1 prior u
        = prior.withDensity (fun w => (S1 w).rnDeriv (S1 ∘ₘ prior) u) := by
  unfold listener
  exact posterior_eq_withDensity_of_countable S1 prior

/-- **Region inference**: the listener's posterior mass on a set of worlds `A`
given utterance `u` is the integral of the speaker likelihood-ratio over `A`.
This is the measure-native quantity behind RSA "the listener infers `φ`" claims
(projection, exhaustivity = posterior mass on the relevant region of worlds) —
stated at the level of sets, where it is meaningful for any distribution class,
rather than at points. -/
theorem listener_region {W U : Type*} [MeasurableSpace W] [MeasurableSpace U]
    [Countable W] [StandardBorelSpace W] [Nonempty W]
    (S1 : Kernel W U) (prior : Measure W) [IsFiniteMeasure prior] [IsFiniteKernel S1]
    {A : Set W} (hA : MeasurableSet A) :
    ∀ᵐ u ∂(S1 ∘ₘ prior),
      listener S1 prior u A = ∫⁻ w in A, (S1 w).rnDeriv (S1 ∘ₘ prior) u ∂prior := by
  filter_upwards [listener_eq_withDensity S1 prior] with u hu
  rw [hu, withDensity_apply _ hA]

/-! ### The RSA speaker is the rational optimizer

`speaker base score = base.tilted score` is a Gibbs measure, so the
Gibbs / Donsker–Varadhan variational principle
(`MeasureTheory.isGreatest_logIntegralExp`, proved generically in
`Core/Probability/GibbsVariational.lean`) applies directly: among all candidate
distributions over utterances, the speaker is the one **maximizing expected
utility `𝔼_q[score]` minus the KL cost `KL(q ‖ base)` of departing from the
prior**, with optimal value the free energy `base.logIntegralExp score`. This
turns RSA's "rational speaker" from a stipulated softmax into a theorem. -/

open InformationTheory

/-- The RSA speaker is the **rational optimizer**: `speaker base score` attains
the greatest value of expected-utility-minus-KL-cost
`q ↦ 𝔼_q[score] − KL(q ‖ base)` over candidate utterance distributions, the
optimum being the free energy `base.logIntegralExp score`. A direct instance of
the Gibbs / Donsker–Varadhan variational principle
`MeasureTheory.isGreatest_logIntegralExp` at the tilt defining the speaker. -/
theorem speaker_isGreatest {U : Type*} [MeasurableSpace U] (base : Measure U)
    [IsProbabilityMeasure base] (score : U → ℝ)
    (h_int_f : Integrable score (speaker base score))
    (h_int_llr : Integrable (llr (speaker base score) base) (speaker base score))
    (h_exp : Integrable (fun u => Real.exp (score u)) base) :
    IsGreatest
      {x : ℝ | ∃ q : Measure U, IsProbabilityMeasure q ∧ q ≪ base ∧
        Integrable (llr q base) q ∧ Integrable score q ∧
        x = (∫ u, score u ∂q) - (klDiv q base).toReal}
      (base.logIntegralExp score) :=
  isGreatest_logIntegralExp base h_int_f h_int_llr h_exp

end RSA.Gibbs
