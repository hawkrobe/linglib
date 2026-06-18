import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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
`klDiv`) characterization is the Gibbs / Donsker–Varadhan variational principle in
`Core/Probability/GibbsVariational.lean`, applied here via `speaker_isGreatest`.

## Main statements

* `speaker_count_singleton` / `speaker_countRestrict_singleton` — closed form of
  the speaker mass at an utterance (softmax over the base / over the applicable set
  `A`); `speaker_countRestrict_singleton_of_not_mem` gives `0` off `A`.
* `speaker_count_lt_iff_score_lt` / `speaker_lt_iff_score_lt` /
  `speaker_countRestrict_lt_iff_score_lt` — **monotonicity in informativity**: the
  speaker prefers `b` over `a` iff its utility is higher. The partition function
  cancels; reduces to strict monotonicity of `Real.exp`.
* `listener` / `listener_comp_speaker_marginal` / `listener_region` — the pragmatic
  listener as the Bayesian posterior `S1 † prior`, stated measure-natively.
* `speaker_isGreatest` — the RSA speaker is the **rational optimizer** (Gibbs /
  Donsker–Varadhan variational principle).
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

/-- **Speaker monotonicity, general probability/finite base**: for any finite
base measure that assigns equal nonzero mass to the two utterances, the speaker
prefers `b` over `a` iff `b` has the higher utility. Generalizes
`speaker_count_lt_iff_score_lt` off the counting base — the form the variational
principle needs, where the base is a *probability* measure (e.g.
`ProbabilityTheory.uniformOn`). The shared singleton mass and the partition
function `Z = ∫ y, exp (score y) ∂base` cancel, reducing to `Real.exp`
monotonicity.

An integrability hypothesis on `exp ∘ score` is required (and is automatic on a
`Fintype`): without it a non-integrable tilt collapses to the zero measure
(`MeasureTheory.tilted_of_not_integrable`), making both sides vanish and the
equivalence false. It mirrors the `h_exp` hypothesis of `speaker_isGreatest`. -/
theorem speaker_lt_iff_score_lt {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (base : Measure U) [IsFiniteMeasure base]
    (score : U → ℝ) (a b : U) (hmass : base {a} = base {b}) (hpos : base {a} ≠ 0)
    (hexp : Integrable (fun u => Real.exp (score u)) base) :
    speaker base score {a} < speaker base score {b} ↔ score a < score b := by
  have : NeZero base := ⟨fun h => hpos (by rw [h]; rfl)⟩
  have hZ : 0 < ∫ y, Real.exp (score y) ∂base := integral_exp_pos hexp
  have key : ∀ x : U, speaker base score {x}
      = ENNReal.ofReal (Real.exp (score x) / ∫ y, Real.exp (score y) ∂base) * base {x} := by
    intro x
    rw [speaker, tilted_apply, lintegral_singleton]
  rw [key a, key b, hmass,
    ENNReal.mul_lt_mul_iff_left (hmass ▸ hpos) (measure_ne_top base {b}),
    ENNReal.ofReal_lt_ofReal_iff (by positivity),
    div_lt_div_iff_of_pos_right hZ, Real.exp_lt_exp]

/-! ### Finite-support speaker (counting base restricted to the applicable set)

The faithful RSA speaker normalizes over only the utterances that *apply* to the
referent ([frank-goodman-2012]'s set `W` in eq. 2), not the whole utterance type.
Tilting `Measure.count` restricted to a finite applicable set `A` realizes this:
the closed form at an applicable utterance is the softmax over `A`, and a
non-applicable utterance gets mass `0`. -/

/-- **Finite-support speaker, closed form**: tilting `Measure.count` restricted to
a finite set `A` gives, at any `a ∈ A`, the softmax
`ofReal (exp (score a) / ∑ x ∈ A, exp (score x))` over `A`. With
`score u = log (1 / |u|)` this is [frank-goodman-2012]'s eq. (2). -/
theorem speaker_countRestrict_singleton [Fintype U] [DecidableEq U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (A : Finset U) (score : U → ℝ) (a : U) (ha : a ∈ A) :
    speaker (Measure.count.restrict (↑A : Set U)) score {a}
      = ENNReal.ofReal (Real.exp (score a) / ∑ x ∈ A, Real.exp (score x)) := by
  have hwt : ∀ x : U, (Measure.count.restrict (↑A : Set U)).real {x}
      = if x ∈ A then (1 : ℝ) else 0 := by
    intro x
    rw [Measure.real, Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : x ∈ A
    · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr hx)),
        Measure.count_singleton, if_pos hx, ENNReal.toReal_one]
    · rw [Set.singleton_inter_eq_empty.mpr (by simpa using hx), measure_empty,
        if_neg hx, ENNReal.toReal_zero]
  have hZ : ∫ x, Real.exp (score x) ∂(Measure.count.restrict (↑A : Set U))
      = ∑ x ∈ A, Real.exp (score x) := by
    rw [integral_fintype Integrable.of_finite]
    simp only [hwt, ite_smul, one_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
  have hsing : (Measure.count.restrict (↑A : Set U)) {a} = 1 := by
    rw [Measure.restrict_apply (measurableSet_singleton a),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr ha)),
      Measure.count_singleton]
  rw [speaker, tilted_apply, lintegral_singleton, hZ, hsing, mul_one]

/-- A non-applicable utterance (`a ∉ A`) gets zero speaker mass: the finite-support
speaker is supported exactly on the applicable set `A`. -/
theorem speaker_countRestrict_singleton_of_not_mem [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (A : Finset U) (score : U → ℝ) (a : U) (ha : a ∉ A) :
    speaker (Measure.count.restrict (↑A : Set U)) score {a} = 0 := by
  have hsing : (Measure.count.restrict (↑A : Set U)) {a} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton a),
      Set.singleton_inter_eq_empty.mpr (by simpa using ha), measure_empty]
  rw [speaker, tilted_apply, lintegral_singleton, hsing, mul_zero]

/-- **Finite-support speaker monotonicity**: among applicable utterances, the
speaker prefers `b` over `a` iff `b` has the higher utility. The softmax normalizer
over `A` cancels. A specialization of `speaker_lt_iff_score_lt` to the restricted
counting base, with the equal-mass and nonzero side conditions discharged. -/
theorem speaker_countRestrict_lt_iff_score_lt [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (A : Finset U) (score : U → ℝ) (a b : U)
    (ha : a ∈ A) (hb : b ∈ A) :
    speaker (Measure.count.restrict (↑A : Set U)) score {a}
        < speaker (Measure.count.restrict (↑A : Set U)) score {b}
      ↔ score a < score b := by
  have hone : ∀ {c : U}, c ∈ A → (Measure.count.restrict (↑A : Set U)) {c} = 1 := by
    intro c hc
    rw [Measure.restrict_apply (measurableSet_singleton c),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr hc)),
      Measure.count_singleton]
  exact speaker_lt_iff_score_lt _ score a b ((hone ha).trans (hone hb).symm)
    (by rw [hone ha]; exact one_ne_zero) Integrable.of_finite

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
