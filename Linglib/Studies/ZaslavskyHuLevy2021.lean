module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Pragmatics.RSA.Basic

/-!
# Zaslavsky, Hu and Levy (2021): A Rate–Distortion View of Human Pragmatic Reasoning?

Zaslavsky, Hu and Levy show that the Rational Speech Act recursion is an alternating maximization.
A reference game has finitely many meanings and utterances, a prior over the meanings, a lexicon
and a cost on the utterances. A speaker is a kernel from meanings to utterances and a listener a
kernel back. The tradeoff of a speaker and a listener (`tradeoff`) is the speaker's conditional
entropy plus `α` times the expected utility, the listener's log-probability of the speaker's
meaning less the cost of her utterance. Against a fixed listener the RSA speaker maximizes the
tradeoff, and against a fixed speaker the Bayesian listener does, so the tradeoff never decreases
along the recursion.

## Main statements

* `tradeoff_add_sum_klDiv`, `tradeoff_le_tradeoff_speaker`: against a fixed listener the
  tradeoff of a speaker falls short of the RSA speaker's by her expected divergence from it.
* `expectedUtility_le_pragmaticListener`, `tradeoff_le_tradeoff_pragmaticListener`: against a
  fixed speaker the Bayesian listener maximizes the expected utility, and so the tradeoff.
* `tradeoff_le_tradeoff_listener_succ`, `tradeoff_le_tradeoff_speaker_succ`,
  `exists_tendsto_tradeoff`: along the recursion each listener update and each speaker update
  raises the tradeoff, which therefore converges.
* `listener_apply_singleton_eq_zero`, `speaker_apply_singleton_eq_zero`: no agent of the
  recursion pairs an utterance with a meaning the lexicon rules out for it.

## Implementation notes

* The utility is real-valued, with `Real.log 0 = 0`, where the paper's is `−∞` at a meaning the
  listener rules out. The two agree for a speaker who uses no utterance at a meaning its listener
  rules out, and the optimality statements quantify over such speakers and listeners; the paper
  maximizes over all of them, which adds only competitors whose tradeoff is `−∞`.
* The speaker's step is Gibbs' variational identity for a weight kernel, and the listener's step
  the Bayesian-decoder inequality of the channel-capacity file with the speaker as the channel.
* `speaker t` answers `listener t`, so it is the paper's speaker of depth `t + 1`. The recursion
  assumes a prior that charges every meaning and a finite lexicon in which every meaning has an
  applicable utterance and every utterance applies to some meaning, so that every agent is a
  probability kernel. The lexicon is any such weight and the cost any real function, where the
  paper's lexicon has values in the unit interval and its cost is nonnegative.
* The lexicon statements need `0 < α`, where the paper has `0 ≤ α`. At `α = 0` the speaker
  here is uniform over all the utterances, since `0 ^ 0 = 1`.

## TODO

* The fixed points of the recursion are stationary points of the tradeoff, and the limit of the
  tradeoff along the recursion is its value at one.
* The rate–distortion variant, whose tradeoff has mutual information in place of the conditional
  entropy, with its update equations.
* The asymptotic behaviour of the recursion and the criticality of `α = 1`.

## References

* [zaslavsky-hu-levy-2020]
* [frank-goodman-2012]
-/

@[expose] public section

namespace ZaslavskyHuLevy2021

open MeasureTheory ProbabilityTheory InformationTheory Real Filter Topology
open scoped ENNReal

variable {M U : Type*} [MeasurableSpace M] [MeasurableSpace U] [Fintype M] [Fintype U]
  [MeasurableSingletonClass M] [MeasurableSingletonClass U] (P : Measure M) (C : U → ℝ) (α : ℝ)

/-- The expected utility `𝔼_S[V_L]` of (4) averages the utility `V_L(m, u) = log L(m | u) − C(u)`
of (1) over the meanings and the speaker's utterances. -/
noncomputable def expectedUtility (S : Kernel M U) (L : Kernel U M) : ℝ :=
  ∑ m, P.real {m} * ∫ u, (log ((L u).real {m}) - C u) ∂(S m)

/-- The RSA tradeoff `𝒢_α[S, L]` of (6) is the speaker's conditional entropy `H_S(U | M)` of (5)
plus `α` times the expected utility. -/
noncomputable def tradeoff (S : Kernel M U) (L : Kernel U M) : ℝ :=
  ∑ m, P.real {m} * Hm[S m] + α * expectedUtility P C S L

/-- The tradeoff is bounded above, by the log of the number of utterances when there is no
cost. -/
theorem tradeoff_le [IsProbabilityMeasure P] {α : ℝ} (hα : 0 ≤ α) (S : Kernel M U)
    [IsMarkovKernel S] (L : Kernel U M) [IsMarkovKernel L] :
    tradeoff P C α S L ≤ log (Fintype.card U) + α * ∑ u, |C u| := by
  have hV (m : M) : ∫ u, (log ((L u).real {m}) - C u) ∂(S m) ≤ ∑ u, |C u| :=
    calc ∫ u, (log ((L u).real {m}) - C u) ∂(S m)
      _ ≤ ∫ _, ∑ u, |C u| ∂(S m) := integral_mono .of_finite .of_finite fun u ↦ by
          have := Finset.single_le_sum (fun v _ ↦ abs_nonneg (C v)) (Finset.mem_univ u)
          have := log_nonpos measureReal_nonneg (measureReal_le_one (μ := L u) (s := {m}))
          have := neg_abs_le (C u)
          beta_reduce
          linarith
      _ = ∑ u, |C u| := by simp
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hα)
  · calc ∑ m, P.real {m} * Hm[S m]
      _ ≤ ∑ m, P.real {m} * log (Fintype.card U) := Finset.sum_le_sum fun m _ ↦
          mul_le_mul_of_nonneg_left (measureEntropy_le_log_card _) measureReal_nonneg
      _ = log (Fintype.card U) := by
          rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]
  · calc expectedUtility P C S L
      _ ≤ ∑ m, P.real {m} * ∑ u, |C u| := Finset.sum_le_sum fun m _ ↦
          mul_le_mul_of_nonneg_left (hV m) measureReal_nonneg
      _ = ∑ u, |C u| := by rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

/-! ### The speaker's step -/

private theorem log_toReal_rpow {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx : x ≠ ∞) :
    log (x ^ α).toReal = α * log x.toReal := by
  rcases eq_or_ne x 0 with rfl | h0
  · rcases hα.eq_or_lt with rfl | h
    · simp
    · simp [ENNReal.zero_rpow_of_pos h]
  · rw [← ENNReal.toReal_rpow, Real.log_rpow (ENNReal.toReal_pos h0 hx)]

section Speaker

variable {α} (hα : 0 ≤ α) (L : Kernel U M) [IsFiniteKernel L]
include hα

/-- Gibbs' variational identity for the speaker at a meaning. The entropy of a distribution over
utterances plus `α` times its expected utility falls short of the log partition function by its
divergence from the speaker's row. -/
theorem measureEntropy_add_utility_add_klDiv (m : M) (q : Measure U) [IsProbabilityMeasure q]
    (hq : q ≪ RSA.speaker α C L Measure.dirac m) :
    Hm[q] + α * ∫ u, (log ((L u).real {m}) - C u) ∂q +
        (klDiv q (RSA.speaker α C L Measure.dirac m)).toReal =
      log (∑ u, (L u {m} ^ α).toReal * exp (-(α * C u))) := by
  rw [RSA.speaker_dirac_eq_ofWeights] at hq ⊢
  have hw (u : U) : L u {m} ^ α ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα (measure_ne_top _ _)
  have hterm (u : U) :
      q.real {u} * log (L u {m} ^ α * ENNReal.ofReal (exp (-(α * C u)))).toReal =
        α * (q.real {u} * (log ((L u).real {m}) - C u)) := by
    rcases eq_or_ne (q {u}) 0 with h | h
    · rw [measureReal_def, h, ENNReal.toReal_zero, zero_mul, zero_mul, mul_zero]
    · have h0 : (L u {m} ^ α).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨left_ne_zero_of_mul
        fun h0 ↦ h (hq (Kernel.ofWeights_apply_singleton_eq_zero h0)), hw u⟩
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le, log_mul h0 (exp_ne_zero _),
        log_exp, log_toReal_rpow hα (measure_ne_top _ _), measureReal_def (L u)]
      ring
  have key := toReal_klDiv_ofWeights_add_measureEntropy
    (w := fun m u ↦ L u {m} ^ α * ENNReal.ofReal (exp (-(α * C u)))) (i := m)
    (fun u ↦ ENNReal.mul_ne_top (hw u) ENNReal.ofReal_ne_top) hq
  simp only [hterm, ← Finset.mul_sum] at key
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at key
  rw [integral_fintype .of_finite]
  simp_rw [smul_eq_mul]
  linarith

/-- Against a fixed listener, the tradeoff of a speaker and her expected divergence from the RSA
speaker add up to the expected log partition function. -/
theorem tradeoff_add_sum_klDiv (S : Kernel M U) [IsMarkovKernel S]
    (hS : ∀ m, S m ≪ RSA.speaker α C L Measure.dirac m) :
    tradeoff P C α S L +
        ∑ m, P.real {m} * (klDiv (S m) (RSA.speaker α C L Measure.dirac m)).toReal =
      ∑ m, P.real {m} * log (∑ u, (L u {m} ^ α).toReal * exp (-(α * C u))) := by
  simp_rw [← measureEntropy_add_utility_add_klDiv C hα L _ (S _) (hS _)]
  rw [tradeoff, expectedUtility, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ ↦ by ring

/-- Against a fixed listener the RSA speaker maximizes the tradeoff (7). -/
theorem tradeoff_le_tradeoff_speaker (hL : ∀ m, ∃ u, L u {m} ≠ 0) (S : Kernel M U)
    [IsMarkovKernel S] (hS : ∀ m, S m ≪ RSA.speaker α C L Measure.dirac m) :
    tradeoff P C α S L ≤ tradeoff P C α (RSA.speaker α C L Measure.dirac) L := by
  have := RSA.isMarkovKernel_speaker_dirac hα C L hL
  have h := tradeoff_add_sum_klDiv P C hα L S hS
  have h' := tradeoff_add_sum_klDiv P C hα L (RSA.speaker α C L Measure.dirac)
    fun _ ↦ Measure.AbsolutelyContinuous.rfl
  simp only [klDiv_self, ENNReal.toReal_zero, mul_zero, Finset.sum_const_zero, add_zero] at h'
  have hnonneg : 0 ≤ ∑ m, P.real {m} *
      (klDiv (S m) (RSA.speaker α C L Measure.dirac m)).toReal :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg
  linarith

end Speaker

/-! ### The listener's step -/

section Listener

variable [Nonempty M] [IsProbabilityMeasure P] (S : Kernel M U) [IsMarkovKernel S]
  (L : Kernel U M) [IsMarkovKernel L] (hL : ∀ u, (S ∘ₘ P) {u} ≠ 0 → (S†P) u ≪ L u)
include hL

/-- Against a fixed speaker the Bayesian listener maximizes the expected utility (12). -/
theorem expectedUtility_le_pragmaticListener :
    expectedUtility P C S L ≤ expectedUtility P C S (RSA.pragmaticListener S P) := by
  have h := sum_mul_integral_log_le S P L hL
  simp_rw [expectedUtility, integral_sub (.of_finite) (.of_finite), mul_sub,
    Finset.sum_sub_distrib]
  exact sub_le_sub_right h _

/-- Against a fixed speaker the Bayesian listener maximizes the tradeoff (8). -/
theorem tradeoff_le_tradeoff_pragmaticListener (hα : 0 ≤ α) :
    tradeoff P C α S L ≤ tradeoff P C α S (RSA.pragmaticListener S P) :=
  add_le_add_right
    (mul_le_mul_of_nonneg_left (expectedUtility_le_pragmaticListener P C S L hL) hα) _

end Listener

/-! ### The recursion -/

section Recursion

variable [Nonempty M] [IsProbabilityMeasure P] (l : U → M → ℝ≥0∞)

/-- The listeners of the recursion (3) start from the literal listener
`L₀(m | u) ∝ l(m, u) P(m)`, and each later one is the Bayesian inverse of the speaker answering
the one before. -/
noncomputable def listener : ℕ → Kernel U M
  | 0 => RSA.gradedListener P l
  | t + 1 => RSA.pragmaticListener (RSA.speaker α C (listener t) Measure.dirac) P

/-- The speaker of the recursion (2) answers `listener t`, so it is the paper's `S_{t+1}`. -/
noncomputable def speaker (t : ℕ) : Kernel M U :=
  RSA.speaker α C (listener P C α l t) Measure.dirac

instance : ∀ t, IsFiniteKernel (listener P C α l t)
  | 0 => inferInstanceAs (IsFiniteKernel (RSA.gradedListener P l))
  | _ + 1 => inferInstanceAs (IsFiniteKernel (RSA.pragmaticListener _ P))

variable {P C α l} (hP : ∀ m, P {m} ≠ 0) (hl : ∀ u m, l u m ≠ ∞) {u : U} {m : M}
include hP hl

/-- Every listener of the recursion is a probability kernel when every utterance applies to some
meaning. -/
theorem isMarkovKernel_listener (hu : ∀ u, ∃ m, l u m ≠ 0) :
    ∀ t, IsMarkovKernel (listener P C α l t)
  | 0 => ⟨fun u ↦ RSA.isProbabilityMeasure_gradedListener P l u
      (by
        obtain ⟨m, hm⟩ := hu u
        rw [lintegral_fintype]
        exact fun h ↦ mul_ne_zero hm (hP m) (Finset.sum_eq_zero_iff.1 h m (Finset.mem_univ m)))
      (by
        rw [lintegral_fintype]
        exact ENNReal.sum_ne_top.2 fun m _ ↦ ENNReal.mul_ne_top (hl u m) (measure_ne_top _ _))⟩
  | _ + 1 => inferInstanceAs (IsMarkovKernel (RSA.pragmaticListener _ P))

/-- No listener of the recursion rules out a meaning the utterance applies to. -/
theorem listener_apply_singleton_ne_zero (hα : 0 ≤ α) (h : l u m ≠ 0) :
    ∀ t, listener P C α l t u {m} ≠ 0
  | 0 => by
    rw [listener, RSA.gradedListener_apply_singleton]
    exact ENNReal.div_ne_zero.2 ⟨mul_ne_zero h (hP m), ENNReal.sum_ne_top.2 fun m' _ ↦
      ENNReal.mul_ne_top (hl u m') (measure_ne_top _ _)⟩
  | t + 1 => by
    have hS : RSA.speaker α C (listener P C α l t) Measure.dirac m {u} ≠ 0 :=
      RSA.speaker_dirac_apply_singleton_ne_zero hα (listener_apply_singleton_ne_zero hα h t)
    exact (RSA.pragmaticListener_apply_singleton_ne_zero_iff
      (comp_apply_singleton_ne_zero _ _ (hP m) hS) m).2 ⟨hP m, hS⟩

/-- The listeners of the recursion respect the lexicon. An utterance never leads the listener to
a meaning it does not apply to. -/
theorem listener_apply_singleton_eq_zero (hα : 0 < α) (hu : ∀ u, ∃ m, l u m ≠ 0)
    (h : l u m = 0) : ∀ t, listener P C α l t u {m} = 0
  | 0 => by rw [listener, RSA.gradedListener_apply_singleton, h, zero_mul, ENNReal.zero_div]
  | t + 1 => by
    obtain ⟨m', hm'⟩ := hu u
    exact RSA.pragmaticListener_apply_singleton_eq_zero
      (comp_apply_singleton_ne_zero _ _ (hP m') (RSA.speaker_dirac_apply_singleton_ne_zero hα.le
        (listener_apply_singleton_ne_zero hP hl hα.le hm' t)))
      (RSA.speaker_dirac_apply_singleton_eq_zero hα (listener_apply_singleton_eq_zero hα hu h t))

/-- The speakers of the recursion respect the lexicon. No meaning is expressed by an utterance
that does not apply to it. -/
theorem speaker_apply_singleton_eq_zero (hα : 0 < α) (hu : ∀ u, ∃ m, l u m ≠ 0)
    (h : l u m = 0) (t : ℕ) : speaker P C α l t m {u} = 0 :=
  RSA.speaker_dirac_apply_singleton_eq_zero hα (listener_apply_singleton_eq_zero hP hl hα hu h t)

variable (hα : 0 ≤ α) (hm : ∀ m, ∃ u, l u m ≠ 0)
include hα hm

/-- Every speaker of the recursion is a probability kernel. -/
theorem isMarkovKernel_speaker (t : ℕ) : IsMarkovKernel (speaker P C α l t) :=
  RSA.isMarkovKernel_speaker_dirac hα C _ fun m ↦
    (hm m).imp fun _ h ↦ listener_apply_singleton_ne_zero hP hl hα h t

/-- Each speaker update raises the tradeoff, the second inequality of (9). -/
theorem tradeoff_le_tradeoff_speaker_succ (t : ℕ) :
    tradeoff P C α (speaker P C α l t) (listener P C α l (t + 1)) ≤
      tradeoff P C α (speaker P C α l (t + 1)) (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker (C := C) hP hl hα hm t
  refine tradeoff_le_tradeoff_speaker P C hα _
    (fun m ↦ (hm m).imp fun _ h ↦ listener_apply_singleton_ne_zero hP hl hα h (t + 1)) _ fun m ↦
    Measure.absolutelyContinuous_of_forall_singleton fun u hu ↦ of_not_not fun hS ↦ ?_
  exact RSA.speaker_dirac_apply_singleton_ne_zero hα
    ((RSA.pragmaticListener_apply_singleton_ne_zero_iff
      (comp_apply_singleton_ne_zero _ _ (hP m) hS) m).2 ⟨hP m, hS⟩) hu

variable (hu : ∀ u, ∃ m, l u m ≠ 0)
include hu

/-- Each listener update raises the tradeoff, the first inequality of (9). -/
theorem tradeoff_le_tradeoff_listener_succ (t : ℕ) :
    tradeoff P C α (speaker P C α l t) (listener P C α l t) ≤
      tradeoff P C α (speaker P C α l t) (listener P C α l (t + 1)) := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp [tradeoff]
  have := isMarkovKernel_speaker (C := C) hP hl hα hm t
  have := isMarkovKernel_listener (C := C) (α := α) hP hl hu t
  refine tradeoff_le_tradeoff_pragmaticListener P C α _ _ (fun u hu' ↦
    Measure.absolutelyContinuous_of_forall_singleton fun m hL ↦ of_not_not fun hpost ↦ ?_) hα
  exact ((posterior_apply_singleton_ne_zero_iff _ _ hu' m).1 hpost).2
    (RSA.speaker_dirac_apply_singleton_eq_zero hα' hL)

/-- The tradeoff converges along the recursion, being monotone and bounded above. -/
theorem exists_tendsto_tradeoff : ∃ g,
    Tendsto (fun t ↦ tradeoff P C α (speaker P C α l t) (listener P C α l t)) atTop (𝓝 g) := by
  refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun t ↦
    (tradeoff_le_tradeoff_listener_succ hP hl hα hm hu t).trans
      (tradeoff_le_tradeoff_speaker_succ hP hl hα hm t))
    ⟨log (Fintype.card U) + α * ∑ u, |C u|, ?_⟩⟩
  rintro _ ⟨t, rfl⟩
  have := isMarkovKernel_speaker (C := C) hP hl hα hm t
  have := isMarkovKernel_listener (C := C) (α := α) hP hl hu t
  exact tradeoff_le P C hα _ _

end Recursion

end ZaslavskyHuLevy2021
