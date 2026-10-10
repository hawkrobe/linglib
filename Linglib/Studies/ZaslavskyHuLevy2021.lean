module

public import Linglib.Pragmatics.RSA.Tradeoff

/-!
# Zaslavsky, Hu and Levy (2021): A Rate–Distortion View of Human Pragmatic Reasoning?

Zaslavsky, Hu and Levy show that the Rational Speech Act recursion is an alternating maximization.
A reference game has finitely many meanings and utterances, a prior over the meanings, a lexicon
and a cost on the utterances. A speaker is a kernel from meanings to utterances and a listener a
kernel back. The tradeoff of a speaker and a listener is the speaker's conditional entropy plus
`α` times the expected utility, the listener's log-probability of the speaker's meaning less the
cost of her utterance. Against a fixed listener the RSA speaker maximizes the tradeoff, and
against a fixed speaker the Bayesian listener does, so the tradeoff never decreases along the
recursion.

## Main statements

* `tradeoff_le_tradeoff_speaker`, `tradeoff_le_tradeoff_pragmaticListener`: against a fixed
  listener the RSA speaker maximizes the tradeoff, and against a fixed speaker the Bayesian
  listener does.
* `tradeoff_le_tradeoff_listener_succ`, `tradeoff_le_tradeoff_speaker_succ`,
  `exists_tendsto_tradeoff`: along the recursion each listener update and each speaker update
  raises the tradeoff, which therefore converges.
* `listener_apply_singleton_eq_zero`, `speaker_listener_apply_singleton_eq_zero`: no agent of the
  recursion pairs an utterance with a meaning the lexicon rules out for it.

## Implementation notes

* The paper's speaker knows the meaning, so its tradeoff is `RSA.tradeoff` at the identity
  observation kernel, which `RSA.tradeoff_id` writes as the paper does, and its speaker believes
  the point mass. The two maximality statements are cases of the ones in the tradeoff file, whose
  notes say how the real-valued utility there relates to the paper's.
* `listener t` is the paper's listener of depth `t`, and the speaker who answers it is the
  paper's speaker of depth `t + 1`. The recursion assumes a prior that charges every meaning and
  a finite lexicon in which every meaning has an applicable utterance and every utterance applies
  to some meaning, so that every agent is a probability kernel. The lexicon is any such weight
  and the cost any real function, where the paper's lexicon has values in the unit interval and
  its cost is nonnegative.
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

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

variable {M U : Type*} [MeasurableSpace M] [MeasurableSpace U] [Fintype M] [Fintype U]
  [MeasurableSingletonClass M] [MeasurableSingletonClass U] (P : Measure M) (C : U → ℝ) (α : ℝ)

/-! ### The two steps -/

/-- Against a fixed listener the RSA speaker maximizes the tradeoff (7). -/
theorem tradeoff_le_tradeoff_speaker [IsFiniteMeasure P] {α : ℝ} (hα : 0 ≤ α) (L : Kernel U M)
    [IsFiniteKernel L] (S : Kernel M U) [IsMarkovKernel S]
    (hS : ∀ m, P {m} ≠ 0 → S m ≪ RSA.speaker α C L Measure.dirac m) :
    RSA.tradeoff P Kernel.id C α S L ≤
      RSA.tradeoff P Kernel.id C α (RSA.speaker α C L Measure.dirac) L :=
  RSA.tradeoff_le_tradeoff_speaker (RSA.id_comp_real_mul_dirac_real P) hα L S
    (by simpa only [Measure.id_comp] using hS)

section Listener

variable [Nonempty M] [IsProbabilityMeasure P] (S : Kernel M U) [IsMarkovKernel S]
  (L : Kernel U M) [IsMarkovKernel L] (hL : ∀ u, (S ∘ₘ P) {u} ≠ 0 → (S†P) u ≪ L u)
include hL

/-- Against a fixed speaker the Bayesian listener maximizes the expected utility (12). -/
theorem expectedUtility_le_pragmaticListener :
    RSA.expectedUtility P Kernel.id C S L ≤
      RSA.expectedUtility P Kernel.id C S (RSA.pragmaticListener S P) := by
  have h := RSA.expectedUtility_le_pragmaticListener P Kernel.id C S L
    (by simpa only [Kernel.comp_id] using hL)
  simp only [Kernel.comp_id] at h
  exact h

/-- Against a fixed speaker the Bayesian listener maximizes the tradeoff (8). -/
theorem tradeoff_le_tradeoff_pragmaticListener (hα : 0 ≤ α) :
    RSA.tradeoff P Kernel.id C α S L ≤
      RSA.tradeoff P Kernel.id C α S (RSA.pragmaticListener S P) := by
  have h := RSA.tradeoff_le_tradeoff_pragmaticListener P Kernel.id C α S L
    (by simpa only [Kernel.comp_id] using hL) hα
  simp only [Kernel.comp_id] at h
  exact h

end Listener

/-! ### The recursion -/

section Recursion

variable [Nonempty M] [IsProbabilityMeasure P] (l : U → M → ℝ≥0∞)

/-- The listeners of the recursion (3) start from the literal listener
`L₀(m | u) ∝ l(m, u) P(m)`, and each later one is the Bayesian inverse of the speaker (2) who
answers the one before. -/
noncomputable def listener : ℕ → Kernel U M
  | 0 => RSA.gradedListener P l
  | t + 1 => RSA.pragmaticListener (RSA.speaker α C (listener t) Measure.dirac) P

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
theorem speaker_listener_apply_singleton_eq_zero (hα : 0 < α) (hu : ∀ u, ∃ m, l u m ≠ 0)
    (h : l u m = 0) (t : ℕ) : RSA.speaker α C (listener P C α l t) Measure.dirac m {u} = 0 :=
  RSA.speaker_dirac_apply_singleton_eq_zero hα (listener_apply_singleton_eq_zero hP hl hα hu h t)

variable (hα : 0 ≤ α) (hm : ∀ m, ∃ u, l u m ≠ 0)
include hα hm

/-- Every speaker of the recursion is a probability kernel. -/
theorem isMarkovKernel_speaker_listener (t : ℕ) :
    IsMarkovKernel (RSA.speaker α C (listener P C α l t) Measure.dirac) :=
  RSA.isMarkovKernel_speaker_dirac hα C _ fun m ↦
    (hm m).imp fun _ h ↦ listener_apply_singleton_ne_zero hP hl hα h t

/-- Each speaker update raises the tradeoff, the second inequality of (9). -/
theorem tradeoff_le_tradeoff_speaker_succ (t : ℕ) :
    RSA.tradeoff P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) ≤
      RSA.tradeoff P Kernel.id C α (RSA.speaker α C (listener P C α l (t + 1)) Measure.dirac)
        (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  have h := RSA.tradeoff_pragmaticListener_le_tradeoff_speaker (C := C)
    (RSA.id_comp_real_mul_dirac_real P) hα (RSA.speaker α C (listener P C α l t) Measure.dirac)
  simp only [Kernel.comp_id] at h
  exact h

variable (hu : ∀ u, ∃ m, l u m ≠ 0)
include hu

/-- Each listener update raises the tradeoff, the first inequality of (9). -/
theorem tradeoff_le_tradeoff_listener_succ (t : ℕ) :
    RSA.tradeoff P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l t) ≤
      RSA.tradeoff P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  have := isMarkovKernel_listener (C := C) (α := α) hP hl hu t
  have h := RSA.tradeoff_speaker_le_tradeoff_pragmaticListener (C := C)
    (RSA.id_comp_real_mul_dirac_real P) hα (listener P C α l t)
  simp only [Kernel.comp_id] at h
  exact h

/-- The tradeoff converges along the recursion, being monotone and bounded above. -/
theorem exists_tendsto_tradeoff : ∃ g, Tendsto (fun t ↦ RSA.tradeoff P Kernel.id C α
    (RSA.speaker α C (listener P C α l t) Measure.dirac) (listener P C α l t)) atTop (𝓝 g) := by
  refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun t ↦
    (tradeoff_le_tradeoff_listener_succ hP hl hα hm hu t).trans
      (tradeoff_le_tradeoff_speaker_succ hP hl hα hm t))
    ⟨log (Fintype.card U) + α * ∑ u, |C u|, ?_⟩⟩
  rintro _ ⟨t, rfl⟩
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  have := isMarkovKernel_listener (C := C) (α := α) hP hl hu t
  exact RSA.tradeoff_le P Kernel.id C hα _ _

end Recursion

end ZaslavskyHuLevy2021
