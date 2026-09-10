import Linglib.Core.Probability.Kernel.OfWeights
import Linglib.Core.Probability.Kernel.Posterior
import Linglib.Core.Probability.UniformOn
import Linglib.Pragmatics.RSA.Uniform
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Goodman and Stuhlmüller (2013): Knowledge and Implicature

This file formalizes [goodman-stuhlmuller-2013]'s rational speech-act model of scalar
implicature under a speaker with incomplete knowledge. The listener infers the state, how many
of three objects have a property, from the utterance and the speaker's access, the number of
objects she looked at, by inverting a speaker who softmax-optimizes the expected informativity
of her utterance under her belief, her posterior over states given what she observed. The
observation is hypergeometric (`obs`), the speaker's utility is the log-probability of the
literal listener (`obsSpeaker`), the listener marginalizes the observation she cannot see
(`speaker`) and applies Bayes' rule (`listener`). With complete access, *some* implicates
*not all* and a numeral its exact reading, for every rationality (`some_full`,
`numerals_full`); with access to one or two objects, the *some* implicature is canceled
(`some_partial`), *one* after one object and *two* after two carry no implicature
(`one_minimal`, `two_partial`), while *one* after two objects keeps the partial implicature
against three but not against two (`one_partial`), the fine-grained interaction the
experiments test.

## Implementation notes

The literal listener is uniform on an utterance's extension, so the expected log-probability
under the speaker's belief is `-log |⟦u⟧|` when the utterance holds at every state the
observation leaves possible, Quality, and `-∞` otherwise; `obsSpeaker` is the softmax of that
closed form, with weight `|⟦u⟧|^{-α}` or `0`. The alternatives are the paper's, *none*, *some*,
*all* and *one*, *two*, *three*, without a silent option: an observation compatible with no
utterance gives the zero row, which the marginal speaker simply loses. The prior is uniform, the
regime of the paper's expository predictions; its fitted binomial prior and its rationality
`3.4` only reshape the plotted magnitudes. Experiment results and the quantitative fit are prose.

## References

* [goodman-stuhlmuller-2013]
* [frank-goodman-2012]
* [horn-1972]
-/

namespace GoodmanStuhlmuller2013

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A world state: how many of the three objects have the property. -/
abbrev WorldState := Fin 4

/-- The speaker's access: how many of the three objects she looks at. -/
abbrev Access := Fin 4

/-- An observation: how many of the objects she looks at have the property. -/
abbrev Obs := Fin 4

/-! ### The observation kernel -/

/-- The hypergeometric weight of observing `k` objects with the property among `a` drawn
without replacement from three of which `s` have it, `C(s, k) C(3 − s, a − k)`; the
denominator `C(3, a)` is the row's normalization. -/
def hyper (a : Access) (s : WorldState) (k : Obs) : ℕ :=
  if k ≤ a then s.val.choose k.val * (3 - s.val).choose (a.val - k.val) else 0

/-- The observation kernel `P(o | a, s)` of section 1. -/
noncomputable def obs (a : Access) : Kernel WorldState Obs :=
  Kernel.ofWeights λ s k => (hyper a s k : ℝ≥0∞)

/-- A state is compatible with an observation when the observation is possible there. -/
def obsCompatible (a : Access) (k : Obs) (s : WorldState) : Prop := hyper a s k ≠ 0

instance (a : Access) (k : Obs) (s : WorldState) : Decidable (obsCompatible a k s) :=
  inferInstanceAs (Decidable (_ ≠ _))

instance (a : Access) : IsFiniteKernel (obs a) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

theorem obs_apply_singleton (a : Access) (s : WorldState) (k : Obs) :
    obs a s {k} = (hyper a s k : ℝ≥0∞) / ∑ k', (hyper a s k' : ℝ≥0∞) :=
  Kernel.ofWeights_apply_singleton _ _ _

/-- Compatibility is positive observation probability. -/
theorem obs_apply_singleton_ne_zero_iff (a : Access) (s : WorldState) (k : Obs) :
    obs a s {k} ≠ 0 ↔ obsCompatible a k s := by
  rw [obs_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or, Nat.cast_eq_zero]
  exact ⟨And.left, λ h => ⟨h, ENNReal.sum_ne_top.mpr λ _ _ => ENNReal.natCast_ne_top _⟩⟩

theorem obs_real_singleton (a : Access) (s : WorldState) (k : Obs) :
    (obs a s).real {k} = (hyper a s k : ℝ) / ∑ k', (hyper a s k' : ℝ) := by
  rw [obs, Kernel.ofWeights_real_singleton (w := λ s k => (hyper a s k : ℝ≥0∞)) _
    (λ _ => ENNReal.natCast_ne_top _)]
  simp only [ENNReal.toReal_natCast]

/-! ### The speaker and the listener -/

section Model

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
  (m : U → WorldState → Prop) [∀ u, DecidablePred (m u)]

/-- Quality: the utterance holds at every state the observation leaves possible, so its
expected log-probability under the speaker's belief is finite. -/
def Quality (a : Access) (k : Obs) (u : U) : Prop := ∀ s, obsCompatible a k s → m u s

instance (a : Access) (k : Obs) (u : U) : Decidable (Quality m a k u) :=
  inferInstanceAs (Decidable (∀ _, _ → _))

/-- The extension of an utterance. -/
def ext (u : U) : Finset WorldState := Finset.univ.filter (m u)

/-- The literal listener `Plex` of section 1: uniform on the utterance's extension. -/
noncomputable abbrev L0 : Kernel U WorldState := RSA.uniformListener (ext m)

/-- The speaker of equations (2) and (3) after observing `k` of `a` objects: the softmax at
rationality `α` of the expected log-probability of the literal listener under her belief,
which is `-log |⟦u⟧|` under Quality and `-∞` otherwise. -/
noncomputable def obsSpeaker (α : ℝ) (a : Access) : Kernel Obs U :=
  Kernel.ofWeights λ k u =>
    if Quality m a k u then ENNReal.ofReal (((ext m u).card : ℝ)⁻¹ ^ α) else 0

instance (α : ℝ) (a : Access) : IsFiniteKernel (obsSpeaker m α a) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- Equation (4): the speaker the listener models, the observation she cannot see marginalized
over the observation kernel. -/
noncomputable def speaker (α : ℝ) (a : Access) : Kernel WorldState U :=
  obsSpeaker m α a ∘ₖ obs a

instance (α : ℝ) (a : Access) : IsFiniteKernel (speaker m α a) :=
  inferInstanceAs (IsFiniteKernel (obsSpeaker m α a ∘ₖ obs a))

/-- Equation (1): the listener, the speaker's Bayesian inverse under a uniform prior. -/
noncomputable def listener (α : ℝ) (a : Access) : Kernel U WorldState :=
  (speaker m α a)†(uniformOn Set.univ)

variable {m}

/-- Under Quality the literal listener's probability of a possible state is the inverse of
the extension's size, the quantity the speaker's weight raises to the rationality. -/
theorem L0_apply_singleton_of_quality {a : Access} {k : Obs} {u : U} (hq : Quality m a k u)
    {s : WorldState} (hs : obsCompatible a k s) : L0 m u {s} = ((ext m u).card : ℝ≥0∞)⁻¹ := by
  rw [L0, RSA.uniformListener_apply_singleton, if_pos]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq s hs⟩

theorem speaker_apply_singleton (α : ℝ) (a : Access) (s : WorldState) (u : U) :
    speaker m α a s {u} = ∑ k, obs a s {k} * obsSpeaker m α a k {u} := by
  rw [speaker, Kernel.comp_apply' _ _ _ (measurableSet_singleton u), lintegral_fintype]
  exact Finset.sum_congr rfl λ k _ => mul_comm _ _

theorem speaker_real_singleton (α : ℝ) (a : Access) (s : WorldState) (u : U) :
    (speaker m α a s).real {u} = ∑ k, (obs a s).real {k} * (obsSpeaker m α a k).real {u} := by
  rw [measureReal_def, speaker_apply_singleton,
    ENNReal.toReal_sum λ k _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

theorem obsSpeaker_real_singleton (α : ℝ) (a : Access) (k : Obs) (u : U) :
    (obsSpeaker m α a k).real {u} =
      (if Quality m a k u then ((ext m u).card : ℝ)⁻¹ ^ α else 0) /
        ∑ u', if Quality m a k u' then ((ext m u').card : ℝ)⁻¹ ^ α else 0 := by
  rw [obsSpeaker, Kernel.ofWeights_real_singleton
    (w := λ k u => if Quality m a k u then ENNReal.ofReal (((ext m u).card : ℝ)⁻¹ ^ α) else 0) _
    (λ u' => by split_ifs <;> simp)]
  have h : ∀ u', (ENNReal.ofReal (((ext m u').card : ℝ)⁻¹ ^ α)).toReal =
      ((ext m u').card : ℝ)⁻¹ ^ α :=
    λ u' => ENNReal.toReal_ofReal (Real.rpow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) α)
  simp only [apply_ite ENNReal.toReal, h, ENNReal.toReal_zero]

/-- Comparing the listener's posterior at two states is comparing the speaker's probability of
the utterance at them, the uniform prior canceling. -/
theorem listener_real_lt_iff {α : ℝ} {a : Access} {u : U}
    (hu : (speaker m α a ∘ₘ uniformOn Set.univ) {u} ≠ 0) (s₁ s₂ : WorldState) :
    (listener m α a u).real {s₁} < (listener m α a u).real {s₂} ↔
      (speaker m α a s₁).real {u} < (speaker m α a s₂).real {u} := by
  rw [listener, ← Finset.coe_singleton, ← Finset.coe_singleton,
    posterior_real_finset_lt_iff _ _ hu, Finset.sum_singleton, Finset.sum_singleton,
    uniformOn_univ_real_singleton, uniformOn_univ_real_singleton]
  exact mul_lt_mul_iff_of_pos_left (by positivity)

/-- An utterance some state makes probable has positive marginal probability. -/
theorem comp_ne_zero_of_real_pos {α : ℝ} {a : Access} {u : U} {s : WorldState}
    (h : 0 < (speaker m α a s).real {u}) : (speaker m α a ∘ₘ uniformOn Set.univ) {u} ≠ 0 := by
  rw [Measure.comp_apply_singleton, ne_eq, Finset.sum_eq_zero_iff, not_forall]
  refine ⟨s, ?_⟩
  simp only [Finset.mem_univ, true_implies]
  rw [measureReal_def] at h
  exact mul_ne_zero (uniformOn_univ_singleton_ne_zero s) (ENNReal.toReal_pos_iff.mp h).1.ne'

end Model

/-! ### The alternatives, section 1.1 -/

/-- The quantifier alternatives *none*, *some*, *all*. -/
inductive QUtt where
  | none_
  | some_
  | all
  deriving DecidableEq, Fintype

instance : MeasurableSpace QUtt := ⊤
instance : DiscreteMeasurableSpace QUtt := ⟨λ _ => MeasurableSpace.measurableSet_top⟩
instance : MeasurableSingletonClass QUtt := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The standard meanings: *none* at zero, *some* at one or more, *all* at three. -/
def qMeaning : QUtt → WorldState → Prop
  | .none_, s => s = 0
  | .some_, s => 1 ≤ s
  | .all, s => s = 3

instance : ∀ q, DecidablePred (qMeaning q)
  | .none_, s => inferInstanceAs (Decidable (s = 0))
  | .some_, s => inferInstanceAs (Decidable (1 ≤ s))
  | .all, s => inferInstanceAs (Decidable (s = 3))

/-- The numeral alternatives *one*, *two*, *three*. -/
inductive NumUtt where
  | one
  | two
  | three
  deriving DecidableEq, Fintype

instance : MeasurableSpace NumUtt := ⊤
instance : DiscreteMeasurableSpace NumUtt := ⟨λ _ => MeasurableSpace.measurableSet_top⟩
instance : MeasurableSingletonClass NumUtt := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- [horn-1972]'s lower-bound meanings: a numeral holds at its number or more. -/
def lbMeaning : NumUtt → WorldState → Prop
  | .one, s => 1 ≤ s
  | .two, s => 2 ≤ s
  | .three, s => 3 ≤ s

instance : ∀ n, DecidablePred (lbMeaning n)
  | .one, s => inferInstanceAs (Decidable (1 ≤ s))
  | .two, s => inferInstanceAs (Decidable (2 ≤ s))
  | .three, s => inferInstanceAs (Decidable (3 ≤ s))

/-- The quantifiers as `Fin 3`, for sums over the alternatives. -/
def QUtt.equivFin : QUtt ≃ Fin 3 where
  toFun | .none_ => 0 | .some_ => 1 | .all => 2
  invFun | 0 => .none_ | 1 => .some_ | 2 => .all
  left_inv u := by cases u <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The numerals as `Fin 3`, for sums over the alternatives. -/
def NumUtt.equivFin : NumUtt ≃ Fin 3 where
  toFun | .one => 0 | .two => 1 | .three => 2
  invFun | 0 => .one | 1 => .two | 2 => .three
  left_inv u := by cases u <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem QUtt.sum_univ {M : Type*} [AddCommMonoid M] (f : QUtt → M) :
    ∑ u, f u = f .none_ + f .some_ + f .all := by
  rw [Fintype.sum_equiv QUtt.equivFin f (f ∘ QUtt.equivFin.symm) λ u => by simp,
    Fin.sum_univ_three]
  rfl

theorem NumUtt.sum_univ {M : Type*} [AddCommMonoid M] (f : NumUtt → M) :
    ∑ u, f u = f .one + f .two + f .three := by
  rw [Fintype.sum_equiv NumUtt.equivFin f (f ∘ NumUtt.equivFin.symm) λ u => by simp,
    Fin.sum_univ_three]
  rfl

/-! ### The predictions of section 1.1, for every rationality -/

section Findings

variable {α : ℝ}

/-- The extension sizes and Quality decisions the findings need. -/
private theorem qCells :
    (ext qMeaning .none_).card = 1 ∧ (ext qMeaning .some_).card = 3 ∧
      (ext qMeaning .all).card = 1 ∧ (ext lbMeaning .one).card = 3 ∧
      (ext lbMeaning .two).card = 2 ∧ (ext lbMeaning .three).card = 1 := by
  decide

/-- The speaker's real probability of an utterance at a state, expanded over the observations
and the alternatives. -/
private theorem speaker_real_q (a : Access) (s : WorldState) (u : QUtt) :
    (speaker qMeaning α a s).real {u} =
      ∑ k, ((hyper a s k : ℝ) / ∑ k', (hyper a s k' : ℝ)) *
        ((if Quality qMeaning a k u then ((ext qMeaning u).card : ℝ)⁻¹ ^ α else 0) /
          ∑ u', if Quality qMeaning a k u' then ((ext qMeaning u').card : ℝ)⁻¹ ^ α else 0) := by
  simp only [speaker_real_singleton, obs_real_singleton, obsSpeaker_real_singleton]

private theorem speaker_real_lb (a : Access) (s : WorldState) (u : NumUtt) :
    (speaker lbMeaning α a s).real {u} =
      ∑ k, ((hyper a s k : ℝ) / ∑ k', (hyper a s k' : ℝ)) *
        ((if Quality lbMeaning a k u then ((ext lbMeaning u).card : ℝ)⁻¹ ^ α else 0) /
          ∑ u', if Quality lbMeaning a k u' then ((ext lbMeaning u').card : ℝ)⁻¹ ^ α else 0) := by
  simp only [speaker_real_singleton, obs_real_singleton, obsSpeaker_real_singleton]

/-- The weights `|⟦u⟧|^{-α}` of an extension of three states and of two, `x = 3^{-α}` and
`y = 2^{-α}`, with `0 < x < y < 1`. -/
private theorem xy (hα : 0 < α) :
    (1 / 3 : ℝ) ^ α ≠ 0 ∧ 0 < (1 / 3 : ℝ) ^ α ∧ (1 / 3 : ℝ) ^ α < (1 / 2 : ℝ) ^ α ∧
      (1 / 2 : ℝ) ^ α < 1 :=
  have hx : 0 < (1 / 3 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  ⟨hx.ne', hx, Real.rpow_lt_rpow (by norm_num) (by norm_num) hα,
    Real.rpow_lt_one (by norm_num) (by norm_num) hα⟩

/-- With complete access, *some* is read as *some but not all*: the state with two objects is
more probable than the state with three, since at three the speaker would rather say *all*. -/
theorem some_full (hα : 0 < α) :
    (listener qMeaning α 3 .some_).real {3} < (listener qMeaning α 3 .some_).real {2} := by
  obtain ⟨hx0, hx, hxy, hy1⟩ := xy hα
  obtain ⟨h1, h2, h3, -, -, -⟩ := qCells
  have e2 : (speaker qMeaning α 3 2).real {.some_} = 1 := by
    rw [speaker_real_q]
    simp +decide only [Fin.sum_univ_four, QUtt.sum_univ, hyper, h1, h2, h3]
    norm_num [hx0]
  have e3 : (speaker qMeaning α 3 3).real {.some_} = (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + 1) := by
    rw [speaker_real_q]
    simp +decide only [Fin.sum_univ_four, QUtt.sum_univ, hyper, h1, h2, h3]
    norm_num [hx0]
  rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 2) (by rw [e2]; norm_num)), e2, e3,
    div_lt_one (by positivity)]
  linarith

/-- With access to one or two objects the implicature is canceled: the state with two objects
is not more probable than the state with three, since a speaker who has seen one or two
objects with the property can say nothing stronger than *some* whatever the state. -/
theorem some_partial (hα : 0 < α) :
    ¬ (listener qMeaning α 1 .some_).real {3} < (listener qMeaning α 1 .some_).real {2} ∧
      ¬ (listener qMeaning α 2 .some_).real {3} < (listener qMeaning α 2 .some_).real {2} := by
  obtain ⟨hx0, hx, hxy, hy1⟩ := xy hα
  obtain ⟨h1, h2, h3, -, -, -⟩ := qCells
  have a12 : (speaker qMeaning α 1 2).real {.some_} = 2 / 3 := by
    rw [speaker_real_q]
    simp +decide only [Fin.sum_univ_four, QUtt.sum_univ, hyper, h1, h2, h3]
    norm_num [hx0]
  have a13 : (speaker qMeaning α 1 3).real {.some_} = 1 := by
    rw [speaker_real_q]
    simp +decide only [Fin.sum_univ_four, QUtt.sum_univ, hyper, h1, h2, h3]
    norm_num [hx0]
  have a22 : (speaker qMeaning α 2 2).real {.some_} = 1 := by
    rw [speaker_real_q]
    simp +decide only [Fin.sum_univ_four, QUtt.sum_univ, hyper, h1, h2, h3]
    norm_num [hx0]
  have a23 : (speaker qMeaning α 2 3).real {.some_} = 1 := by
    rw [speaker_real_q]
    simp +decide only [Fin.sum_univ_four, QUtt.sum_univ, hyper, h1, h2, h3]
    norm_num [hx0]
  constructor
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 3) (by rw [a13]; norm_num)), a12,
      a13]
    norm_num
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 3) (by rw [a23]; norm_num)), a22,
      a23]
    exact lt_irrefl _

/-- With complete access the numerals get their exact readings: after *two* the state with two
objects beats the state with three, and after *one* the state with one beats both others. -/
theorem numerals_full (hα : 0 < α) :
    (listener lbMeaning α 3 .two).real {3} < (listener lbMeaning α 3 .two).real {2} ∧
      (listener lbMeaning α 3 .one).real {2} < (listener lbMeaning α 3 .one).real {1} ∧
      (listener lbMeaning α 3 .one).real {3} < (listener lbMeaning α 3 .one).real {1} := by
  obtain ⟨hx0, hx, hxy, hy1⟩ := xy hα
  obtain ⟨-, -, -, h4, h5, h6⟩ := qCells
  have hy0 : (1 / 2 : ℝ) ^ α ≠ 0 := (hx.trans hxy).ne'
  have t2 : (speaker lbMeaning α 3 2).real {.two} =
      (1 / 2 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have t3 : (speaker lbMeaning α 3 3).real {.two} =
      (1 / 2 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α + 1) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have o1 : (speaker lbMeaning α 3 1).real {.one} = 1 := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have o2 : (speaker lbMeaning α 3 2).real {.one} =
      (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have o3 : (speaker lbMeaning α 3 3).real {.one} =
      (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α + 1) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  refine ⟨?_, ?_, ?_⟩
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 2) (by rw [t2]; positivity)), t2,
      t3]
    exact div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 1) (by rw [o1]; norm_num)), o1,
      o2, div_lt_one (by positivity)]
    linarith
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 1) (by rw [o1]; norm_num)), o1,
      o3, div_lt_one (by positivity)]
    linarith

/-- After seeing one object, *one* carries no implicature: the state with one object beats
neither the state with two nor the state with three. -/
theorem one_minimal (hα : 0 < α) :
    ¬ (listener lbMeaning α 1 .one).real {2} < (listener lbMeaning α 1 .one).real {1} ∧
      ¬ (listener lbMeaning α 1 .one).real {3} < (listener lbMeaning α 1 .one).real {1} := by
  obtain ⟨hx0, hx, hxy, hy1⟩ := xy hα
  obtain ⟨-, -, -, h4, h5, h6⟩ := qCells
  have hy0 : (1 / 2 : ℝ) ^ α ≠ 0 := (hx.trans hxy).ne'
  have v1 : (speaker lbMeaning α 1 1).real {.one} = 1 / 3 := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have v2 : (speaker lbMeaning α 1 2).real {.one} = 2 / 3 := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have v3 : (speaker lbMeaning α 1 3).real {.one} = 1 := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  constructor
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 3) (by rw [v3]; norm_num)), v1, v2]
    norm_num
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 3) (by rw [v3]; norm_num)), v1, v3]
    norm_num

/-- After seeing two objects, *two* carries no implicature: the state with two objects does not
beat the state with three, since the speaker could only have seen both objects with the
property in either. -/
theorem two_partial (hα : 0 < α) :
    ¬ (listener lbMeaning α 2 .two).real {3} < (listener lbMeaning α 2 .two).real {2} := by
  obtain ⟨hx0, hx, hxy, hy1⟩ := xy hα
  obtain ⟨-, -, -, h4, h5, h6⟩ := qCells
  have hy0 : (1 / 2 : ℝ) ^ α ≠ 0 := (hx.trans hxy).ne'
  have v2 : (speaker lbMeaning α 2 2).real {.two} =
      1 / 3 * ((1 / 2 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α)) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have v3 : (speaker lbMeaning α 2 3).real {.two} =
      (1 / 2 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 3) (by rw [v3]; positivity)), v2, v3,
    not_lt]
  have : 0 ≤ (1 / 2 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) := by positivity
  linarith

/-- After seeing two objects, *one* keeps a partial implicature: the state with one object beats
the state with three, where the speaker who saw both would have preferred *two*, but not the
state with two, where she may have seen only one. -/
theorem one_partial (hα : 0 < α) :
    (listener lbMeaning α 2 .one).real {3} < (listener lbMeaning α 2 .one).real {1} ∧
      ¬ (listener lbMeaning α 2 .one).real {2} < (listener lbMeaning α 2 .one).real {1} := by
  obtain ⟨hx0, hx, hxy, hy1⟩ := xy hα
  obtain ⟨-, -, -, h4, h5, h6⟩ := qCells
  have hy0 : (1 / 2 : ℝ) ^ α ≠ 0 := (hx.trans hxy).ne'
  have v1 : (speaker lbMeaning α 2 1).real {.one} = 2 / 3 := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have v2 : (speaker lbMeaning α 2 2).real {.one} =
      2 / 3 + 1 / 3 * ((1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α)) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have v3 : (speaker lbMeaning α 2 3).real {.one} =
      (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) := by
    rw [speaker_real_lb]
    simp +decide only [Fin.sum_univ_four, NumUtt.sum_univ, hyper, h4, h5, h6]
    norm_num [hx0, hy0]
  have hp : (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  constructor
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 1) (by rw [v1]; norm_num)), v1, v3]
    linarith
  · rw [listener_real_lt_iff (comp_ne_zero_of_real_pos (s := 1) (by rw [v1]; norm_num)), v1, v2,
      not_lt]
    have : 0 ≤ (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + (1 / 2 : ℝ) ^ α) := by positivity
    linarith

end Findings

end GoodmanStuhlmuller2013
