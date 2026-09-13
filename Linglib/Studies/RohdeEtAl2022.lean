import Linglib.Pragmatics.RSA.Silence

/-!
# Rohde, Hoek, Keshev and Franke (2022): This better be interesting

This file formalizes the paper's Bayesian conceptualization of a listener's expectations
about upcoming content: the probability of a meaning given that a speaker chose to report
it combines the prior probability of the situation with the likelihood that a speaker would
articulate it, and the two are separable, the likelihood varying with the context of speech.
Over the two values of the paper's forced choice, one near the pretest mean and one a
standard deviation above it, the posterior on the atypical value given a report exceeds its
prior exactly when the atypical situation is the likelier to be reported,
`prior_lt_posterior_iff`, and between two contexts the posterior is larger where the atypical
situation is relatively likelier to be reported, `posterior_lt_posterior_iff`. An
informativity speaker who may also stay silent, silence conveying only the prior, derives the
direction of the likelihood: because silence is the more attractive the likelier the situation,
a report is likelier at the atypical value, `S_report_lt`, so a report shifts the guess toward
the atypical value relative to the prior, `prior_lt_posterior`, the more so the more
available silence is, `posterior_lt_of_silence_lt`, and not at all when the speaker was asked
and silence was not an option, `posterior_eq_prior_of_asked`.

## Implementation notes

The paper gives the conceptualization in prose and its predictions through four
forced-choice experiments; the speaker with a null message is the model the paper takes from
its precursors, on the substrate's kernel pipeline, and the null message's weight is the
parameter the paper's contexts vary. The experiments' selection rates are not represented.

## References

* [H. Rohde, J. Hoek, M. Keshev, M. Franke, *This better be interesting: a speaker's decision
  to speak cues listeners to expect informative content* (2022)][rohde-etal-2022]
* [L. Bergen, R. Levy, N. D. Goodman, *Pragmatic reasoning through semantic inference*
  (2016)][bergen-levy-goodman-2016]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace RohdeEtAl2022

/-- The two values of the forced choice: one near the mean of the pretest, one a standard
deviation above it. -/
inductive Value
  | typical
  | atypical
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Value := ⊤
instance : DiscreteMeasurableSpace Value := ⟨λ _ => trivial⟩

private theorem pair_support (μ : Measure Value) :
    ∀ v, μ {v} ≠ 0 → v = Value.atypical ∨ v = Value.typical :=
  λ v _ => by cases v <;> simp

/-! ### The Bayesian conceptualization -/

section Bayes

variable (μ : Measure Value) [IsProbabilityMeasure μ]

/-- Guessing a reported value: the posterior on the atypical value given that the speaker
reported exceeds its prior exactly when the atypical situation is the likelier to be reported.
The think condition asks for the prior, the announce condition for the posterior. -/
theorem prior_lt_posterior_iff (report : Kernel Value Bool) [IsFiniteKernel report]
    (hx : (report ∘ₘ μ) {true} ≠ 0) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0) :
    μ.real {.atypical} < ((report†μ) true).real {.atypical} ↔
      (report .typical).real {true} < (report .atypical).real {true} :=
  real_lt_posterior_real_singleton_iff_of_pair report μ (by decide) (pair_support μ) hx ha ht

/-- The likelihood is separable from the prior and manipulable: between two contexts, the
posterior on the atypical value given a report is larger in the context where the atypical
situation is relatively likelier to be reported. -/
theorem posterior_lt_posterior_iff (report₁ report₂ : Kernel Value Bool)
    [IsFiniteKernel report₁] [IsFiniteKernel report₂] (hx₁ : (report₁ ∘ₘ μ) {true} ≠ 0)
    (hx₂ : (report₂ ∘ₘ μ) {true} ≠ 0) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0) :
    ((report₁†μ) true).real {.atypical} < ((report₂†μ) true).real {.atypical} ↔
      (report₁ .atypical).real {true} * (report₂ .typical).real {true} <
        (report₂ .atypical).real {true} * (report₁ .typical).real {true} := by
  have hm₁ : 0 < (report₁ ∘ₘ μ).real {true} :=
    ENNReal.toReal_pos hx₁ (measure_ne_top _ _)
  have hm₂ : 0 < (report₂ ∘ₘ μ).real {true} :=
    ENNReal.toReal_pos hx₂ (measure_ne_top _ _)
  have hp : 0 < μ.real {Value.atypical} := ENNReal.toReal_pos ha (measure_ne_top _ _)
  have hq : 0 < μ.real {Value.typical} := ENNReal.toReal_pos ht (measure_ne_top _ _)
  rw [posterior_real_singleton _ _ hx₁, posterior_real_singleton _ _ hx₂,
    div_lt_div_iff₀ hm₁ hm₂,
    Measure.comp_real_singleton_of_pair _ _ (by decide) (pair_support μ),
    Measure.comp_real_singleton_of_pair _ _ (by decide) (pair_support μ), ← sub_pos]
  rw [show μ.real {Value.atypical} * (report₂ Value.atypical).real {true} *
      (μ.real {Value.atypical} * (report₁ Value.atypical).real {true} +
        μ.real {Value.typical} * (report₁ Value.typical).real {true}) -
      μ.real {Value.atypical} * (report₁ Value.atypical).real {true} *
      (μ.real {Value.atypical} * (report₂ Value.atypical).real {true} +
        μ.real {Value.typical} * (report₂ Value.typical).real {true}) =
      μ.real {Value.atypical} * μ.real {Value.typical} *
        ((report₂ Value.atypical).real {true} * (report₁ Value.typical).real {true} -
          (report₁ Value.atypical).real {true} * (report₂ Value.typical).real {true}) by ring,
    mul_pos_iff_of_pos_left (mul_pos hp hq), sub_pos]

end Bayes

/-! ### Informativity and the null message -/

/-- A report of a value, or silence. -/
abbrev Utterance := WithSilence Value

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩

/-- A report is true of the value it reports; silence is true of both. -/
def extension : Utterance → Set Value
  | some v => {v}
  | none => Set.univ

variable (μ : Measure Value)

/-- The literal listener: a report conveys its value, silence conveys the prior. -/
noncomputable def L0 : Kernel Utterance Value :=
  literalListener μ λ u => (extension u).indicator 1

theorem L0_some_of_ne {v w : Value} (h : v ≠ w) : L0 μ (some v) {w} = 0 :=
  literalListener_indicator_apply_singleton_of_notMem μ extension
    (by simp [extension, Ne.symm h])

variable (α : ℝ) (κs κn : ℝ≥0∞)

/-- The speaker: the informativity speaker over reports, weighted `κs`, with silence weighted
`κn`. -/
noncomputable def S : Kernel Value Utterance := speaker α (liftCostFactor κn λ _ => κs) (L0 μ)

instance : IsFiniteKernel (S μ α κs κn) :=
  inferInstanceAs (IsFiniteKernel (speaker α (liftCostFactor κn λ _ => κs) (L0 μ)))

/-! ### The decision to speak as the observation -/

/-- Whether the speaker spoke: the report's form, a value reported or silence. -/
noncomputable def spoke : Kernel Value Bool := (S μ α κs κn).map Option.isSome

instance : IsFiniteKernel (spoke μ α κs κn) :=
  inferInstanceAs (IsFiniteKernel ((S μ α κs κn).map Option.isSome))

/-- The probability of speaking at a value is the share of the report of that value, the
other report being false there. -/
theorem spoke_apply_true (hα : 0 < α) (v : Value) :
    spoke μ α κs κn v {true} = S μ α κs κn v {some v} := by
  rw [spoke, Kernel.map_apply' _ Measurable.of_discrete _ (MeasurableSet.singleton true),
    show (Option.isSome ⁻¹' ({true} : Set Bool) : Set Utterance) =
      {some .typical} ∪ {some .atypical} by ext u; rcases u with _ | (_ | _) <;> simp,
    measure_union (by simp) (MeasurableSet.singleton _)]
  simp only [S]
  cases v
  · rw [speaker_apply_singleton_eq_zero hα
      (L0_some_of_ne μ (v := .atypical) (w := .typical) (by decide)), add_zero]
  · rw [speaker_apply_singleton_eq_zero hα
      (L0_some_of_ne μ (v := .typical) (w := .atypical) (by decide)), zero_add]

variable [IsProbabilityMeasure μ]

theorem L0_some_self {v : Value} (hv : μ {v} ≠ 0) : L0 μ (some v) {v} = 1 :=
  literalListener_indicator_apply_singleton_of_eq_singleton μ extension rfl hv

theorem L0_none (v : Value) : L0 μ none {v} = μ {v} :=
  literalListener_indicator_apply_singleton_of_eq_univ μ extension rfl v

theorem L0_le_one (u : Utterance) (v : Value) : L0 μ u {v} ≤ 1 := by
  rcases u with _ | w
  · rw [L0_none]; exact prob_le_one
  · by_cases h : w = v
    · subst h
      by_cases hv : μ {w} = 0
      · rw [L0, literalListener_indicator_apply_singleton μ extension (Set.mem_singleton w),
          hv, mul_zero]
        exact zero_le_one
      · rw [L0_some_self μ hv]
    · rw [L0_some_of_ne μ h]; exact zero_le_one

/-! ### Newsworthiness -/


private theorem cost_ne_top (hκs : κs ≠ ∞) (hκn : κn ≠ ∞) :
    ∀ u : Utterance, liftCostFactor κn (λ _ => κs) u ≠ ∞ := by
  rintro (_ | _) <;> simpa

/-- The share of a report at its value: the report competes with silence only, and silence is
weighted by the prior of the value. -/
theorem S_report (hα : 0 < α) (hκs : κs ≠ ∞) (hκn : κn ≠ ∞) {v : Value}
    (hv : μ {v} ≠ 0) :
    (S μ α κs κn v).real {some v} =
      κs.toReal / (κs.toReal + κn.toReal * (μ {v} ^ α).toReal) := by
  rw [S, speaker_real_singleton hα.le (cost_ne_top κs κn hκs hκn) (L0_le_one μ · v),
    Fintype.sum_option,
    Finset.sum_eq_single v
      (λ w _ hw => by
        rw [L0_some_of_ne μ hw, ENNReal.zero_rpow_of_pos hα, ENNReal.toReal_zero, zero_mul])
      (λ h => absurd (Finset.mem_univ v) h),
    L0_some_self μ hv, L0_none, ENNReal.one_rpow, ENNReal.toReal_one, one_mul,
    liftCostFactor_some, liftCostFactor_none, add_comm, mul_comm (κn.toReal)]

/-- The share of a report is positive. -/
theorem S_report_pos (hα : 0 < α) (hκs0 : κs ≠ 0) (hκs : κs ≠ ∞) (hκn : κn ≠ ∞)
    {v : Value} (hv : μ {v} ≠ 0) : 0 < (S μ α κs κn v).real {some v} := by
  rw [S_report μ α κs κn hα hκs hκn hv]
  have hs : 0 < κs.toReal := ENNReal.toReal_pos hκs0 hκs
  exact div_pos hs (add_pos_of_pos_of_nonneg hs (by positivity))

/-- Improbable situations yield likely utterances: the share of a report is greater at the
value with the smaller prior, since silence, which conveys the prior, is the more attractive
the likelier the value. -/
theorem S_report_lt (hα : 0 < α) (hκs0 : κs ≠ 0) (hκs : κs ≠ ∞) (hκn0 : κn ≠ 0)
    (hκn : κn ≠ ∞) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0)
    (h : μ {.atypical} < μ {.typical}) :
    (S μ α κs κn .typical).real {some .typical} <
      (S μ α κs κn .atypical).real {some .atypical} := by
  rw [S_report μ α κs κn hα hκs hκn ht, S_report μ α κs κn hα hκs hκn ha]
  have hs : 0 < κs.toReal := ENNReal.toReal_pos hκs0 hκs
  have hn : 0 < κn.toReal := ENNReal.toReal_pos hκn0 hκn
  have hpow : (μ {Value.atypical} ^ α).toReal < (μ {Value.typical} ^ α).toReal :=
    (ENNReal.toReal_lt_toReal (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
      (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))).mpr (ENNReal.rpow_lt_rpow h hα)
  rw [div_lt_div_iff_of_pos_left hs (add_pos_of_pos_of_nonneg hs (by positivity))
    (add_pos_of_pos_of_nonneg hs (by positivity))]
  exact add_lt_add_right (mul_lt_mul_of_pos_left hpow hn) _

theorem spoke_apply_true_ne_zero (hα : 0 < α) (hκs0 : κs ≠ 0) (hκs : κs ≠ ∞)
    (hκn : κn ≠ ∞) {v : Value} (hv : μ {v} ≠ 0) : spoke μ α κs κn v {true} ≠ 0 := by
  rw [spoke_apply_true μ α κs κn hα]
  intro h0
  have := S_report_pos μ α κs κn hα hκs0 hκs hκn hv
  rw [measureReal_def, h0, ENNReal.toReal_zero] at this
  exact lt_irrefl _ this

/-- A report shifts the guess toward the atypical value: given that the speaker spoke, the
posterior on the atypical value exceeds the prior that the think condition returns. -/
theorem prior_lt_posterior (hα : 0 < α) (hκs0 : κs ≠ 0) (hκs : κs ≠ ∞)
    (hκn0 : κn ≠ 0) (hκn : κn ≠ ∞) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0)
    (h : μ {.atypical} < μ {.typical}) :
    μ.real {.atypical} < (((spoke μ α κs κn)†μ) true).real {.atypical} := by
  rw [prior_lt_posterior_iff μ _
    (comp_apply_singleton_ne_zero _ _ ht
      (spoke_apply_true_ne_zero μ α κs κn hα hκs0 hκs hκn ht)) ht ha]
  simpa only [measureReal_def, spoke_apply_true μ α κs κn hα] using
    S_report_lt μ α κs κn hα hκs0 hκs hκn0 hκn ht ha h

/-- When the speaker was asked, so that silence was not an option, a report carries no
information about typicality: the posterior is the prior, as the when-asked and think
conditions align. -/
theorem posterior_eq_prior_of_asked (hα : 0 < α) (hκs0 : κs ≠ 0) (hκs : κs ≠ ∞)
    (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0) :
    (((spoke μ α κs 0)†μ) true).real {.atypical} = μ.real {.atypical} := by
  have h1 : ∀ v, μ {v} ≠ 0 → (spoke μ α κs 0 v).real {true} = 1 := λ v hv => by
    rw [measureReal_def, spoke_apply_true μ α κs 0 hα, ← measureReal_def,
      S_report μ α κs 0 hα hκs ENNReal.zero_ne_top hv, ENNReal.toReal_zero, zero_mul, add_zero]
    exact div_self (ENNReal.toReal_pos hκs0 hκs).ne'
  rw [posterior_real_singleton _ _
      (comp_apply_singleton_ne_zero _ _ ht
        (spoke_apply_true_ne_zero μ α κs 0 hα hκs0 hκs ENNReal.zero_ne_top ht)),
    Measure.comp_real_singleton_of_pair _ _ (by decide) (pair_support μ), h1 _ ha, h1 _ ht,
    mul_one, mul_one, measureReal_singleton_add_singleton_of_pair μ (by decide) (pair_support μ),
    div_one]

/-- The likelihood of speech is malleable: the more available silence is, the more a report
shifts the guess toward the atypical value, as the out-of-the-blue and large-audience
conditions increase the emphasis on information exchange. -/
theorem posterior_lt_of_silence_lt (hα : 0 < α) (hκs0 : κs ≠ 0) (hκs : κs ≠ ∞)
    {κn₁ κn₂ : ℝ≥0∞} (hκn₂ : κn₂ ≠ ∞) (hlt : κn₁ < κn₂) (ht : μ {.typical} ≠ 0)
    (ha : μ {.atypical} ≠ 0) (h : μ {.atypical} < μ {.typical}) :
    (((spoke μ α κs κn₁)†μ) true).real {.atypical} <
      (((spoke μ α κs κn₂)†μ) true).real {.atypical} := by
  have hκn₁ : κn₁ ≠ ∞ := ne_top_of_lt hlt
  rw [posterior_lt_posterior_iff μ _ _
    (comp_apply_singleton_ne_zero _ _ ht
      (spoke_apply_true_ne_zero μ α κs κn₁ hα hκs0 hκs hκn₁ ht))
    (comp_apply_singleton_ne_zero _ _ ht
      (spoke_apply_true_ne_zero μ α κs κn₂ hα hκs0 hκs hκn₂ ht)) ht ha]
  simp only [measureReal_def, spoke_apply_true μ α κs _ hα]
  rw [← measureReal_def, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    S_report μ α κs κn₁ hα hκs hκn₁ ha, S_report μ α κs κn₂ hα hκs hκn₂ ht,
    S_report μ α κs κn₂ hα hκs hκn₂ ha, S_report μ α κs κn₁ hα hκs hκn₁ ht]
  have hs : 0 < κs.toReal := ENNReal.toReal_pos hκs0 hκs
  have hn : κn₁.toReal < κn₂.toReal := (ENNReal.toReal_lt_toReal hκn₁ hκn₂).mpr hlt
  have hn₁ : 0 ≤ κn₁.toReal := ENNReal.toReal_nonneg
  have hAB : (μ {Value.atypical} ^ α).toReal < (μ {Value.typical} ^ α).toReal :=
    (ENNReal.toReal_lt_toReal (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
      (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))).mpr (ENNReal.rpow_lt_rpow h hα)
  have hB : 0 ≤ (μ {Value.atypical} ^ α).toReal := ENNReal.toReal_nonneg
  set s := κs.toReal
  set n₁ := κn₁.toReal
  set n₂ := κn₂.toReal
  set A := (μ {Value.typical} ^ α).toReal
  set B := (μ {Value.atypical} ^ α).toReal
  have hA : 0 ≤ A := hB.trans hAB.le
  have d₁ : 0 < s + n₁ * B := add_pos_of_pos_of_nonneg hs (mul_nonneg hn₁ hB)
  have d₂ : 0 < s + n₂ * A := add_pos_of_pos_of_nonneg hs (mul_nonneg (hn₁.trans hn.le) hA)
  have d₃ : 0 < s + n₂ * B := add_pos_of_pos_of_nonneg hs (mul_nonneg (hn₁.trans hn.le) hB)
  have d₄ : 0 < s + n₁ * A := add_pos_of_pos_of_nonneg hs (mul_nonneg hn₁ hA)
  rw [div_mul_div_comm, div_mul_div_comm, div_lt_div_iff₀ (mul_pos d₁ d₂) (mul_pos d₃ d₄)]
  refine mul_lt_mul_of_pos_left ?_ (mul_pos hs hs)
  have key : (s + n₁ * B) * (s + n₂ * A) - (s + n₂ * B) * (s + n₁ * A)
      = s * ((n₂ - n₁) * (A - B)) := by ring
  linarith [key, mul_pos hs (mul_pos (sub_pos.mpr hn) (sub_pos.mpr hAB))]

end RohdeEtAl2022
