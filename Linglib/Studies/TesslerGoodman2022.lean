import Linglib.Studies.TesslerGoodman2019

/-!
# Tessler and Goodman (2022): Warm (for Winter): Inferring Comparison Classes in Communication

This file formalizes [tessler-goodman-2022]'s model of how a listener infers the comparison
class of a bare gradable adjective. The literal listener of [lassiter-goodman-2017] interprets
*tall* and *short* as thresholds on the degree, the threshold drawn from a uniform prior over
the support of the degree prior, and conditions the prior of the comparison class on the
utterance with the threshold integrated out (4)–(5), `thresholdMeaning`, `meaning`, `L0`, the
substrate's `RSA.literalListener` at the threshold prior of [tessler-goodman-2019]. The speaker
knows the comparison class and chooses among *tall*, *short* and silence to convey the degree
(3), `S`, the substrate's `RSA.speaker`. The pragmatic listener knows the referent's kind but
not the class the speaker assumed, and infers the degree and the class jointly at the kind's
degree prior and a flat class prior (1), `L1`, the substrate's `RSA.familyListener`.

The speaker's share of *tall* at a degree depends on the comparison class only through the
class's mean degree, and falls as that mean rises, `S_tall_real`, `share_lt_share`: *tall*
is the more informative the lower the class's expectations. Averaged over the kind's plausible
degrees, the listener who hears *tall* therefore infers the class with the smaller mean and the
listener who hears *short* the class with the larger mean, `tall_infers_smaller_mean`,
`short_infers_larger_mean`, whatever the rationality. This is the polarity by expectations
interaction of Figure 1: a basketball player, whose heights exceed people's, is *tall* for a
person and *short* for a basketball player, and a jockey the reverse, `expected_tall`,
`expected_short`; *warm (for winter)* is the same interaction on the scale of temperature. The
literal listener of (6), who updates on the literal meaning alone, predicts the opposite,
preferring for *tall* the class with the larger mean, `literalScore_tall_lt`.

The free-paraphrase experiment over ninety item sets and the comparison of comparison-class
priors, flat, basic-level biased and frequency weighted, are the paper's empirical content and
are described, not formalized.

## Implementation notes

The degree scale is a finite type carrying a degree in the open unit interval, and the priors
of the comparison classes and of the kind are probability measures on it with full support, so
that every degree is a live hypothesis; the paper's degree priors are elicited or fitted
distributions. Costs are equal and omitted. The comparison-class prior is flat, the paper's
first model variant; the theorems concern the direction of the inference, which the priors
with a basic-level bias or a frequency effect modulate but do not reverse.

## References

* [tessler-goodman-2022]
* [tessler-goodman-2019]
* [lassiter-goodman-2017]
* [frank-goodman-2012]
* [kennedy-2007]
-/

namespace TesslerGoodman2022

open MeasureTheory ProbabilityTheory RSA TesslerGoodman2019
open scoped ENNReal

/-- The utterances: the positive adjective, the negative adjective, and silence. -/
inductive Utterance
  | tall
  | short
  | silent
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩

/-- The two comparison classes of the idealized case: the referent's own subordinate category,
or a superordinate category. -/
inductive ComparisonClass
  | subordinate
  | superordinate
  deriving DecidableEq, Fintype

instance : MeasurableSpace ComparisonClass := ⊤

instance : DiscreteMeasurableSpace ComparisonClass := ⟨λ _ => trivial⟩

instance : Nonempty ComparisonClass := ⟨.subordinate⟩

/-- The threshold semantics (4): *tall* holds of a degree above the threshold, *short* of one
below it, and silence everywhere. -/
def thresholdMeaning : Utterance → ℝ → ℝ → Prop
  | .tall, θ, x => θ < x
  | .short, θ, x => x < θ
  | .silent, _, _ => True

/-- The uniform threshold prior's mass above a degree in the unit interval. -/
theorem uniformThreshold_Ioi {p : ℝ} (h0 : 0 ≤ p) :
    uniformThreshold (Set.Ioi p) = ENNReal.ofReal (1 - p) := by
  rw [uniformThreshold, Measure.restrict_apply measurableSet_Ioi,
    show Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 by
      ext θ; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h, _, h1⟩; exact ⟨h, h1⟩
      · rintro ⟨h, h1⟩; exact ⟨h, by linarith, h1⟩,
    Real.volume_Ioc]

theorem uniformThreshold_univ : uniformThreshold Set.univ = 1 := by
  rw [uniformThreshold, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

section Model

variable {X : Type*}

/-- The meaning of (5): the threshold semantics integrated out against the uniform threshold
prior. -/
noncomputable def meaning (deg : X → ℝ) (u : Utterance) (x : X) : ℝ≥0∞ :=
  uniformThreshold {θ | thresholdMeaning u θ (deg x)}

variable (deg : X → ℝ)

theorem meaning_tall {x : X} (h : deg x ≤ 1) : meaning deg .tall x = ENNReal.ofReal (deg x) :=
  uniformThreshold_Iio h

theorem meaning_short {x : X} (h : 0 ≤ deg x) :
    meaning deg .short x = ENNReal.ofReal (1 - deg x) :=
  uniformThreshold_Ioi h

theorem meaning_silent (x : X) : meaning deg .silent x = 1 := by
  show uniformThreshold Set.univ = 1
  exact uniformThreshold_univ

variable [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]

/-- The literal listener (4)–(5): the comparison class's degree prior conditioned on the
marginalized meaning. -/
noncomputable def L0 (classPrior : ComparisonClass → Measure X) (c : ComparisonClass) :
    Kernel Utterance X :=
  literalListener (classPrior c) (meaning deg)

/-- The speaker (3): rationality `α`, equal costs, the comparison class known. -/
noncomputable def S (α : ℝ) (classPrior : ComparisonClass → Measure X) (c : ComparisonClass) :
    Kernel X Utterance :=
  speaker α 1 (L0 deg classPrior c)

/-- The pragmatic listener (1): the joint posterior over the degree and the comparison class,
at the kind's degree prior and a flat class prior. -/
noncomputable def L1 [Nonempty X] (α : ℝ) (classPrior : ComparisonClass → Measure X)
    (κ : Measure X) [IsFiniteMeasure κ] : Kernel Utterance (X × ComparisonClass) :=
  familyListener (L0 deg classPrior) α 1 (κ.prod (uniformOn Set.univ))

/-- The mean degree under a comparison class. -/
noncomputable def mean (classPrior : ComparisonClass → Measure X) (c : ComparisonClass) : ℝ :=
  expectedPrevalence (classPrior c) deg

/-- The speaker's share of the positive adjective as a function of the degree `a` and the
class's mean `m`: its informativity against the negative adjective and silence. -/
noncomputable def share (α a m : ℝ) : ℝ :=
  (a / m) ^ α / ((a / m) ^ α + ((1 - a) / (1 - m)) ^ α + 1)

/-- The class marginal of the literal listener (6) at a flat class prior, up to the common
normalizer: the prior probability under the class that the utterance is true. -/
noncomputable def literalScore (classPrior : ComparisonClass → Measure X) (u : Utterance)
    (c : ComparisonClass) : ℝ :=
  ∑ x, (classPrior c).real {x} * (meaning deg u x).toReal

variable (classPrior : ComparisonClass → Measure X) {α : ℝ}

/-- Comparison-class preference of the pragmatic listener reduces to the kind-prior-weighted
speaker shares: the flat class prior and the observation marginal cancel. -/
theorem L1_snd_real_lt_iff [Nonempty X] (κ : Measure X) [IsFiniteMeasure κ] {u : Utterance}
    (hu : (familySpeaker (L0 deg classPrior) α 1 ∘ₘ κ.prod (uniformOn Set.univ)) {u} ≠ 0)
    (c₁ c₂ : ComparisonClass) :
    (L1 deg α classPrior κ u).snd.real {c₁} < (L1 deg α classPrior κ u).snd.real {c₂} ↔
      ∑ x, κ.real {x} * (S deg α classPrior c₁ x).real {u} <
        ∑ x, κ.real {x} * (S deg α classPrior c₂ x).real {u} := by
  rw [Measure.snd_real_singleton, Measure.snd_real_singleton, L1,
    familyListener_real_lt_iff _ _ _ hu, Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_singleton, Measure.prod_real_singleton, S]
  have hc : ∀ c : ComparisonClass,
      (uniformOn (Set.univ : Set ComparisonClass)).real {c} = 1 / 2 := by
    intro c
    rw [measureReal_def, uniformOn_univ_apply_singleton,
      show Fintype.card ComparisonClass = 2 from rfl, ENNReal.toReal_inv]
    norm_num
  simp only [hc, mul_assoc, mul_left_comm _ (1 / 2 : ℝ), ← Finset.mul_sum]
  exact mul_lt_mul_iff_right₀ (by norm_num)

variable [∀ c, IsProbabilityMeasure (classPrior c)]

private theorem sum_utterance (f : Utterance → ℝ) : ∑ u, f u = f .tall + f .short + f .silent := by
  rw [show (Finset.univ : Finset Utterance) = {.tall, .short, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-- A probability measure on a finite type has a positive-mass atom. -/
private theorem exists_real_pos (μ : Measure X) [IsProbabilityMeasure μ] : ∃ x, 0 < μ.real {x} := by
  by_contra h
  push Not at h
  have := Finset.sum_nonpos (s := Finset.univ) λ x _ => h x
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ] at this
  linarith

theorem mean_pos (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) :
    0 < mean deg classPrior c := by
  obtain ⟨x, hx⟩ := exists_real_pos (classPrior c)
  rw [mean, expectedPrevalence_eq_sum]
  exact Finset.sum_pos' (λ y _ => mul_nonneg measureReal_nonneg (hdeg y).1.le)
    ⟨x, Finset.mem_univ _, mul_pos hx (hdeg x).1⟩

theorem mean_lt_one (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) :
    mean deg classPrior c < 1 := by
  obtain ⟨x, hx⟩ := exists_real_pos (classPrior c)
  have h1 : ∑ y, (classPrior c).real {y} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  rw [mean, expectedPrevalence_eq_sum, ← h1]
  exact Finset.sum_lt_sum (λ y _ => mul_le_of_le_one_right measureReal_nonneg (hdeg y).2.le)
    ⟨x, Finset.mem_univ _, mul_lt_of_lt_one_right hx (hdeg x).2⟩

/-- The row sum of the negative adjective's meaning is the complement of the mean. -/
theorem sum_meaning_short (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) :
    ∑ x, meaning deg .short x * classPrior c {x} = ENNReal.ofReal (1 - mean deg classPrior c) := by
  have h1 : ∑ y, (classPrior c).real {y} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  rw [mean, expectedPrevalence_eq_sum, ← h1, ← Finset.sum_sub_distrib,
    ENNReal.ofReal_sum_of_nonneg λ x _ => by
      nlinarith [(hdeg x).2, measureReal_nonneg (μ := classPrior c) (s := {x})]]
  refine Finset.sum_congr rfl λ x _ => ?_
  rw [meaning_short deg (hdeg x).1.le, ← ENNReal.ofReal_toReal (measure_ne_top (classPrior c) {x}),
    ← ENNReal.ofReal_mul (by linarith [(hdeg x).2])]
  congr 1
  rw [measureReal_def]
  ring

/-- The row sum of the positive adjective's meaning is the mean. -/
theorem sum_meaning_tall (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) :
    ∑ x, meaning deg .tall x * classPrior c {x} = ENNReal.ofReal (mean deg classPrior c) :=
  expectedMeaning_uniformThreshold deg (classPrior c) λ x => ⟨(hdeg x).1.le, (hdeg x).2.le⟩

theorem L0_silent_apply (c : ComparisonClass) (x : X) :
    L0 deg classPrior c .silent {x} = classPrior c {x} := by
  rw [L0, literalListener_apply_singleton]
  simp only [meaning_silent, one_mul]
  rw [sum_measure_singleton, Finset.coe_univ, measure_univ, div_one]

theorem L0_tall_real (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) (x : X) :
    (L0 deg classPrior c .tall).real {x} =
      deg x * (classPrior c).real {x} / mean deg classPrior c := by
  rw [L0, measureReal_def, literalListener_apply_singleton, sum_meaning_tall deg classPrior hdeg,
    meaning_tall deg (hdeg x).2.le, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hdeg x).1.le, ENNReal.toReal_ofReal (mean_pos deg classPrior hdeg c).le,
    measureReal_def]

theorem L0_short_real (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) (x : X) :
    (L0 deg classPrior c .short).real {x} =
      (1 - deg x) * (classPrior c).real {x} / (1 - mean deg classPrior c) := by
  rw [L0, measureReal_def, literalListener_apply_singleton, sum_meaning_short deg classPrior hdeg,
    meaning_short deg (hdeg x).1.le, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [(hdeg x).2]),
    ENNReal.toReal_ofReal (by linarith [mean_lt_one deg classPrior hdeg c]), measureReal_def]

/-- The speaker's share of *tall* depends on the comparison class only through its mean. -/
theorem S_tall_real (hα : 0 < α) (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass)
    {x : X} (hx : classPrior c {x} ≠ 0) :
    (S deg α classPrior c x).real {.tall} = share α (deg x) (mean deg classPrior c) := by
  rw [S, speaker_real_singleton (cost := 1) (L := L0 deg classPrior c) hα.le
    (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one _ _ u _), sum_utterance]
  simp only [Pi.one_apply, ENNReal.toReal_one, mul_one, ← ENNReal.toReal_rpow]
  rw [L0_silent_apply, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    L0_tall_real deg classPrior hdeg, L0_short_real deg classPrior hdeg]
  have hp : 0 < (classPrior c).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hm := mean_pos deg classPrior hdeg c
  have hm1 := mean_lt_one deg classPrior hdeg c
  have hq : 0 < (classPrior c).real {x} ^ α := Real.rpow_pos_of_pos hp α
  have hd := hdeg x
  rw [show deg x * (classPrior c).real {x} / mean deg classPrior c =
      deg x / mean deg classPrior c * (classPrior c).real {x} by ring,
    show (1 - deg x) * (classPrior c).real {x} / (1 - mean deg classPrior c) =
      (1 - deg x) / (1 - mean deg classPrior c) * (classPrior c).real {x} by ring,
    Real.mul_rpow (div_pos hd.1 hm).le hp.le,
    Real.mul_rpow (div_pos (by linarith) (by linarith)).le hp.le, share]
  rw [show (deg x / mean deg classPrior c) ^ α * (classPrior c).real {x} ^ α +
      ((1 - deg x) / (1 - mean deg classPrior c)) ^ α * (classPrior c).real {x} ^ α +
      (classPrior c).real {x} ^ α =
      ((deg x / mean deg classPrior c) ^ α + ((1 - deg x) / (1 - mean deg classPrior c)) ^ α + 1)
        * (classPrior c).real {x} ^ α by ring,
    mul_div_mul_right _ _ hq.ne']

/-- The speaker's share of *short* is the share of *tall* at the complementary degree and
mean. -/
theorem S_short_real (hα : 0 < α) (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass)
    {x : X} (hx : classPrior c {x} ≠ 0) :
    (S deg α classPrior c x).real {.short} =
      share α (1 - deg x) (1 - mean deg classPrior c) := by
  rw [S, speaker_real_singleton (cost := 1) (L := L0 deg classPrior c) hα.le
    (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one _ _ u _), sum_utterance]
  simp only [Pi.one_apply, ENNReal.toReal_one, mul_one, ← ENNReal.toReal_rpow]
  rw [L0_silent_apply, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    L0_tall_real deg classPrior hdeg, L0_short_real deg classPrior hdeg]
  have hp : 0 < (classPrior c).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hm := mean_pos deg classPrior hdeg c
  have hm1 := mean_lt_one deg classPrior hdeg c
  have hq : 0 < (classPrior c).real {x} ^ α := Real.rpow_pos_of_pos hp α
  have hd := hdeg x
  rw [show deg x * (classPrior c).real {x} / mean deg classPrior c =
      deg x / mean deg classPrior c * (classPrior c).real {x} by ring,
    show (1 - deg x) * (classPrior c).real {x} / (1 - mean deg classPrior c) =
      (1 - deg x) / (1 - mean deg classPrior c) * (classPrior c).real {x} by ring,
    Real.mul_rpow (div_pos hd.1 hm).le hp.le,
    Real.mul_rpow (div_pos (by linarith) (by linarith)).le hp.le, share,
    sub_sub_cancel, sub_sub_cancel]
  rw [show (deg x / mean deg classPrior c) ^ α * (classPrior c).real {x} ^ α +
      ((1 - deg x) / (1 - mean deg classPrior c)) ^ α * (classPrior c).real {x} ^ α +
      (classPrior c).real {x} ^ α =
      (((1 - deg x) / (1 - mean deg classPrior c)) ^ α + (deg x / mean deg classPrior c) ^ α + 1)
        * (classPrior c).real {x} ^ α by ring,
    mul_div_mul_right _ _ hq.ne']

/-- The share of the positive adjective falls as the class's mean rises: the adjective is the
more informative the lower the expectations it is measured against. -/
theorem share_lt_share (hα : 0 < α) {a m₁ m₂ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hm₁ : 0 < m₁)
    (h : m₁ < m₂) (hm₂ : m₂ < 1) : share α a m₂ < share α a m₁ := by
  unfold share
  have hm₂' : 0 < m₂ := hm₁.trans h
  have h1a : 0 < 1 - a := by linarith
  have h1m₁ : 0 < 1 - m₁ := by linarith
  have h1m₂ : 0 < 1 - m₂ := by linarith
  have hA : (a / m₂) ^ α < (a / m₁) ^ α :=
    Real.rpow_lt_rpow (div_pos ha hm₂').le (div_lt_div_of_pos_left ha hm₁ h) hα
  have hB : ((1 - a) / (1 - m₁)) ^ α < ((1 - a) / (1 - m₂)) ^ α :=
    Real.rpow_lt_rpow (div_pos h1a h1m₁).le (div_lt_div_of_pos_left h1a h1m₂ (by linarith)) hα
  have h0 : 0 < (a / m₂) ^ α := Real.rpow_pos_of_pos (div_pos ha hm₂') α
  have h0' : 0 < ((1 - a) / (1 - m₁)) ^ α := Real.rpow_pos_of_pos (div_pos h1a h1m₁) α
  have h1 : 0 < (a / m₁) ^ α := Real.rpow_pos_of_pos (div_pos ha hm₁) α
  have h1' : 0 < ((1 - a) / (1 - m₂)) ^ α := Real.rpow_pos_of_pos (div_pos h1a h1m₂) α
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_lt_mul'' hA hB h0.le h0'.le]

/-- At a full-support class prior every utterance has positive literal-listener mass. -/
theorem L0_apply_ne_zero (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (hsupp : ∀ c x, classPrior c {x} ≠ 0)
    (c : ComparisonClass) (u : Utterance) (x : X) : L0 deg classPrior c u {x} ≠ 0 := by
  rw [L0, literalListener_apply_singleton, ENNReal.div_ne_zero]
  refine ⟨mul_ne_zero ?_ (hsupp c x), ENNReal.sum_ne_top.2 λ _ _ =>
    ENNReal.mul_ne_top (measure_ne_top uniformThreshold _) (measure_ne_top _ _)⟩
  cases u with
  | tall => rw [meaning_tall deg (hdeg x).2.le]; exact (ENNReal.ofReal_pos.2 (hdeg x).1).ne'
  | short =>
    rw [meaning_short deg (hdeg x).1.le]
    exact (ENNReal.ofReal_pos.2 (by linarith [(hdeg x).2])).ne'
  | silent => rw [meaning_silent]; exact one_ne_zero

/-- Under full-support priors the speaker produces every utterance somewhere, so every
observation has positive marginal. -/
theorem comp_ne_zero [Nonempty X] (κ : Measure X) (hα : 0 < α)
    (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (hsupp : ∀ c x, classPrior c {x} ≠ 0)
    (hκ : ∀ x, κ {x} ≠ 0) (u : Utterance) :
    (familySpeaker (L0 deg classPrior) α 1 ∘ₘ κ.prod (uniformOn Set.univ)) {u} ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  refine comp_familySpeaker_ne_zero (w := x) (l := .subordinate) ?_
    (speaker_apply_singleton_ne_zero hα.le (λ _ => one_ne_zero) (λ _ => ENNReal.one_ne_top)
      (λ u' => literalListener_apply_le_one _ _ u' _)
      (L0_apply_ne_zero deg classPrior hdeg hsupp _ u x))
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  exact mul_ne_zero (hκ x) (uniformOn_univ_singleton_ne_zero _)

variable (κ : Measure X) [IsFiniteMeasure κ]

/-- Polarity by expectations, the positive adjective: hearing *tall*, the listener infers the
comparison class with the smaller mean degree, against which *tall* is the more informative. -/
theorem tall_infers_smaller_mean [Nonempty X] (hα : 0 < α) (hdeg : ∀ x, 0 < deg x ∧ deg x < 1)
    (hsupp : ∀ c x, classPrior c {x} ≠ 0) (hκ : ∀ x, κ {x} ≠ 0) {c₁ c₂ : ComparisonClass}
    (h : mean deg classPrior c₁ < mean deg classPrior c₂) :
    (L1 deg α classPrior κ .tall).snd.real {c₂} < (L1 deg α classPrior κ .tall).snd.real {c₁} := by
  rw [L1_snd_real_lt_iff deg classPrior κ (comp_ne_zero deg classPrior κ hα hdeg hsupp hκ .tall)]
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty λ x _ => ?_
  rw [S_tall_real deg classPrior hα hdeg c₁ (hsupp c₁ x),
    S_tall_real deg classPrior hα hdeg c₂ (hsupp c₂ x)]
  exact mul_lt_mul_of_pos_left (share_lt_share hα (hdeg x).1 (hdeg x).2
    (mean_pos deg classPrior hdeg c₁) h (mean_lt_one deg classPrior hdeg c₂))
    (ENNReal.toReal_pos (hκ x) (measure_ne_top _ _))

/-- Polarity by expectations, the negative adjective: hearing *short*, the listener infers the
comparison class with the larger mean degree. -/
theorem short_infers_larger_mean [Nonempty X] (hα : 0 < α) (hdeg : ∀ x, 0 < deg x ∧ deg x < 1)
    (hsupp : ∀ c x, classPrior c {x} ≠ 0) (hκ : ∀ x, κ {x} ≠ 0) {c₁ c₂ : ComparisonClass}
    (h : mean deg classPrior c₁ < mean deg classPrior c₂) :
    (L1 deg α classPrior κ .short).snd.real {c₁} <
      (L1 deg α classPrior κ .short).snd.real {c₂} := by
  rw [L1_snd_real_lt_iff deg classPrior κ (comp_ne_zero deg classPrior κ hα hdeg hsupp hκ .short)]
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty λ x _ => ?_
  rw [S_short_real deg classPrior hα hdeg c₁ (hsupp c₁ x),
    S_short_real deg classPrior hα hdeg c₂ (hsupp c₂ x)]
  refine mul_lt_mul_of_pos_left ?_ (ENNReal.toReal_pos (hκ x) (measure_ne_top _ _))
  exact share_lt_share hα (by linarith [(hdeg x).2]) (by linarith [(hdeg x).1])
    (by linarith [mean_lt_one deg classPrior hdeg c₂]) (by linarith)
    (by linarith [mean_pos deg classPrior hdeg c₁])

/-- A kind expected to be tall, such as basketball players, whose degrees exceed the
superordinate class's: *tall* is read against people and *short* against the kind
(Figure 1E). -/
theorem expected_tall [Nonempty X] (hα : 0 < α) (hdeg : ∀ x, 0 < deg x ∧ deg x < 1)
    (hsupp : ∀ c x, classPrior c {x} ≠ 0) (hκ : ∀ x, κ {x} ≠ 0)
    (h : mean deg classPrior .superordinate < mean deg classPrior .subordinate) :
    (L1 deg α classPrior κ .tall).snd.real {.subordinate} <
        (L1 deg α classPrior κ .tall).snd.real {.superordinate} ∧
      (L1 deg α classPrior κ .short).snd.real {.superordinate} <
        (L1 deg α classPrior κ .short).snd.real {.subordinate} :=
  ⟨tall_infers_smaller_mean deg classPrior κ hα hdeg hsupp hκ h,
    short_infers_larger_mean deg classPrior κ hα hdeg hsupp hκ h⟩

/-- A kind expected to be short, such as jockeys: *tall* is read against the kind and *short*
against people. -/
theorem expected_short [Nonempty X] (hα : 0 < α) (hdeg : ∀ x, 0 < deg x ∧ deg x < 1)
    (hsupp : ∀ c x, classPrior c {x} ≠ 0) (hκ : ∀ x, κ {x} ≠ 0)
    (h : mean deg classPrior .subordinate < mean deg classPrior .superordinate) :
    (L1 deg α classPrior κ .tall).snd.real {.superordinate} <
        (L1 deg α classPrior κ .tall).snd.real {.subordinate} ∧
      (L1 deg α classPrior κ .short).snd.real {.subordinate} <
        (L1 deg α classPrior κ .short).snd.real {.superordinate} :=
  ⟨tall_infers_smaller_mean deg classPrior κ hα hdeg hsupp hκ h,
    short_infers_larger_mean deg classPrior κ hα hdeg hsupp hκ h⟩

/-- The literal listener's score for *tall* is the class's mean degree. -/
theorem literalScore_tall (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) (c : ComparisonClass) :
    literalScore deg classPrior .tall c = mean deg classPrior c := by
  rw [literalScore, mean, expectedPrevalence_eq_sum]
  refine Finset.sum_congr rfl λ x _ => ?_
  rw [meaning_tall deg (hdeg x).2.le, ENNReal.toReal_ofReal (hdeg x).1.le]

/-- The literal listener (6) prefers, for *tall*, the class with the larger mean: the opposite
of the pragmatic inference (Figure 2). -/
theorem literalScore_tall_lt (hdeg : ∀ x, 0 < deg x ∧ deg x < 1) {c₁ c₂ : ComparisonClass}
    (h : mean deg classPrior c₁ < mean deg classPrior c₂) :
    literalScore deg classPrior .tall c₁ < literalScore deg classPrior .tall c₂ := by
  rwa [literalScore_tall deg classPrior hdeg, literalScore_tall deg classPrior hdeg]

end Model

end TesslerGoodman2022
