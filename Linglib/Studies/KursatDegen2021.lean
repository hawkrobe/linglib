import Linglib.Studies.DegenEtAl2020
import Linglib.Pragmatics.RSA.Uniform

/-!
# Kursat and Degen (2021): Perceptual Difficulty and Redundant Modification

This file formalizes the Perceptual Difficulty Hypothesis of [kursat-degen-2021]: the noise
attached to an adjective in the continuous-semantics model of [degen-etal-2020] reflects how
hard it is to verify that an object has the property, so that harder properties are mentioned
redundantly less often. The critical display of Experiment 2 is modelled as the paper describes
it, a target, a competitor sharing the redundant property, and two distractors sharing the
sufficient property with the competitor, with one noise channel per property. The speaker of
[degen-etal-2020] prefers the redundant expression exactly when the redundant property's channel
exceeds one half, whatever the sufficient property's channel (`redundant_preferred_iff`), so a
material channel at or below one half and a colour channel above it yield redundant colour where
material suffices and no redundant material where colour suffices
(`perceptual_difficulty_asymmetry`).

The reported effects of the three experiments are recorded as `Effect`s: material adjectives
are verified less accurately and more slowly than colour adjectives, in isolation and in the
production displays (`material_harder`); colour is mentioned redundantly more often than
material (`color_more_redundant`); and perceptual difficulty within a property type does not
predict redundancy, so only the weak version of the hypothesis is supported
(`strong_version_unsupported`).

## Implementation notes

The model reuses the noise channel of [degen-etal-2020]. The scene is abstracted to the roles
of its two properties, so a colour-redundant trial and a material-redundant trial are the same
model with the channels swapped. Coefficients are the paper's, as printed; the response-time
coefficient of Experiment 1 is printed with a standard error inconsistent with its
t-statistic. Where the paper reports a p-value only as a bound, `Effect.p` records the bound.

## References

* [kursat-degen-2021]
* [degen-etal-2020]
-/

namespace KursatDegen2021

open MeasureTheory ProbabilityTheory RSA
open DegenEtAl2020 (channel channel_nonneg)
open scoped ENNReal

/-! ### The critical display of Experiment 2 -/

/-- The four objects of a critical trial: the target, the competitor sharing the redundant
property with it, and two distractors sharing the sufficient property with the competitor. -/
inductive World where
  | target
  | competitor
  | distractor₁
  | distractor₂
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨λ _ => trivial⟩

/-- Whether an object has the target's sufficient property. -/
def World.hasSufficient : World → Bool
  | .target => true
  | .competitor | .distractor₁ | .distractor₂ => false

/-- Whether an object has the target's redundant property. -/
def World.hasRedundant : World → Bool
  | .target | .competitor => true
  | .distractor₁ | .distractor₂ => false

/-- The two referring expressions: the sufficient adjective alone, or both adjectives. -/
inductive Utterance where
  | sufficient
  | redundant
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩

/-- The continuous meaning with channel `xs` for the sufficient property and `xr` for the
redundant one: each mentioned adjective holds of an object to degree `x` when it matches and
`1 − x` when it does not. -/
def meaning (xs xr : ℝ) : Utterance → World → ℝ
  | .sufficient, w => channel xs (some true) w.hasSufficient
  | .redundant, w => channel xs (some true) w.hasSufficient * channel xr (some true) w.hasRedundant

section Model

variable {xs xr : ℝ}

theorem meaning_nonneg (hs0 : 0 ≤ xs) (hs1 : xs ≤ 1) (hr0 : 0 ≤ xr) (hr1 : xr ≤ 1)
    (u : Utterance) (w : World) : 0 ≤ meaning xs xr u w := by
  cases u <;> simp only [meaning]
  · exact channel_nonneg hs0 hs1 _ _
  · exact mul_nonneg (channel_nonneg hs0 hs1 _ _) (channel_nonneg hr0 hr1 _ _)

/-- The literal listener: the meaning normalized over the display at a uniform prior. -/
noncomputable def L0 (xs xr : ℝ) : Kernel Utterance World :=
  literalListener (uniformOn Set.univ) λ u w => ENNReal.ofReal (meaning xs xr u w)

/-- The speaker with unit informativeness weight and no cost. -/
noncomputable def S1 (xs xr : ℝ) : Kernel World Utterance := speaker 1 1 (L0 xs xr)

private theorem sum_world (f : World → ℝ) :
    ∑ w, f w = f .target + f .competitor + f .distractor₁ + f .distractor₂ := by
  rw [show (Finset.univ : Finset World) =
      {.target, .competitor, .distractor₁, .distractor₂} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem row_sufficient : ∑ w, meaning xs xr .sufficient w = 3 - 2 * xs := by
  rw [sum_world]
  simp [meaning, channel, World.hasSufficient]
  ring

private theorem row_redundant :
    ∑ w, meaning xs xr .redundant w = xr + 2 * (1 - xs) * (1 - xr) := by
  rw [sum_world]
  simp [meaning, channel, World.hasSufficient, World.hasRedundant]
  ring

/-- The redundant expression is preferred for the target exactly when the redundant property's
channel exceeds one half, whatever the sufficient property's channel short of Boolean. -/
theorem redundant_preferred_iff (hs0 : 0 < xs) (hs1 : xs < 1) (hr0 : 0 < xr) (hr1 : xr ≤ 1) :
    (S1 xs xr .target).real {.sufficient} < (S1 xs xr .target).real {.redundant} ↔ 1/2 < xr := by
  have hnn := meaning_nonneg hs0.le hs1.le hr0.le hr1
  have hsuf : 0 < 3 - 2 * xs := by linarith
  have hred : 0 < xr + 2 * (1 - xs) * (1 - xr) := by nlinarith
  have h1 := literalListener_uniformOn_ofReal_apply_singleton (meaning xs xr) .sufficient
    World.target (hnn _) (by rw [row_sufficient]; exact hsuf)
  have h2 := literalListener_uniformOn_ofReal_apply_singleton (meaning xs xr) .redundant
    World.target (hnn _) (by rw [row_redundant]; exact hred)
  have hm1 : meaning xs xr .sufficient .target = xs := by
    simp [meaning, channel, World.hasSufficient]
  have hm2 : meaning xs xr .redundant .target = xs * xr := by
    simp [meaning, channel, World.hasSufficient, World.hasRedundant]
  rw [S1]
  refine (speaker_real_singleton_lt_iff (cost := 1) (L := L0 xs xr) (w := World.target)
    zero_le_one (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one _ _ u _)
    ⟨.redundant, ?_⟩).trans ?_
  · rw [ENNReal.rpow_one, Pi.one_apply, mul_one, L0, h2, row_redundant, hm2]
    exact (ENNReal.ofReal_pos.mpr (div_pos (mul_pos hs0 hr0) hred)).ne'
  · simp only [ENNReal.rpow_one, Pi.one_apply, mul_one, L0]
    rw [h1, h2, row_sufficient, row_redundant, hm1, hm2,
      ENNReal.ofReal_lt_ofReal_iff (div_pos (mul_pos hs0 hr0) hred), div_lt_div_iff₀ hsuf hred]
    have hk : 0 < xs * (1 - xs) := mul_pos hs0 (by linarith)
    constructor <;> intro h <;> nlinarith [hk]

end Model

/-- The Perceptual Difficulty Hypothesis in the model: with the material channel at or below
one half and the colour channel above it, redundant colour is preferred where material suffices
and redundant material is dispreferred where colour suffices. -/
theorem perceptual_difficulty_asymmetry {xm xc : ℝ} (hm0 : 0 < xm) (hm : xm ≤ 1/2)
    (hc : 1/2 < xc) (hc1 : xc < 1) :
    (S1 xm xc .target).real {.sufficient} < (S1 xm xc .target).real {.redundant} ∧
      ¬ (S1 xc xm .target).real {.sufficient} < (S1 xc xm .target).real {.redundant} :=
  ⟨(redundant_preferred_iff hm0 (by linarith) (by linarith) hc1.le).2 hc,
   λ h => absurd ((redundant_preferred_iff (by linarith) hc1 hm0 (by linarith)).1 h) (not_lt.2 hm)⟩

/-! ### The reported effects -/

/-- A fixed effect as the paper reports it: coefficient, standard error, and the p-value or its
reported bound. -/
structure Effect where
  /-- The coefficient. -/
  beta : ℚ
  /-- The standard error. -/
  se : ℚ
  /-- The p-value, or its reported upper bound. -/
  p : ℚ

/-- Experiment 1: the log odds of an error, material against colour. -/
def exp1Error : Effect := ⟨48/100, 12/100, 1/10000⟩

/-- Experiment 1: response time, material against colour, as printed. -/
def exp1RT : Effect := ⟨544/100, 474/100, 1/10000⟩

/-- Experiment 2: the log odds of redundant mention, colour against material. -/
def exp2Redundancy : Effect := ⟨232/100, 64/100, 1/10000⟩

/-- Experiment 3: the log odds of an error, material against colour. -/
def exp3Error : Effect := ⟨96/100, 9/100, 1/10000⟩

/-- Experiment 3: log response time, material against colour. -/
def exp3RT : Effect := ⟨24/100, 18/1000, 1/10000⟩

/-- Experiment 3: residualized perceptual difficulty as a predictor of redundancy. -/
def withinDifficulty : Effect := ⟨-113/10, 1641/100, 49/100⟩

/-- Experiment 3: the interaction of property type with residualized difficulty. -/
def withinInteraction : Effect := ⟨1357/100, 3187/100, 67/100⟩

/-- Experiment 3: the residualized log ratio of sufficient to redundant response time. -/
def withinLogRatio : Effect := ⟨531/100, 387/100, 17/100⟩

/-- Material is harder to verify than colour: more errors and longer response times, in
isolation and in the production displays. -/
theorem material_harder :
    0 < exp1Error.beta ∧ 0 < exp1RT.beta ∧ 0 < exp3Error.beta ∧ 0 < exp3RT.beta := by
  norm_num [exp1Error, exp1RT, exp3Error, exp3RT]

/-- Colour is mentioned redundantly more often than material. -/
theorem color_more_redundant : 0 < exp2Redundancy.beta := by
  norm_num [exp2Redundancy]

/-- The strong version of the hypothesis, difficulty predicting redundancy within a property
type, finds no support: none of the three within-property tests reaches significance. -/
theorem strong_version_unsupported :
    1/20 < withinDifficulty.p ∧ 1/20 < withinInteraction.p ∧ 1/20 < withinLogRatio.p := by
  norm_num [withinDifficulty, withinInteraction, withinLogRatio]

end KursatDegen2021
