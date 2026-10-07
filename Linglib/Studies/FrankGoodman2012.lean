module

public import Linglib.Pragmatics.RSA.Basic

/-!
# Frank and Goodman (2012): Predicting Pragmatic Reasoning in Language Games

This file formalizes Frank and Goodman's rational speech act model at the paper's stimulus: three
objects, a blue square, a blue circle and a green square, described by the four words *blue*,
*green*, *square* and *circle*. A word applies to the objects it describes (`Feature.AppliesTo`).
The literal listener hears a word as the uniform distribution over the objects it applies to
(`literal`), and a speaker who wants to refer to an object chooses a word in proportion to the
literal listener's probability of the object, the reciprocal of the number of objects the word
applies to (the paper's second equation, `speaker`). The speaker is the substrate's `RSA.speaker`, a
score speaker at the informativity utility, and so inherits its characterization as the rational
optimizer (`RSA.isGreatest_freeEnergy_speakerOfScore`). At the stimulus the speaker prefers the word
with the smaller extension wherever both apply (`size_principle`), so it prefers the uniquely
identifying *circle* to the ambiguous *blue* for the blue circle, with all its mass in the limit of
full rationality (`prefers_informative`, `fully_rational_picks_circle`); it uses an ambiguous word
less at an object that a unique word identifies (`narrowing_blue`, `narrowing_square`), and never
uses a word where it does not apply (`unique_green`, `unique_circle`). These asymmetries are what
the paper's listener, the Bayesian posterior of the speaker against the empirically measured
salience prior (its first equation), inverts; the paper reports the fit of speaker and listener bets
to the model's predictions.

## Implementation notes

* The paper's speaker has rationality one and costless words; the findings are stated at every
  positive rationality.
* The literal listener conditions the counting measure on the extension, the uniform prior over
  the objects.
* The listener of the paper's first equation is `RSA.pragmaticListener` against a salience prior;
  its predictions at the stimulus are not instantiated here.

## TODO

* The listener on hearing *blue*: its odds for the blue square against the blue circle are the
  prior odds times three halves, the ratio of the speaker's probabilities of *blue* at the two
  objects.

## References

* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace FrankGoodman2012

/-! ### The stimulus (Figure 1A) -/

/-- The three objects of the context. -/
inductive Object
  | blueSquare | blueCircle | greenSquare
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The four words. -/
inductive Feature
  | blue | green | square | circle
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Object := ⊤
instance : DiscreteMeasurableSpace Object := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Feature := ⊤
instance : DiscreteMeasurableSpace Feature := ⟨fun _ ↦ trivial⟩

/-- The word describes the object. -/
def Feature.AppliesTo : Feature → Object → Prop
  | .blue, .blueSquare | .blue, .blueCircle | .green, .greenSquare
  | .square, .blueSquare | .square, .greenSquare | .circle, .blueCircle => True
  | _, _ => False

instance : DecidableRel Feature.AppliesTo := fun w o ↦ by
  cases w <;> cases o <;> unfold Feature.AppliesTo <;> infer_instance

/-- The extension of a word, the objects it applies to; its size is the paper's `|w|`. -/
def Feature.extension (w : Feature) : Finset Object := Finset.univ.filter w.AppliesTo

/-- On hearing a word, the literal listener is uniform over its extension. -/
noncomputable def literal : Kernel Feature Object :=
  RSA.literalListener Measure.count fun w ↦ (↑w.extension : Set Object).indicator 1

instance : IsFiniteKernel literal := inferInstanceAs (IsFiniteKernel (RSA.literalListener _ _))

/-- The speaker at rationality `α` and no cost is `S₁(w | r) ∝ L₀(r | w) ^ α`, the paper's
second equation at `α = 1`. -/
noncomputable def speaker (α : ℝ) : Kernel Object Feature := RSA.speaker α 0 literal

theorem mem_extension {w : Feature} {r : Object} :
    r ∈ (↑w.extension : Set Object) ↔ w.AppliesTo r := by
  simp [Feature.extension]

/-- The literal listener gives an object the reciprocal of the size of the word's extension. -/
theorem literal_apply_singleton (w : Feature) (r : Object) :
    literal w {r} = if w.AppliesTo r then (w.extension.card : ℝ≥0∞)⁻¹ else 0 := by
  split_ifs with h
  · rw [literal, RSA.literalListener_indicator_apply_singleton Measure.count
      (fun w : Feature ↦ (↑w.extension : Set Object)) (mem_extension.2 h),
      Measure.count_apply_finset, Measure.count_singleton, mul_one]
  · exact RSA.literalListener_indicator_apply_singleton_of_notMem Measure.count
      (fun w : Feature ↦ (↑w.extension : Set Object)) (mt mem_extension.1 h)

/-! ### Predictions -/

/-- By the size principle, of two words that apply to an object the speaker prefers the one with
the smaller extension. -/
theorem size_principle {α : ℝ} (hα : 0 < α) {r : Object} {w₁ w₂ : Feature} (h₁ : w₁.AppliesTo r)
    (h₂ : w₂.AppliesTo r) :
    (speaker α r).real {w₁} < (speaker α r).real {w₂} ↔ w₂.extension.card < w₁.extension.card := by
  refine (RSA.speaker_literalListener_indicator_real_singleton_lt_iff hα 0 Measure.count
    (fun w : Feature ↦ (↑w.extension : Set Object)) (by simp) (mem_extension.2 h₁)
    (mem_extension.2 h₂)).trans ?_
  rw [Measure.count_apply_finset, Measure.count_apply_finset, Nat.cast_lt]

/-- For the blue circle the speaker prefers *circle*, which identifies it, to the ambiguous
*blue*. -/
theorem prefers_informative {α : ℝ} (hα : 0 < α) :
    (speaker α .blueCircle).real {.blue} < (speaker α .blueCircle).real {.circle} :=
  (size_principle hα (by decide) (by decide)).2 (by decide)

/-- As rationality grows without bound the speaker puts all its mass on *circle*. -/
theorem fully_rational_picks_circle :
    Filter.Tendsto (fun α ↦ (speaker α .blueCircle).real {.circle}) Filter.atTop (𝓝 1) := by
  refine RSA.tendsto_speaker_real_singleton_atTop ?_ fun u hu ↦ ?_
  · rw [literal_apply_singleton, ite_eq_left (by decide)]
    simp [show Feature.circle.extension.card = 1 from by decide]
  · simp only [Pi.zero_apply, neg_zero, Real.exp_zero, mul_one]
    rw [literal_apply_singleton, literal_apply_singleton,
      ite_eq_left (by decide : Feature.circle.AppliesTo _),
      show Feature.circle.extension.card = 1 from by decide]
    cases u
    · rw [ite_eq_left (by decide), show Feature.blue.extension.card = 2 from by decide]
      norm_num
    · rw [ite_eq_right (by decide)]; norm_num
    · rw [ite_eq_right (by decide)]; norm_num
    · exact absurd rfl hu

/-- On reals, the speaker's probability of a word at an object is the literal listener's
probability raised to the rationality, over its total across the words. -/
theorem speaker_real_singleton {α : ℝ} (hα : 0 ≤ α) (r : Object) (w : Feature) :
    (speaker α r).real {w} = (literal w {r} ^ α).toReal / ∑ v, (literal v {r} ^ α).toReal :=
  RSA.speaker_zero_real_singleton hα w

private theorem univ_feature : (Finset.univ : Finset Feature) = {.blue, .green, .square, .circle} :=
  by decide

/-- *Blue* is used less for the blue circle, where *circle* competes, than for the blue square,
where the only competitor is as ambiguous, so a listener hearing *blue* narrows toward the blue
square. -/
theorem narrowing_blue {α : ℝ} (hα : 0 < α) :
    (speaker α .blueCircle).real {.blue} < (speaker α .blueSquare).real {.blue} := by
  set x : ℝ := ((2 : ℝ≥0∞)⁻¹ ^ α).toReal
  have hx0 : 0 < x := ENNReal.toReal_pos (by simp) (ENNReal.rpow_ne_top_of_nonneg hα.le (by simp))
  have hx1 : x < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top
      (ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) hα)
  have h2 : Feature.blue.extension.card = 2 := by decide
  have h2' : Feature.square.extension.card = 2 := by decide
  have h1 : Feature.circle.extension.card = 1 := by decide
  rw [speaker_real_singleton hα.le, speaker_real_singleton hα.le, univ_feature]
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, literal_apply_singleton, h1, h2, h2']
  simp [ENNReal.zero_rpow_of_pos hα, Feature.AppliesTo]
  rw [div_lt_div_iff_of_pos_left hx0 (by positivity) (by positivity)]
  linarith

/-- *Square* is likewise used less for the green square, which *green* identifies. -/
theorem narrowing_square {α : ℝ} (hα : 0 < α) :
    (speaker α .greenSquare).real {.square} < (speaker α .blueSquare).real {.square} := by
  set x : ℝ := ((2 : ℝ≥0∞)⁻¹ ^ α).toReal
  have hx0 : 0 < x := ENNReal.toReal_pos (by simp) (ENNReal.rpow_ne_top_of_nonneg hα.le (by simp))
  have hx1 : x < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top
      (ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) hα)
  have h2 : Feature.blue.extension.card = 2 := by decide
  have h2' : Feature.square.extension.card = 2 := by decide
  have h1 : Feature.green.extension.card = 1 := by decide
  rw [speaker_real_singleton hα.le, speaker_real_singleton hα.le, univ_feature]
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, literal_apply_singleton, h1, h2, h2']
  simp [ENNReal.zero_rpow_of_pos hα, Feature.AppliesTo]
  rw [div_lt_div_iff_of_pos_left hx0 (by positivity) (by positivity)]
  linarith

/-- A word that does not apply is never used, and one that does is used with positive
probability. -/
private theorem unique {α : ℝ} (hα : 0 < α) {w : Feature} {r r' : Object}
    (hr : ¬ w.AppliesTo r) (hr' : w.AppliesTo r') :
    (speaker α r).real {w} < (speaker α r').real {w} := by
  rw [measureReal_def, measureReal_def, speaker,
    RSA.speaker_apply_singleton_eq_zero hα (by rw [literal_apply_singleton, ite_eq_right hr]),
    ENNReal.toReal_zero]
  refine ENNReal.toReal_pos (RSA.speaker_apply_singleton_ne_zero hα.le ?_) (measure_ne_top _ _)
  rw [literal_apply_singleton, ite_eq_left hr']
  simp

/-- *Green* is never used for the blue square and is used for the green square, so a listener
hearing it identifies the green square. -/
theorem unique_green {α : ℝ} (hα : 0 < α) :
    (speaker α .blueSquare).real {.green} < (speaker α .greenSquare).real {.green} :=
  unique hα (by decide) (by decide)

/-- Unique reference for *circle*. -/
theorem unique_circle {α : ℝ} (hα : 0 < α) :
    (speaker α .blueSquare).real {.circle} < (speaker α .blueCircle).real {.circle} :=
  unique hα (by decide) (by decide)

end FrankGoodman2012
