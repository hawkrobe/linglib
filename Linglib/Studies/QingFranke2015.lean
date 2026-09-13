import Linglib.Pragmatics.RSA.Basic
import Linglib.Core.Probability.Kernel.Posterior
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Qing and Franke (2015): Variations on a Bayesian Theme

This file formalizes [qing-franke-2015]'s family of models of the referential game of
[frank-goodman-2012], the rational speech act model decomposed along its design choices (§3):
the speaker's belief about the literal listener, a uniform prior or the empirically measured
salience prior; the speaker's goal, the belief-oriented log probability of the referent or the
action-oriented probability itself; a cost on adjectives (11); and for the listener, its own
prior and whether it acts on its posterior by a further soft maximization (14). The context is
the paper's Fig. 3, a square and a circle of one colour and a circle of the other. Speaker
preference is a threshold on the cost: the speakers that ignore salience prefer the unique word
at the two objects that have one for every cost within `log 2` of zero in the belief-oriented
and within `1/2` in the action-oriented model, bounds beyond the paper's cost support of
`(-0.4, 0.4)`, and prefer the noun at the object with both features shared exactly when nouns
are cheaper (`belief_blue_lt_iff`, `action_blue_lt_iff`, `belief_shared_lt_iff`), the majority
directions of Table 1; the salience-belief speaker's threshold at the blue circle,
`log (169 / 139)`, lies inside the support (`salience_blue_lt_iff`, `salience_threshold_lt`).
The uniform-prior listener follows pragmatic narrowing on both ambiguous words at every
rationality
(`uniform_listener_circle`, `uniform_listener_green`). The salience-prior listener that embeds
the original speaker follows salience on *circle* below a threshold on the embedded rationality
and narrowing on *green* only above one (`salience_listener_circle_iff`,
`salience_listener_green_iff`), the two directions of Table 2; at rationality one it mispredicts
*green* (`rsa_listener_green`), the model-side face of the paper's rejection of `λ = 1`, and it
matches both directions on a window of rationalities above one (`salience_listener_window`).
Acting on the posterior preserves its order (`actionListener_lt_iff`).

## Implementation notes

The speakers are score speakers over the literal listener's real mass, the action-oriented one
gated to true words as in the paper's fn. 13, and listeners are posteriors of a speaker against
a prior. Only the salience condition of Table 2 enters the models, as the salience prior; the
counts of Tables 1 and 2 are not restated, and the Bayesian model comparison of §5 is not
formalized.

## References

* [qing-franke-2015]
* [frank-goodman-2012]
-/

open MeasureTheory ProbabilityTheory RSA Real
open scoped ENNReal

namespace QingFranke2015

/-! ### The context (Fig. 3) -/

/-- The three objects: the square and the circle sharing a colour, and the circle of the other
colour. -/
inductive Object
  | greenSquare | greenCircle | blueCircle
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Object := ⊤
instance : DiscreteMeasurableSpace Object := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass Object := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The four words. -/
inductive Word
  | green | circle | square | blue
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass Word := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The word describes the object (Fig. 1b). -/
def Word.AppliesTo : Word → Object → Prop
  | .green, .greenSquare | .green, .greenCircle | .circle, .greenCircle | .circle, .blueCircle
  | .square, .greenSquare | .blue, .blueCircle => True
  | _, _ => False

instance : DecidableRel Word.AppliesTo := λ u t => by
  cases u <;> cases t <;> unfold Word.AppliesTo <;> infer_instance

/-- The extension of a word. -/
def Word.extension (u : Word) : Set Object := {t | u.AppliesTo t}

instance (u : Word) : DecidablePred (· ∈ u.extension) := λ t =>
  inferInstanceAs (Decidable (u.AppliesTo t))

/-- The cost (11): `c` on the colour adjectives, nothing on the shape nouns. -/
def Word.cost (c : ℝ) : Word → ℝ
  | .green | .blue => c
  | .circle | .square => 0

/-! ### Priors -/

/-- The prior determined by a weighting of the objects. -/
noncomputable def priorOf (w : Object → ℕ) : Measure Object :=
  ∑ t, (w t : ℝ≥0∞) • Measure.dirac t

@[simp] theorem priorOf_singleton (w : Object → ℕ) (t : Object) : priorOf w {t} = w t :=
  Measure.sum_smul_dirac_apply_singleton (λ t => (w t : ℝ≥0∞)) t

theorem priorOf_apply (w : Object → ℕ) (s : Set Object) [DecidablePred (· ∈ s)] :
    priorOf w s = ∑ t, if t ∈ s then (w t : ℝ≥0∞) else 0 := by
  simp only [priorOf, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_apply, Pi.one_apply, mul_ite,
    mul_one, mul_zero]

instance (w : Object → ℕ) : IsFiniteMeasure (priorOf w) :=
  ⟨by
    rw [priorOf_apply w Set.univ]
    exact ENNReal.sum_lt_top.mpr λ t _ => by simp⟩

/-- The uniform prior `U`. -/
noncomputable abbrev uniform : Measure Object := priorOf λ _ => 1

/-- The salience condition of Table 2, the paper's estimate of the salience prior `S`. -/
def salienceCount : Object → ℕ
  | .greenSquare => 71
  | .greenCircle => 30
  | .blueCircle => 139

/-- The salience prior. -/
noncomputable abbrev salience : Measure Object := priorOf salienceCount

/-! ### The literal listener and the speakers (§3) -/

/-- The literal listener at a prior (1): the prior conditioned on the word's extension. -/
noncomputable def L0 (μ : Measure Object) : Kernel Word Object :=
  literalListener μ λ u => u.extension.indicator 1

theorem L0_real_of_mem (w : Object → ℕ) {u : Word} {t : Object} (h : t ∈ u.extension) :
    (L0 (priorOf w) u).real {t} = (w t : ℝ) / (priorOf w u.extension).toReal := by
  rw [L0, measureReal_def, literalListener_indicator_apply_singleton _ _ h, ENNReal.toReal_mul,
    ENNReal.toReal_inv, priorOf_singleton, ENNReal.toReal_natCast, div_eq_inv_mul]

/-- The literal listener at the uniform prior: the reciprocal of the extension's size. -/
theorem L0_uniform_real_of_mem {u : Word} {t : Object} (h : t ∈ u.extension) :
    (L0 uniform u).real {t} = 1 / (Finset.univ.filter (· ∈ u.extension)).card := by
  rw [L0_real_of_mem _ h, priorOf_apply]
  simp only [Nat.cast_one]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, ENNReal.toReal_natCast]

/-- The literal listener at the salience prior conditions the salience counts. -/
theorem L0_salience_real_of_mem {u : Word} {t : Object} (h : t ∈ u.extension) :
    (L0 salience u).real {t} =
      (salienceCount t : ℝ) /
        ∑ t' ∈ Finset.univ.filter (· ∈ u.extension), (salienceCount t' : ℝ) := by
  rw [L0_real_of_mem _ h, priorOf_apply, ← Finset.sum_filter,
    ENNReal.toReal_sum λ _ _ => ENNReal.natCast_ne_top _]
  simp only [ENNReal.toReal_natCast]

/-- The speaker's goal: the belief-oriented log probability of the referent (10) or the
action-oriented probability itself (9). -/
inductive Goal
  | belief | action
  deriving DecidableEq, Repr

/-- The goal's measure of the literal listener's probability of the referent. -/
noncomputable def Goal.value : Goal → ℝ → ℝ
  | .belief => log
  | .action => id

/-- The utility of a word at an object: the goal's value of the literal listener's probability
less the cost, scaled by the rationality; a false word is never used (fn. 13). -/
noncomputable def score (g : Goal) (μ : Measure Object) (lam c : ℝ) (t : Object) (u : Word) :
    EReal :=
  if t ∈ u.extension then ((lam * (g.value ((L0 μ u).real {t}) - u.cost c) : ℝ) : EReal) else ⊥

/-- The speaker models `σ_xy` of (9) and (10): the score speaker at goal `x` and belief
prior `y`. -/
noncomputable def speaker (g : Goal) (μ : Measure Object) (lam c : ℝ) : Kernel Object Word :=
  speakerOfScore (score g μ lam c)

instance (g : Goal) (μ : Measure Object) (lam c : ℝ) : IsFiniteKernel (speaker g μ lam c) :=
  inferInstanceAs (IsFiniteKernel (speakerOfScore _))

theorem score_ne_top (g : Goal) (μ : Measure Object) (lam c : ℝ) (t : Object) (u : Word) :
    score g μ lam c t u ≠ ⊤ := by
  unfold score
  split
  · exact EReal.coe_ne_top _
  · exact bot_ne_top

theorem score_of_mem (g : Goal) (μ : Measure Object) (lam c : ℝ) {t : Object} {u : Word}
    (h : t ∈ u.extension) :
    score g μ lam c t u = ((lam * (g.value ((L0 μ u).real {t}) - u.cost c) : ℝ) : EReal) := by
  unfold score
  rw [if_pos h]

theorem score_ne_bot (g : Goal) (μ : Measure Object) (lam c : ℝ) {t : Object} {u : Word}
    (h : t ∈ u.extension) : score g μ lam c t u ≠ ⊥ := by
  rw [score_of_mem g μ lam c h]
  exact EReal.coe_ne_bot _

theorem score_of_notMem (g : Goal) (μ : Measure Object) (lam c : ℝ) {t : Object} {u : Word}
    (h : t ∉ u.extension) : score g μ lam c t u = ⊥ := by
  unfold score
  rw [if_neg h]

/-- Every object has a true word. -/
theorem exists_score_ne_bot (g : Goal) (μ : Measure Object) (lam c : ℝ) (t : Object) :
    ∃ u, score g μ lam c t u ≠ ⊥ := by
  cases t
  · exact ⟨.square, score_ne_bot g μ lam c (by decide)⟩
  · exact ⟨.circle, score_ne_bot g μ lam c (by decide)⟩
  · exact ⟨.blue, score_ne_bot g μ lam c (by decide)⟩

/-- Speaker preference at an object is utility comparison. -/
theorem speaker_lt_iff (g : Goal) (μ : Measure Object) (lam c : ℝ) (t : Object) (u u' : Word) :
    (speaker g μ lam c t).real {u} < (speaker g μ lam c t).real {u'} ↔
      score g μ lam c t u < score g μ lam c t u' :=
  speakerOfScore_real_singleton_lt_iff (score_ne_top g μ lam c t)
    (exists_score_ne_bot g μ lam c t)

/-- The share of a word at an object with two true words is the logistic function of the utility
difference. -/
theorem speaker_real_of_pair (g : Goal) (μ : Measure Object) (lam c : ℝ) {t : Object}
    {u u' : Word} (huu' : u ≠ u') (hu : t ∈ u.extension) (hu' : t ∈ u'.extension)
    (hsupp : ∀ v, t ∈ v.extension → v = u ∨ v = u') :
    (speaker g μ lam c t).real {u} =
      sigmoid ((score g μ lam c t u).toReal - (score g μ lam c t u').toReal) :=
  speakerOfScore_real_singleton_of_pair huu' (score_ne_bot g μ lam c hu)
    (score_ne_bot g μ lam c hu') (score_ne_top g μ lam c t)
    λ v hv => hsupp v (by
      by_contra h
      exact hv (score_of_notMem g μ lam c h))

/-! ### Speaker thresholds (Table 1) -/

section Uniform

private theorem l0u_half {u : Word} {t : Object} (h : t ∈ u.extension)
    (hc : (Finset.univ.filter (· ∈ u.extension)).card = 2) : (L0 uniform u).real {t} = 1 / 2 := by
  rw [L0_uniform_real_of_mem h, hc, Nat.cast_ofNat]

private theorem l0u_one {u : Word} {t : Object} (h : t ∈ u.extension)
    (hc : (Finset.univ.filter (· ∈ u.extension)).card = 1) : (L0 uniform u).real {t} = 1 := by
  rw [L0_uniform_real_of_mem h, hc, Nat.cast_one, div_one]

variable {lam c : ℝ}

/-- The belief-oriented speaker prefers the unique *blue* to the ambiguous *circle* at the blue
circle exactly when the adjective costs less than `log 2`. -/
theorem belief_blue_lt_iff (hlam : 0 < lam) :
    (speaker .belief uniform lam c .blueCircle).real {.circle}
      < (speaker .belief uniform lam c .blueCircle).real {.blue} ↔ c < log 2 := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0u_half (by decide) (by decide), l0u_one (by decide) (by decide), EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost, one_div, log_inv, log_one]
  constructor <;> intro h <;> nlinarith

/-- It prefers the unique *square* to *green* at the green square exactly when the adjective
costs more than `-log 2`. -/
theorem belief_square_lt_iff (hlam : 0 < lam) :
    (speaker .belief uniform lam c .greenSquare).real {.green}
      < (speaker .belief uniform lam c .greenSquare).real {.square} ↔ -log 2 < c := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0u_half (by decide) (by decide), l0u_one (by decide) (by decide), EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost, one_div, log_inv, log_one]
  constructor <;> intro h <;> nlinarith

/-- At the object with both features shared the two words are equally informative, and the
noun wins exactly when it is cheaper. -/
theorem belief_shared_lt_iff (hlam : 0 < lam) :
    (speaker .belief uniform lam c .greenCircle).real {.green}
      < (speaker .belief uniform lam c .greenCircle).real {.circle} ↔ 0 < c := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0u_half (by decide) (by decide), l0u_half (by decide) (by decide), EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost]
  constructor <;> intro h <;> nlinarith

/-- The action-oriented speaker's threshold at the blue circle is `1/2`. -/
theorem action_blue_lt_iff (hlam : 0 < lam) :
    (speaker .action uniform lam c .blueCircle).real {.circle}
      < (speaker .action uniform lam c .blueCircle).real {.blue} ↔ c < 1 / 2 := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0u_half (by decide) (by decide), l0u_one (by decide) (by decide), EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost, id]
  constructor <;> intro h <;> nlinarith

/-- Its threshold at the green square is `-1/2`. -/
theorem action_square_lt_iff (hlam : 0 < lam) :
    (speaker .action uniform lam c .greenSquare).real {.green}
      < (speaker .action uniform lam c .greenSquare).real {.square} ↔ -(1 / 2) < c := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0u_half (by decide) (by decide), l0u_one (by decide) (by decide), EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost, id]
  constructor <;> intro h <;> nlinarith

/-- At the shared object the action-oriented speaker too follows the sign of the cost. -/
theorem action_shared_lt_iff (hlam : 0 < lam) :
    (speaker .action uniform lam c .greenCircle).real {.green}
      < (speaker .action uniform lam c .greenCircle).real {.circle} ↔ 0 < c := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0u_half (by decide) (by decide), l0u_half (by decide) (by decide), EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost, id]
  constructor <;> intro h <;> nlinarith

end Uniform

/-- Both thresholds for the unique words lie beyond the paper's cost support `(-0.4, 0.4)`. -/
theorem support_lt_thresholds : (0.4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < log 2 :=
  ⟨by norm_num, by linarith [log_two_gt_d9]⟩

section Salience

private theorem l0s_circle_blueCircle :
    (L0 salience .circle).real {.blueCircle} = (169 / 139)⁻¹ := by
  rw [L0_salience_real_of_mem (by decide),
    show Finset.univ.filter (· ∈ Word.circle.extension) = {.greenCircle, .blueCircle} by decide,
    Finset.sum_pair (by decide)]
  simp only [salienceCount, Nat.cast_ofNat]
  norm_num

private theorem l0s_blue_blueCircle : (L0 salience .blue).real {.blueCircle} = 1 := by
  rw [L0_salience_real_of_mem (by decide),
    show Finset.univ.filter (· ∈ Word.blue.extension) = {.blueCircle} by decide,
    Finset.sum_singleton]
  simp only [salienceCount, Nat.cast_ofNat]
  norm_num

private theorem l0s_circle_greenCircle :
    (L0 salience .circle).real {.greenCircle} = 30 / 101 * (169 / 101)⁻¹ := by
  rw [L0_salience_real_of_mem (by decide),
    show Finset.univ.filter (· ∈ Word.circle.extension) = {.greenCircle, .blueCircle} by decide,
    Finset.sum_pair (by decide)]
  simp only [salienceCount, Nat.cast_ofNat]
  norm_num

private theorem l0s_green_greenCircle : (L0 salience .green).real {.greenCircle} = 30 / 101 := by
  rw [L0_salience_real_of_mem (by decide),
    show Finset.univ.filter (· ∈ Word.green.extension) = {.greenSquare, .greenCircle} by decide,
    Finset.sum_pair (by decide)]
  simp only [salienceCount, Nat.cast_ofNat]
  norm_num

variable {lam c : ℝ}

/-- The salience-belief speaker (7) prefers *blue* to *circle* at the blue circle exactly when the
adjective costs less than `log (169 / 139)`. -/
theorem salience_blue_lt_iff (hlam : 0 < lam) :
    (speaker .belief salience lam c .blueCircle).real {.circle}
      < (speaker .belief salience lam c .blueCircle).real {.blue} ↔ c < log (169 / 139) := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0s_circle_blueCircle, l0s_blue_blueCircle, EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost, log_inv, log_one]
  constructor <;> intro h <;> nlinarith

/-- At the shared object it prefers the adjective *green* for every cost below
`log (169 / 101)`, the whole of the paper's support. -/
theorem salience_shared_lt_iff (hlam : 0 < lam) :
    (speaker .belief salience lam c .greenCircle).real {.circle}
      < (speaker .belief salience lam c .greenCircle).real {.green} ↔ c < log (169 / 101) := by
  rw [speaker_lt_iff, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    l0s_circle_greenCircle, l0s_green_greenCircle, EReal.coe_lt_coe_iff]
  simp only [Goal.value, Word.cost]
  rw [log_mul (by norm_num) (by norm_num), log_inv]
  constructor <;> intro h <;> nlinarith

end Salience

/-- The salience-belief speaker's threshold lies inside the paper's cost support. -/
theorem salience_threshold_lt : log (169 / 139) < (0.4 : ℝ) := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  linarith [add_one_lt_exp (by norm_num : (0.4 : ℝ) ≠ 0)]

/-! ### Listeners (§3), (12) to (15) -/

/-- The belief-oriented listener (15): the posterior of a speaker against the listener's prior. -/
noncomputable def listener (ν : Measure Object) [IsFiniteMeasure ν] (σ : Kernel Object Word)
    [IsFiniteKernel σ] : Kernel Word Object :=
  σ†ν

/-- The action-oriented listener (14): the soft maximization of a posterior. -/
noncomputable def actionListener (lamL : ℝ) (ρ : Kernel Word Object) : Kernel Word Object :=
  speakerOfScore λ u t => ((lamL * (ρ u).real {t} : ℝ) : EReal)

/-- Acting on the posterior preserves its order. -/
theorem actionListener_lt_iff {lamL : ℝ} (hlamL : 0 < lamL) (ρ : Kernel Word Object) (u : Word)
    (t t' : Object) :
    (actionListener lamL ρ u).real {t} < (actionListener lamL ρ u).real {t'} ↔
      (ρ u).real {t} < (ρ u).real {t'} := by
  rw [actionListener, speakerOfScore_real_singleton_lt_iff
    (score := λ u t => ((lamL * (ρ u).real {t} : ℝ) : EReal)) (w := u)
    (λ _ => EReal.coe_ne_top _) ⟨t, EReal.coe_ne_bot _⟩, EReal.coe_lt_coe_iff]
  constructor <;> intro h <;> nlinarith

/-- Listener preference between two objects is prior-weighted speaker preference. -/
theorem listener_lt_iff (ν : Measure Object) [IsFiniteMeasure ν] (σ : Kernel Object Word)
    [IsFiniteKernel σ] {u : Word} (hu : (σ ∘ₘ ν) {u} ≠ 0) (t t' : Object) :
    (listener ν σ u).real {t} < (listener ν σ u).real {t'} ↔
      ν.real {t} * (σ t).real {u} < ν.real {t'} * (σ t').real {u} := by
  have h := posterior_real_finset_lt_iff σ ν hu {t} {t'}
  simp only [Finset.coe_singleton, Finset.sum_singleton] at h
  exact h

section BeliefUniform

variable {lam c : ℝ}

private theorem supp_blueCircle (v : Word) (hv : Object.blueCircle ∈ v.extension) :
    v = .circle ∨ v = .blue := by
  cases v <;> simp_all [Word.extension, Word.AppliesTo]

private theorem supp_greenCircle (v : Word) (hv : Object.greenCircle ∈ v.extension) :
    v = .green ∨ v = .circle := by
  cases v <;> simp_all [Word.extension, Word.AppliesTo]

private theorem supp_greenSquare (v : Word) (hv : Object.greenSquare ∈ v.extension) :
    v = .green ∨ v = .square := by
  cases v <;> simp_all [Word.extension, Word.AppliesTo]

/-- The share of *circle* at the blue circle under the original speaker. -/
theorem circle_at_blueCircle :
    (speaker .belief uniform lam c .blueCircle).real {.circle} = sigmoid (lam * (c - log 2)) := by
  rw [speaker_real_of_pair _ _ _ _ (u := .circle) (u' := .blue) (by decide) (by decide) (by decide)
      supp_blueCircle, score_of_mem _ _ _ _ (by decide), score_of_mem _ _ _ _ (by decide),
    EReal.toReal_coe, EReal.toReal_coe, l0u_half (by decide) (by decide),
    l0u_one (by decide) (by decide)]
  simp only [Goal.value, Word.cost, one_div, log_inv, log_one]
  ring_nf

/-- The share of *circle* at the green circle. -/
theorem circle_at_greenCircle :
    (speaker .belief uniform lam c .greenCircle).real {.circle} = sigmoid (lam * c) := by
  rw [speaker_real_of_pair _ _ _ _ (u := .circle) (u' := .green) (by decide) (by decide)
      (by decide) (λ v hv => (supp_greenCircle v hv).symm), score_of_mem _ _ _ _ (by decide),
    score_of_mem _ _ _ _ (by decide), EReal.toReal_coe, EReal.toReal_coe,
    l0u_half (by decide) (by decide), l0u_half (by decide) (by decide)]
  simp only [Goal.value, Word.cost]
  ring_nf

/-- The share of *green* at the green square. -/
theorem green_at_greenSquare :
    (speaker .belief uniform lam c .greenSquare).real {.green} =
      sigmoid (lam * (-log 2 - c)) := by
  rw [speaker_real_of_pair _ _ _ _ (u := .green) (u' := .square) (by decide) (by decide)
      (by decide) supp_greenSquare, score_of_mem _ _ _ _ (by decide),
    score_of_mem _ _ _ _ (by decide), EReal.toReal_coe, EReal.toReal_coe,
    l0u_half (by decide) (by decide), l0u_one (by decide) (by decide)]
  simp only [Goal.value, Word.cost, one_div, log_inv, log_one]
  ring_nf

/-- The share of *green* at the green circle. -/
theorem green_at_greenCircle :
    (speaker .belief uniform lam c .greenCircle).real {.green} = sigmoid (-(lam * c)) := by
  rw [speaker_real_of_pair _ _ _ _ (u := .green) (u' := .circle) (by decide) (by decide)
      (by decide) supp_greenCircle, score_of_mem _ _ _ _ (by decide),
    score_of_mem _ _ _ _ (by decide), EReal.toReal_coe, EReal.toReal_coe,
    l0u_half (by decide) (by decide), l0u_half (by decide) (by decide)]
  simp only [Goal.value, Word.cost]
  ring_nf

/-- Every word is heard with positive probability under the original speaker at any prior with
positive mass everywhere. -/
theorem comp_speaker_ne_zero (w : Object → ℕ) (hw : ∀ t, w t ≠ 0) (u : Word) :
    (speaker .belief uniform lam c ∘ₘ priorOf w) {u} ≠ 0 := by
  have key : ∀ t, t ∈ u.extension → (speaker .belief uniform lam c ∘ₘ priorOf w) {u} ≠ 0 :=
    λ t ht => comp_apply_singleton_ne_zero _ _ (by rw [priorOf_singleton]; exact_mod_cast hw t)
      (speakerOfScore_apply_singleton_ne_zero (score_ne_bot _ _ _ _ ht) (score_ne_top _ _ _ _ t))
  cases u
  · exact key .greenSquare (by decide)
  · exact key .greenCircle (by decide)
  · exact key .greenSquare (by decide)
  · exact key .blueCircle (by decide)

/-- The uniform-prior listener hearing *circle* prefers the green circle: a blue-circle speaker
had *blue*. -/
theorem uniform_listener_circle (hlam : 0 < lam) :
    (listener uniform (speaker .belief uniform lam c) .circle).real {.blueCircle}
      < (listener uniform (speaker .belief uniform lam c) .circle).real {.greenCircle} := by
  rw [listener_lt_iff _ _ (comp_speaker_ne_zero _ (λ _ => one_ne_zero) _), circle_at_blueCircle,
    circle_at_greenCircle, measureReal_def, measureReal_def, priorOf_singleton, priorOf_singleton]
  simp only [Nat.cast_one, ENNReal.toReal_one, one_mul]
  exact sigmoid_lt (by nlinarith [log_pos (by norm_num : (1 : ℝ) < 2)])

/-- Hearing *green* it prefers the green circle: a green-square speaker had *square*. -/
theorem uniform_listener_green (hlam : 0 < lam) :
    (listener uniform (speaker .belief uniform lam c) .green).real {.greenSquare}
      < (listener uniform (speaker .belief uniform lam c) .green).real {.greenCircle} := by
  rw [listener_lt_iff _ _ (comp_speaker_ne_zero _ (λ _ => one_ne_zero) _), green_at_greenSquare,
    green_at_greenCircle, measureReal_def, measureReal_def, priorOf_singleton, priorOf_singleton]
  simp only [Nat.cast_one, ENNReal.toReal_one, one_mul]
  exact sigmoid_lt (by nlinarith [log_pos (by norm_num : (1 : ℝ) < 2)])

private theorem exp_shift (lam c : ℝ) :
    exp (-(lam * (c - log 2))) = exp (-(lam * c)) * (2 : ℝ) ^ lam := by
  rw [rpow_def_of_pos (by norm_num), ← exp_add]
  congr 1
  ring

private theorem exp_shift' (lam c : ℝ) :
    exp (-(lam * (-log 2 - c))) = exp (lam * c) * (2 : ℝ) ^ lam := by
  rw [rpow_def_of_pos (by norm_num), ← exp_add]
  congr 1
  ring

/-- The salience-prior listener hearing *circle* prefers the salient blue circle, the direction of
Table 2, exactly when `30 (1 + e^{-λc} 2^λ) < 139 (1 + e^{-λc})`. -/
theorem salience_listener_circle_iff :
    (listener salience (speaker .belief uniform lam c) .circle).real {.greenCircle}
      < (listener salience (speaker .belief uniform lam c) .circle).real {.blueCircle} ↔
      30 * (1 + exp (-(lam * c)) * (2 : ℝ) ^ lam) < 139 * (1 + exp (-(lam * c))) := by
  rw [listener_lt_iff _ _ (comp_speaker_ne_zero _ (by decide) _), circle_at_blueCircle,
    circle_at_greenCircle, measureReal_def, measureReal_def, priorOf_singleton, priorOf_singleton]
  simp only [salienceCount, Nat.cast_ofNat, ENNReal.toReal_ofNat, sigmoid_def, exp_shift]
  have hx := exp_pos (-(lam * c))
  have hy : (0 : ℝ) < (2 : ℝ) ^ lam := rpow_pos_of_pos (by norm_num) _
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) (by positivity)]

/-- Hearing *green* it prefers the green circle, again the direction of Table 2, exactly when
`71 (1 + e^{λc}) < 30 (1 + e^{λc} 2^λ)`. -/
theorem salience_listener_green_iff :
    (listener salience (speaker .belief uniform lam c) .green).real {.greenSquare}
      < (listener salience (speaker .belief uniform lam c) .green).real {.greenCircle} ↔
      71 * (1 + exp (lam * c)) < 30 * (1 + exp (lam * c) * (2 : ℝ) ^ lam) := by
  rw [listener_lt_iff _ _ (comp_speaker_ne_zero _ (by decide) _), green_at_greenSquare,
    green_at_greenCircle, measureReal_def, measureReal_def, priorOf_singleton, priorOf_singleton]
  simp only [salienceCount, Nat.cast_ofNat, ENNReal.toReal_ofNat, sigmoid_def, exp_shift',
    neg_neg]
  have hx := exp_pos (lam * c)
  have hy : (0 : ℝ) < (2 : ℝ) ^ lam := rpow_pos_of_pos (by norm_num) _
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) (by positivity)]

end BeliefUniform

/-- The original model `ρ_bS(σ_bU)` at rationality one and no cost mispredicts *green*: the
salient green square wins. -/
theorem rsa_listener_green :
    ¬ (listener salience (speaker .belief uniform 1 0) .green).real {.greenSquare}
      < (listener salience (speaker .belief uniform 1 0) .green).real {.greenCircle} := by
  rw [salience_listener_green_iff]
  norm_num

/-- Without cost, the salience listener matches both directions of Table 2 exactly on the window
`112/30 < 2^λ < 248/30` of embedded rationalities. -/
theorem salience_listener_window (lam : ℝ) :
    ((listener salience (speaker .belief uniform lam 0) .circle).real {.greenCircle}
        < (listener salience (speaker .belief uniform lam 0) .circle).real {.blueCircle} ∧
      (listener salience (speaker .belief uniform lam 0) .green).real {.greenSquare}
        < (listener salience (speaker .belief uniform lam 0) .green).real {.greenCircle}) ↔
      112 / 30 < (2 : ℝ) ^ lam ∧ (2 : ℝ) ^ lam < 248 / 30 := by
  rw [salience_listener_circle_iff, salience_listener_green_iff]
  simp only [mul_zero, neg_zero, exp_zero, one_mul]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end QingFranke2015
