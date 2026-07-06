import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rescorla-Wagner associative learning
[rescorla-wagner-1972] [ellis-2006] [cheng-holyoak-1995]

Error-driven associative learning: on each trial every present cue's strength
is updated by `ΔV_c = α_c · β · (λ − ΣV)`. The shared prediction-error term
makes learning competitive across cues.

## Main declarations

* `RescorlaWagner`, `RescorlaWagner.update`, `RescorlaWagner.iterateConst`.
* `RescorlaWagner.totalStrength_convergence`: total strength converges to `λ`.
* `RescorlaWagner.proportional_partition`, `RescorlaWagner.overshadowing`,
  `RescorlaWagner.blocking`, `RescorlaWagner.blocked_cue_zero`: the
  salience-proportional equilibrium and the blocking/overshadowing predictions
  ([ellis-2006] applies both to second-language acquisition).

The real-valued generalization of the rule is `Core.Learning.WidrowHoff`.
-/

namespace Core

open Finset Filter

section RescorlaWagner

/-- The Rescorla-Wagner learning model ([rescorla-wagner-1972]): on each
trial every present cue has its associative strength updated by

    ΔV_c = α_c · β · (λ − ΣV)

where `α_c` is cue salience, `β` the learning rate (outcome importance), `λ` the
maximum conditioning supported by the outcome, and `ΣV` the summed strength of
the cues present on the trial. The prediction-error term `(λ − ΣV)` is what makes
learning competitive across cues. -/
structure RescorlaWagner (C : Type*) where
  /-- Cue salience: how noticeable each cue is. Must be in [0, 1]. -/
  salience : C → ℝ
  /-- Learning rate (outcome importance). Must be in (0, 1]. -/
  learnRate : ℝ
  /-- Maximum conditioning supported by the outcome. -/
  maxCond : ℝ
  /-- Salience is non-negative. -/
  salience_nonneg : ∀ (c : C), 0 ≤ salience c
  /-- Salience is at most 1. -/
  salience_le_one : ∀ (c : C), salience c ≤ 1
  /-- Learning rate is strictly positive. -/
  learnRate_pos : 0 < learnRate
  /-- Learning rate is at most 1. -/
  learnRate_le_one : learnRate ≤ 1
  /-- Maximum conditioning is non-negative. -/
  maxCond_nonneg : 0 ≤ maxCond

variable {C : Type*} [DecidableEq C]

/-- Prediction error on a trial: `λ − ΣV` for cues present.

When positive, the outcome is under-predicted (surprise → learning).
When zero, the outcome is fully predicted (no learning).
When negative, the outcome is over-predicted (extinction). -/
def RescorlaWagner.predictionError (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) : ℝ :=
  rw.maxCond - ∑ c ∈ present, V c

/-- One trial of Rescorla-Wagner learning ([rescorla-wagner-1972]).

For each cue c:
- If c is present: `V'(c) = V(c) + α_c · β · (λ − ΣV)`
- If c is absent: `V'(c) = V(c)` (no change) -/
def RescorlaWagner.update (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (c : C) : ℝ :=
  if c ∈ present then
    V c + rw.salience c * rw.learnRate * rw.predictionError present V
  else V c

/-- Absent cues are not updated. -/
theorem RescorlaWagner.update_absent (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (c : C) (hc : c ∉ present) :
    rw.update present V c = V c := by
  simp only [update, if_neg hc]

/-- **Blocking theorem** ([rescorla-wagner-1972]; [ellis-2006]):
when cue A already fully predicts the outcome (`V(A) = λ`) and is the only cue
with nonzero strength among those present, adding a novel cue B to the compound
produces *zero learning* for B: `V'(B) = V(B)`. -/
theorem RescorlaWagner.blocking (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (B : C)
    (hB : B ∈ present)
    (h_total : ∑ c ∈ present, V c = rw.maxCond) :
    rw.update present V B = V B := by
  simp only [update, if_pos hB, predictionError, h_total, sub_self,
    mul_zero, add_zero]

/-- When the outcome is fully predicted, *no* present cue learns anything. -/
theorem RescorlaWagner.no_learning_at_equilibrium (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ)
    (h_total : ∑ c ∈ present, V c = rw.maxCond) (c : C) :
    rw.update present V c = V c := by
  by_cases hc : c ∈ present
  · exact rw.blocking present V c hc h_total
  · exact rw.update_absent present V c hc

/-- Iterated R-W learning over a sequence of trials. Each trial specifies
which cues are present. -/
def RescorlaWagner.iterate (rw : RescorlaWagner C)
    (trials : List (Finset C)) (V₀ : C → ℝ) : C → ℝ :=
  trials.foldl (fun V present => fun c => rw.update present V c) V₀

/-- Constant-trial iteration: the same cue set is presented on every trial. -/
def RescorlaWagner.iterateConst (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ) : ℕ → (C → ℝ)
  | 0 => V₀
  | n + 1 => fun c => rw.update S (rw.iterateConst S V₀ n) c

/-! ### Rescorla-Wagner equilibrium, convergence, and overshadowing -/

/-- Total strength recurrence: the summed associative strength across present
cues follows an affine recurrence after each trial,

    ΣV' = ΣV + β · (Σ_{c∈S} α_c) · (λ − ΣV)
        = (1 − β·A) · ΣV + β·A·λ       where A = Σ_{c∈S} α_c

the same shape as the Luce α-model (cf. `LinearLearner.iterate_closed_form`) with
retention rate `1 − β·A`, since the prediction error `(λ − ΣV)` is shared across
all present cues. -/
theorem RescorlaWagner.totalStrength_recurrence (rw : RescorlaWagner C)
    (S : Finset C) (V : C → ℝ) :
    ∑ c ∈ S, rw.update S V c =
      ∑ c ∈ S, V c +
        rw.learnRate * rw.predictionError S V * ∑ c ∈ S, rw.salience c := by
  have h1 : ∀ c ∈ S, rw.update S V c =
      V c + rw.salience c * rw.learnRate * rw.predictionError S V :=
    fun c hc => by simp only [update, if_pos hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- Closed form for iterated total strength under constant-trial R-W learning,

    T_n = r^n · T_0 + (1 − r^n) · λ    where r = 1 − β · Σα. -/
private theorem RescorlaWagner.totalStrength_closed_form (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ) (n : ℕ) :
    ∑ c ∈ S, rw.iterateConst S V₀ n c =
      (1 - rw.learnRate * ∑ c ∈ S, rw.salience c) ^ n *
        ∑ c ∈ S, V₀ c +
      (1 - (1 - rw.learnRate * ∑ c ∈ S, rw.salience c) ^ n) *
        rw.maxCond := by
  induction n with
  | zero =>
    simp only [RescorlaWagner.iterateConst, pow_zero, one_mul, sub_self, zero_mul, add_zero]
  | succ n ih =>
    have hstep : ∑ c ∈ S, rw.iterateConst S V₀ (n + 1) c =
        ∑ c ∈ S, rw.update S (rw.iterateConst S V₀ n) c :=
      Finset.sum_congr rfl fun c _ => rfl
    rw [hstep, rw.totalStrength_recurrence S (rw.iterateConst S V₀ n)]
    simp only [RescorlaWagner.predictionError]
    rw [ih]
    ring

/-- **Total strength convergence**: under repeated identical trials with the
same cue set `S`, the total associative strength converges to `λ`. -/
theorem RescorlaWagner.totalStrength_convergence (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ)
    (h_pos : 0 < rw.learnRate * ∑ c ∈ S, rw.salience c)
    (h_stable : rw.learnRate * ∑ c ∈ S, rw.salience c < 1) :
    Tendsto (fun n => ∑ c ∈ S, rw.iterateConst S V₀ n c)
      atTop (nhds rw.maxCond) := by
  simp_rw [RescorlaWagner.totalStrength_closed_form]
  set r := 1 - rw.learnRate * ∑ c ∈ S, rw.salience c with hr_def
  have hr_nonneg : 0 ≤ r := by linarith
  have hr_lt_one : r < 1 := by linarith
  have htend_pow : Tendsto (fun n => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have h1 : Tendsto (fun n => r ^ n * ∑ c ∈ S, V₀ c) atTop
      (nhds (0 * ∑ c ∈ S, V₀ c)) :=
    htend_pow.mul tendsto_const_nhds
  have h2 : Tendsto (fun n => (1 - r ^ n) * rw.maxCond) atTop
      (nhds ((1 - (0 : ℝ)) * rw.maxCond)) :=
    (tendsto_const_nhds.sub htend_pow).mul tendsto_const_nhds
  have h3 := h1.add h2
  simp only [zero_mul, sub_zero, one_mul, zero_add] at h3
  exact h3

/-- **Proportional partition** ([rescorla-wagner-1972]): when all cues start
with zero associative strength and the same cue set is presented on every trial,
each cue's strength at every step is proportional to its salience — there exists
`Kₙ` with `Vₙ(c) = α_c · Kₙ` for every present cue `c`. At convergence each cue's
strength is its salience-share of the outcome maximum `λ`. -/
theorem RescorlaWagner.proportional_partition (rw : RescorlaWagner C)
    (S : Finset C) (n : ℕ) :
    ∃ K : ℝ, ∀ c ∈ S, rw.iterateConst S (fun _ => 0) n c =
      rw.salience c * K := by
  induction n with
  | zero => exact ⟨0, fun c _ => by simp [RescorlaWagner.iterateConst, mul_zero]⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    have hsum : ∑ c' ∈ S, rw.iterateConst S (fun _ => 0) n c' =
        K * ∑ c' ∈ S, rw.salience c' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c' hc' => by rw [hK c' hc']; ring
    refine ⟨K + rw.learnRate * (rw.maxCond - K * ∑ c' ∈ S, rw.salience c'),
      fun c hc => ?_⟩
    simp only [RescorlaWagner.iterateConst, RescorlaWagner.update, if_pos hc,
      RescorlaWagner.predictionError]
    rw [hK c hc, hsum]
    ring

/-- **Overshadowing** ([rescorla-wagner-1972]; [ellis-2006]): when two
cues are both present on every trial, the more salient cue captures more
associative strength at every step (and hence at equilibrium). Immediate from
`proportional_partition`: `Vₙ(c) = α_c · K`, so `Vₙ(A) = α_A · K > α_B · K = Vₙ(B)`
whenever `K > 0`. -/
theorem RescorlaWagner.overshadowing (rw : RescorlaWagner C)
    (S : Finset C) (A B : C) (n : ℕ)
    (hA : A ∈ S) (hB : B ∈ S) (_hne : A ≠ B)
    (h_salience : rw.salience B < rw.salience A)
    (h_pos : 0 < ∑ c ∈ S, rw.iterateConst S (fun _ => 0) n c) :
    rw.iterateConst S (fun _ => 0) n B <
      rw.iterateConst S (fun _ => 0) n A := by
  obtain ⟨K, hK⟩ := rw.proportional_partition S n
  rw [hK A hA, hK B hB]
  have hK_pos : 0 < K := by
    by_contra h
    push Not at h
    have hle : ∑ c ∈ S, rw.iterateConst S (fun _ => 0) n c ≤ 0 :=
      Finset.sum_nonpos fun c hc => by
        rw [hK c hc]; exact mul_nonpos_of_nonneg_of_nonpos (rw.salience_nonneg c) h
    linarith
  exact mul_lt_mul_of_pos_right h_salience hK_pos

/-- **ΔP–R-W correspondence** ([ellis-2006]; [cheng-holyoak-1995]):
the blocked direction of a blocking experiment. If one cue already captures all
the associative strength and the novel cue starts at zero, the novel cue remains
at zero after compound trials — matching `ΔP = 0` for the blocked cue. -/
theorem RescorlaWagner.blocked_cue_zero (rw : RescorlaWagner C)
    (S : Finset C) (V : C → ℝ) (C' : C)
    (hC : C' ∈ S) (hV : V C' = 0)
    (h_total : ∑ c ∈ S, V c = rw.maxCond) :
    rw.update S V C' = 0 := by
  rw [rw.blocking S V C' hC h_total, hV]

end RescorlaWagner

end Core
