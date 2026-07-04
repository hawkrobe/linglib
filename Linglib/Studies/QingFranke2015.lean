import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Linglib.Pragmatics.GriceanMaxims
import Linglib.Studies.DaleReiter1995

/-!
# [qing-franke-2015]
[frank-goodman-2012] [grice-1975] [dale-reiter-1995]

"Variations on a Bayesian Theme: Comparing Bayesian Models of Referential Reasoning"

## Paradigm

Three objects varying on two dimensions (color × shape) in a reference game:
{green_square, green_circle, blue_circle}. Speaker produces a single feature word;
listener identifies the target object.

Utterances: {square, circle, green, blue}

## The Decomposition

The paper decomposes Bayesian reference games along 3 orthogonal dimensions,
yielding a family of models that includes [frank-goodman-2012] as one instance:

### Speaker Belief (y ∈ {U, S}): What does L0 assume?

- **Uniform (U)**: L0 treats all referents equally:
  U(t|m) = ⟦m⟧(t) / |⟦m⟧| (Eq. 1)
- **Salience (S)**: L0 weights by perceptual salience:
  S(t|m) = S(t) · ⟦m⟧(t) / Σ_t' S(t') · ⟦m⟧(t')

This enters the literal listener as its prior: uniform (`qfPriorU`) or
salience-weighted (`qfPriorS`), via the prior-in-L0 construction.

### Speaker Goal (x ∈ {a, b}): What does the speaker optimize?

- **Belief-oriented (b)**: maximize log-probability of correct belief
  σ_b(m|t) ∝ exp(λ_S · (log y(t|m) - Cost(m))) (Eq. 10)
- **Action-oriented (a)**: maximize probability of correct action
  σ_a(m|t) ∝ exp(λ_S · (y(t|m) - Cost(m))) (Eq. 9)

This enters via `s1Score`: belief-oriented uses log L0; action-oriented uses raw L0.

### Listener Action: How does the listener choose?

- **Belief-oriented (b)**: standard Bayesian update
  ρ_b(t|m) ∝ v(t) · σ(m|t) (Eq. 15)
- **Action-oriented (a)**: softmax over Bayesian posterior
  ρ_a(t|m) ∝ exp(α_L · ρ_b(t|m)) (Eq. 14)

The belief-oriented listener IS the Bayesian `PMF.posterior`. The
action-oriented listener is a composable softmax extension.

## Speaker Models (4 variants)

| Model | Goal | Belief | S1 Score |
|-------|------|--------|----------|
| σ_bU  | belief | uniform | exp(λ · (log U(t\|m) - C(m))) |
| σ_aU  | action | uniform | exp(λ · (U(t\|m) - C(m))) |
| σ_bS  | belief | salience | exp(λ · (log S(t\|m) - C(m))) |
| σ_aS  | action | salience | exp(λ · (S(t\|m) - C(m))) |

σ_bU is standard RSA with utterance costs.

## Key Findings

**Speaker data** (Table 1, N=144 per target): σ_bU and σ_aU best explain production
data (Table 3). Salience in the speaker does NOT help. Cost preference exists (c > 0).

**Listener data** (Table 2, N=180 per utterance): Salience-prior models dominate in
model comparison (Table 4). Best overall: ρ_aS(σ_aU) with informed-correlated
hyperprior.

**Salience reversal**: Uniform and salience priors make **opposite** L1 predictions
for ambiguous utterances. For "circle", human data matches the salience direction
(blue_circle: 117/180 = 65%). For "green", human data matches the pragmatic
direction (green_circle: 115/180 = 64%), NOT salience.

## Qualitative Findings

| # | Finding | Type | Config |
|---|---------|------|--------|
| 1 | `speaker_prefers_unique_shape` | S1: "square" > "green" for green_sq | σ_bU |
| 2 | `speaker_prefers_unique_color` | S1: "blue" > "circle" for blue_circ | σ_bU |
| 3 | `cost_breaks_symmetry` | S1: "circle" > "green" for green_circ | σ_bU |
| 4 | `no_cost_symmetry` | ¬(S1 "circle" > "green" for green_circ) | σ_bU, no cost |
| 5 | `salience_reversal_circle` | uniform vs salience L1 flip for "circle" | σ_bU |
| 6 | `salience_reversal_green` | uniform vs salience L1 flip for "green" | σ_bU |

-/

namespace QingFranke2015

open RSA BigOperators
open Real (exp log exp_pos exp_lt_exp)

-- ============================================================================
-- §1. Empirical Data
-- ============================================================================

/-- The 6 qualitative findings from [qing-franke-2015]. -/
inductive Finding where
  /-- For green_square targets, speakers prefer the unique shape word "square"
      over the shared color word "green". Evidence: 135/144 trials (Table 1). -/
  | speaker_prefers_unique_shape
  /-- For blue_circle targets, speakers prefer the unique color word "blue"
      over the shared shape word "circle". Evidence: 119/144 trials (Table 1). -/
  | speaker_prefers_unique_color
  /-- For green_circle targets, cost breaks the symmetry between the two
      ambiguous words: S1 prefers "circle" (noun, cost=0) over "green"
      (adjective, cost=1/2). Evidence: 81/144 chose "circle" (Table 1). -/
  | cost_breaks_symmetry
  /-- Without cost, the two ambiguous words for green_circle are symmetric:
      neither dominates the other. -/
  | no_cost_symmetry
  /-- Salience reversal for "circle": uniform L1 predicts green_circ > blue_circ,
      but salience L1 predicts blue_circ > green_circ. Human data matches the
      salience direction: 117/180 chose blue_circle (Table 2). -/
  | salience_reversal_circle
  /-- Salience reversal for "green": uniform L1 predicts green_circ > green_sq,
      but salience L1 predicts green_sq > green_circ. Human data matches the
      *pragmatic* direction: 115/180 chose green_circle (Table 2). The model
      predictions are correct; human data here follows pragmatics, not salience. -/
  | salience_reversal_green
  deriving DecidableEq, Repr

def findings : List Finding :=
  [.speaker_prefers_unique_shape, .speaker_prefers_unique_color,
   .cost_breaks_symmetry, .no_cost_symmetry,
   .salience_reversal_circle, .salience_reversal_green]

-- ============================================================================
-- §2. Domain Types
-- ============================================================================

/-- The three objects in the reference game context (Table 1).

    green_square: unique shape, shared color
    blue_circle: unique color, shared shape
    green_circle: both features shared -/
inductive Object where
  | green_square | blue_circle | green_circle
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty Object := ⟨.green_square⟩

/-- The four single-word utterances (feature predicates). -/
inductive Utterance where
  | square | circle | green | blue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty Utterance := ⟨.square⟩

/-- Boolean semantics: ⟦utterance⟧(object).

    - "square" applies to green_square only (unique shape)
    - "circle" applies to blue_circle and green_circle (shared shape)
    - "green" applies to green_square and green_circle (shared color)
    - "blue" applies to blue_circle only (unique color) -/
def Utterance.appliesTo : Utterance → Object → Bool
  | .square, .green_square => true
  | .circle, .blue_circle  => true
  | .circle, .green_circle => true
  | .green,  .green_square => true
  | .green,  .green_circle => true
  | .blue,   .blue_circle  => true
  | _, _ => false

-- ============================================================================
-- §3. Cost Structure
-- ============================================================================

/-- Adjective cost: shape words (nouns) cost 0, color words (adjectives) cost c.
    From [qing-franke-2015] Eq. 11: Cost(m) = c if m is an adjective, 0 otherwise. -/
noncomputable def adjCost (c : ℝ) : Utterance → ℝ
  | .square | .circle => 0
  | .green  | .blue   => c

-- ============================================================================
-- §4. Salience Data
-- ============================================================================

/-- Salience data from Table 2, salience condition (N = 240).

    Blue circle (139) is most salient; green circle (30) least. -/
def saliencePrior : Object → ℝ
  | .green_square => 71
  | .blue_circle  => 139
  | .green_circle => 30

theorem saliencePrior_nonneg : ∀ w, 0 ≤ saliencePrior w := by
  intro w; cases w <;> simp [saliencePrior]

-- ============================================================================
-- §5. Speaker Goal Types (Goal Dimension)
-- ============================================================================

/-- Belief-oriented S1 score [Eq. 10]:
    σ_b(m|t) ∝ exp(λ · (log y(t|m) - Cost(m)))

    The speaker maximizes log-probability of correct belief at L0. Gated by
    if-then-else because `log 0 = 0` in Lean (unlike WebPPL where `log 0 = -∞`
    naturally zeros out false utterances). -/
noncomputable def beliefGoalScore (cost : Utterance → ℝ) :
    (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - cost u))

theorem beliefGoalScore_nonneg (cost : Utterance → ℝ) :
    ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ beliefGoalScore cost l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [beliefGoalScore]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- Action-oriented S1 score [Eq. 9]:
    σ_a(m|t) ∝ exp(λ · (y(t|m) - Cost(m)))

    The speaker maximizes the raw probability that the listener picks the correct
    referent, rather than log-probability. Unlike beliefGoalScore, this gives
    nonzero score even for false utterances (exp(-λ·C) > 0 when y=0).
    The paper notes (Footnote 13) that model comparison restricts to truthful
    predictions; here the model comparison theorems (§13) only compare
    utterances that are true of the target object, so no gating is needed. -/
noncomputable def actionGoalScore (cost : Utterance → ℝ) :
    (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ :=
  fun l0 α _ w u => exp (α * (l0 u w - cost u))

theorem actionGoalScore_nonneg (cost : Utterance → ℝ) :
    ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ actionGoalScore cost l0 α l w u :=
  fun _ _ _ _ _ _ _ => le_of_lt (exp_pos _)

-- ============================================================================
-- §6. Priors
-- ============================================================================

/-- Uniform prior: all objects equally weighted. -/
def uniformPrior : Object → ℝ := fun _ => 1

theorem uniformPrior_nonneg : ∀ w, 0 ≤ uniformPrior w :=
  fun _ => le_of_lt one_pos

-- ============================================================================
-- §7. The 4 Speaker Models
-- ============================================================================

-- ============================================================================
-- §8. Concrete Configs for Findings
-- ============================================================================

-- ============================================================================
-- §9b. PMF chain (local pending the RSA API pass)
-- ============================================================================

section PMFChain

open scoped ENNReal

/-- Every utterance applies to some object, and every object satisfies some
utterance. -/
private theorem appliesTo_sat : ∀ u : Utterance, ∃ w, u.appliesTo w = true := by
  decide

private noncomputable def qfPriorU : PMF Object := PMF.uniformOfFintype Object

private theorem qfPriorU_pos (w : Object) : qfPriorU w ≠ 0 := by
  rw [qfPriorU, PMF.uniformOfFintype_apply]
  simp

private theorem qfPriorU_apply (w : Object) : qfPriorU w = 3⁻¹ := by
  rw [qfPriorU, PMF.uniformOfFintype_apply,
    show Fintype.card Object = 3 from by decide]
  norm_num

private theorem sumObjs (f : Object → ℝ≥0∞) :
    ∑' w, f w = f .green_square + f .blue_circle + f .green_circle := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Object)
      = {.green_square, .blue_circle, .green_circle} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sumUtts (f : Utterance → ℝ≥0∞) :
    ∑' u, f u = f .square + f .circle + f .green + f .blue := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance) = {.square, .circle, .green, .blue} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Salience prior as a PMF (Table 2 counts, total 240). -/
private noncomputable def qfPriorS : PMF Object :=
  PMF.normalize (fun w => ENNReal.ofReal (saliencePrior w))
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.green_square, by
      rw [ENNReal.ofReal_ne_zero_iff]
      norm_num [saliencePrior]⟩)
    (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)

private theorem salience_sum :
    (∑' w, ENNReal.ofReal (saliencePrior w)) = ENNReal.ofReal 240 := by
  rw [sumObjs]
  norm_num [saliencePrior]

private theorem qfPriorS_apply (w : Object) :
    qfPriorS w = ENNReal.ofReal (saliencePrior w / 240) := by
  rw [qfPriorS, PMF.normalize_apply, salience_sum,
    ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_mul (by cases w <;> norm_num [saliencePrior])]
  rw [div_eq_mul_inv]

private theorem qfPriorS_pos (w : Object) : qfPriorS w ≠ 0 := by
  rw [qfPriorS_apply, ENNReal.ofReal_ne_zero_iff]
  cases w <;> norm_num [saliencePrior]

/-- Literal listener at a speaker-belief prior (Figure-4-style prior-in-L0;
[qing-franke-2015] eqs. 5–8). -/
private noncomputable def qfL0 (bel : PMF Object) (hbel : ∀ w, bel w ≠ 0)
    (u : Utterance) : PMF Object :=
  RSA.L0LassiterGoodman bel (fun u w => u.appliesTo w) u (by
    obtain ⟨w, hw⟩ := appliesTo_sat u
    exact ENNReal.summable.tsum_ne_zero_iff.mpr
      ⟨w, by rw [hw]; simpa using hbel w⟩)

/-- Uniform-belief L0 values: `1` on the unique-feature objects, `1/2` on
shared features (extensions of size 1 and 2 over 3 objects). -/
private theorem qfL0_uniform_apply (u : Utterance) (w : Object) :
    qfL0 qfPriorU qfPriorU_pos u w
      = if u.appliesTo w then
          (if u = .square ∨ u = .blue then 1 else 2⁻¹) else 0 := by
  unfold qfL0
  rw [RSA.L0LassiterGoodman_apply]
  have hmass : (∑' w', qfPriorU w' * (if u.appliesTo w' then (1 : ℝ≥0∞) else 0))
      = if u = .square ∨ u = .blue then 3⁻¹ else 3⁻¹ + 3⁻¹ := by
    rw [sumObjs]
    simp only [qfPriorU_apply]
    cases u <;> simp +decide
  rw [hmass, qfPriorU_apply]
  by_cases hw : u.appliesTo w = true
  · rw [hw]
    by_cases h1 : u = .square ∨ u = .blue
    · simp only [h1, if_true, mul_one]
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    · simp only [h1, if_false, reduceIte, mul_one]
      rw [show (3 : ℝ≥0∞)⁻¹ + 3⁻¹ = 3⁻¹ * 2 from by ring,
        ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  · rw [Bool.not_eq_true] at hw
    rw [hw]
    simp

/-- Extension salience sums (denominators of the salience L0). -/
private noncomputable def extSum : Utterance → ℝ
  | .square => 71
  | .circle => 169
  | .green  => 101
  | .blue   => 139

/-- Salience-belief L0 values on support: object salience over extension
salience ([qing-franke-2015] L0 ∝ S(t)·⟦m⟧). -/
private theorem qfL0_salience_true {u : Utterance} {w : Object}
    (hw : u.appliesTo w = true) :
    qfL0 qfPriorS qfPriorS_pos u w
      = ENNReal.ofReal (saliencePrior w / extSum u) := by
  unfold qfL0
  rw [RSA.L0LassiterGoodman_apply, hw]
  have hmass : (∑' w', qfPriorS w' * (if u.appliesTo w' then (1 : ℝ≥0∞) else 0))
      = ENNReal.ofReal (extSum u / 240) := by
    rw [sumObjs]
    simp only [qfPriorS_apply]
    cases u <;>
      · simp +decide [saliencePrior, extSum]
        try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        try norm_num
  rw [hmass, qfPriorS_apply]
  simp only [reduceIte, mul_one]
  rw [← ENNReal.ofReal_inv_of_pos (by cases u <;> norm_num [extSum]),
    ← ENNReal.ofReal_mul (by cases w <;> norm_num [saliencePrior])]
  congr 1
  cases u <;> cases w <;> norm_num [saliencePrior, extSum]

private theorem qfL0_salience_false {u : Utterance} {w : Object}
    (hw : u.appliesTo w = false) :
    qfL0 qfPriorS qfPriorS_pos u w = 0 := by
  unfold qfL0
  rw [RSA.L0LassiterGoodman_apply, hw]
  simp

/-! ### Speakers and exp-bound helpers -/

private noncomputable def qfCf (c : ℝ) (u : Utterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(adjCost c u)))

private theorem qfCf_pos (c : ℝ) (u : Utterance) : qfCf c u ≠ 0 := by
  rw [qfCf, ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

private theorem qfCf_square (c : ℝ) : qfCf c .square = 1 := by
  simp [qfCf, adjCost]

private theorem qfCf_circle (c : ℝ) : qfCf c .circle = 1 := by
  simp [qfCf, adjCost]

private theorem qfCf_green (c : ℝ) : qfCf c .green = ENNReal.ofReal (Real.exp (-c)) :=
  rfl

private theorem qfCf_blue (c : ℝ) : qfCf c .blue = ENNReal.ofReal (Real.exp (-c)) :=
  rfl

private theorem objSat : ∀ w : Object, ∃ u : Utterance, u.appliesTo w = true := by
  decide

/-- Belief-oriented speaker ([qing-franke-2015] eq. 10 at λ = 1): weights
`L0 · exp(−Cost)`. -/
private noncomputable def s1B (bel : PMF Object) (hbel : ∀ w, bel w ≠ 0) (c : ℝ)
    (w : Object) : PMF Utterance :=
  RSA.S1Belief (qfL0 bel hbel) (qfCf c) 1 w
    (by
      obtain ⟨u, hu⟩ := objSat w
      refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨u, mul_ne_zero ?_ (qfCf_pos c u)⟩
      have hL0 : qfL0 bel hbel u w ≠ 0 := by
        unfold qfL0
        rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
        exact ⟨hbel w, hu⟩
      exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hL0) (PMF.apply_ne_top _ _)).ne')
    (ENNReal.tsum_ne_top_of_fintype fun u =>
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
        (by rw [qfCf]; exact ENNReal.ofReal_ne_top))

/-- Action-oriented speaker ([qing-franke-2015] eq. 9 at λ = 1): weights
`exp(L0 − Cost)` — positive on ALL utterances, including false ones (the
action-oriented speaker softmaxes raw success probability). Local private
op pending the RSA API pass. -/
private noncomputable def s1A (bel : PMF Object) (hbel : ∀ w, bel w ≠ 0) (c : ℝ)
    (w : Object) : PMF Utterance :=
  PMF.normalize
    (fun u => ENNReal.ofReal (Real.exp ((qfL0 bel hbel u w).toReal - adjCost c u)))
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.square, by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Real.exp_pos _⟩)
    (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)

/-- The five speaker chains of §7–§8, on the PMF face. -/
noncomputable def s1ZeroCost : Object → PMF Utterance := s1B qfPriorU qfPriorU_pos 0
noncomputable def s1Cost : Object → PMF Utterance := s1B qfPriorU qfPriorU_pos (1/2)
noncomputable def s1AU : Object → PMF Utterance := s1A qfPriorU qfPriorU_pos (1/2)
noncomputable def s1BS : Object → PMF Utterance := s1B qfPriorS qfPriorS_pos (1/2)
noncomputable def s1AS : Object → PMF Utterance := s1A qfPriorS qfPriorS_pos (1/2)

private theorem s1B_marginal_pos (bel : PMF Object) (hbel : ∀ w, bel w ≠ 0) (c : ℝ)
    (lp : PMF Object) (hlp : ∀ w, lp w ≠ 0) (u : Utterance) :
    PMF.marginal (s1B bel hbel c) lp u ≠ 0 := by
  obtain ⟨w, hw⟩ := appliesTo_sat u
  refine PMF.marginal_ne_zero _ _ _ (hlp w) ?_
  have hL0 : qfL0 bel hbel u w ≠ 0 := by
    unfold qfL0
    rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
    exact ⟨hbel w, hw⟩
  unfold s1B
  exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 (qfCf_pos c u)

/-- Pragmatic listeners ([qing-franke-2015] eqs. 12–13, 15): same σ_bU cost
speaker, uniform vs salience world prior. -/
noncomputable def l1Cost (u : Utterance) : PMF Object :=
  PMF.posterior (s1Cost) qfPriorU u
    (s1B_marginal_pos qfPriorU qfPriorU_pos (1/2) qfPriorU qfPriorU_pos u)

noncomputable def l1Sal (u : Utterance) : PMF Object :=
  PMF.posterior (s1Cost) qfPriorS u
    (s1B_marginal_pos qfPriorU qfPriorU_pos (1/2) qfPriorS qfPriorS_pos u)

/-! ### The `exp(−1/2)` atom and its three numeric bounds -/

private noncomputable def xc : ℝ := Real.exp (-(1/2))

private theorem xc_pos : 0 < xc := Real.exp_pos _

private theorem xc_lt_one : xc < 1 := by
  rw [xc, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_lt_exp.mpr (by norm_num)

private theorem xc_sq : xc * xc = (Real.exp 1)⁻¹ := by
  rw [xc, ← Real.exp_add, ← Real.exp_neg]
  norm_num

private theorem xc_sq_mul : xc * xc * Real.exp 1 = 1 := by
  rw [xc_sq, inv_mul_cancel₀ (Real.exp_pos 1).ne']

/-- `exp(−1/2) > 1/2` ⟺ `e < 4` — [qing-franke-2015]'s Finding 2 needs the
adjective's cost penalty to stay above the halved literal probability. -/
private theorem xc_gt_half : 1/2 < xc := by
  by_contra h
  push Not at h
  have h2 : xc * xc ≤ 1/4 := by nlinarith [xc_pos]
  have h3 : Real.exp 1 * (xc * xc) ≤ Real.exp 1 * (1/4) :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
  rw [show Real.exp 1 * (xc * xc) = xc * xc * Real.exp 1 from by ring, xc_sq_mul] at h3
  nlinarith [Real.exp_one_lt_d9]

/-- `exp(−1/2) < 139/169` ⟺ `e > (169/139)²` — the salience-belief speaker's
circle-over-blue reversal at the blue circle. -/
private theorem xc_lt_139_169 : xc < 139/169 := by
  by_contra h
  push Not at h
  have h2 : (139/169 : ℝ) * (139/169) ≤ xc * xc := by nlinarith [xc_pos]
  have h3 : Real.exp 1 * ((139/169 : ℝ) * (139/169)) ≤ Real.exp 1 * (xc * xc) :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
  rw [show Real.exp 1 * (xc * xc) = xc * xc * Real.exp 1 from by ring, xc_sq_mul] at h3
  nlinarith [Real.exp_one_gt_d9]

/-- `exp(−1/2) > 101/169` ⟺ `e < (169/101)²` ≈ 2.7998 — the tight bound
(margin ≈ 0.08 over `exp_one_lt_d9`). -/
private theorem xc_gt_101_169 : 101/169 < xc := by
  by_contra h
  push Not at h
  have h2 : xc * xc ≤ (101/169 : ℝ) * (101/169) := by nlinarith [xc_pos]
  have h3 : Real.exp 1 * (xc * xc) ≤ Real.exp 1 * ((101/169 : ℝ) * (101/169)) :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
  rw [show Real.exp 1 * (xc * xc) = xc * xc * Real.exp 1 from by ring, xc_sq_mul] at h3
  nlinarith [Real.exp_one_lt_d9]

/-! ### Cost-speaker values (for the listener comparisons) -/

private theorem half_conv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/2) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private theorem s1Cost_val {u : Utterance} {w : Object} (hw : u.appliesTo w = true)
    {q Z : ℝ} (hq0 : 0 ≤ q)
    (hq : (if u = .square ∨ u = .blue then (1 : ℝ≥0∞) else 2⁻¹) * qfCf (1/2) u
      = ENNReal.ofReal q)
    (hZ : (∑' u', (qfL0 qfPriorU qfPriorU_pos u' w : ℝ≥0∞) ^ (1 : ℝ) * qfCf (1/2) u')
      = ENNReal.ofReal Z) (hZpos : 0 < Z) :
    s1Cost w u = ENNReal.ofReal (q * Z⁻¹) := by
  unfold s1Cost s1B
  rw [RSA.S1Belief_apply, hZ, ENNReal.rpow_one, qfL0_uniform_apply, hw]
  simp only [if_true]
  rw [hq, ← ENNReal.ofReal_inv_of_pos hZpos, ← ENNReal.ofReal_mul hq0]

private theorem Z_gs :
    (∑' u', (qfL0 qfPriorU qfPriorU_pos u' .green_square : ℝ≥0∞) ^ (1 : ℝ) *
      qfCf (1/2) u') = ENNReal.ofReal (1 + xc/2) := by
  rw [sumUtts]
  simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_square, qfCf_circle,
    qfCf_green, qfCf_blue]
  simp +decide
  rw [half_conv, ← ENNReal.ofReal_mul (by norm_num),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  unfold xc
  norm_num
  ring

private theorem Z_bc :
    (∑' u', (qfL0 qfPriorU qfPriorU_pos u' .blue_circle : ℝ≥0∞) ^ (1 : ℝ) *
      qfCf (1/2) u') = ENNReal.ofReal (1/2 + xc) := by
  rw [sumUtts]
  simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_square, qfCf_circle,
    qfCf_green, qfCf_blue]
  simp +decide
  rw [half_conv, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  unfold xc
  norm_num

private theorem Z_gc :
    (∑' u', (qfL0 qfPriorU qfPriorU_pos u' .green_circle : ℝ≥0∞) ^ (1 : ℝ) *
      qfCf (1/2) u') = ENNReal.ofReal (1/2 + xc/2) := by
  rw [sumUtts]
  simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_square, qfCf_circle,
    qfCf_green, qfCf_blue]
  simp +decide
  rw [half_conv, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  unfold xc
  norm_num
  ring

private theorem third_conv : (3 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/3) := by
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from (ENNReal.ofReal_ofNat 3).symm,
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private theorem circle_weight :
    (if Utterance.circle = Utterance.square ∨ Utterance.circle = Utterance.blue
      then (1 : ℝ≥0∞) else 2⁻¹) * qfCf (1/2) .circle = ENNReal.ofReal (1/2) := by
  rw [show (if Utterance.circle = Utterance.square ∨ Utterance.circle = Utterance.blue
      then (1 : ℝ≥0∞) else 2⁻¹) = 2⁻¹ from by simp +decide, qfCf_circle, mul_one]
  exact half_conv

private theorem green_weight :
    (if Utterance.green = Utterance.square ∨ Utterance.green = Utterance.blue
      then (1 : ℝ≥0∞) else 2⁻¹) * qfCf (1/2) .green = ENNReal.ofReal (xc/2) := by
  rw [show (if Utterance.green = Utterance.square ∨ Utterance.green = Utterance.blue
      then (1 : ℝ≥0∞) else 2⁻¹) = 2⁻¹ from by simp +decide, qfCf_green, half_conv,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  unfold xc
  ring

private theorem sc_circle_gc :
    s1Cost .green_circle .circle = ENNReal.ofReal ((1/2) * (1/2 + xc/2)⁻¹) :=
  s1Cost_val (by decide) (by norm_num) circle_weight Z_gc
    (by have := xc_pos; linarith)

private theorem sc_circle_bc :
    s1Cost .blue_circle .circle = ENNReal.ofReal ((1/2) * (1/2 + xc)⁻¹) :=
  s1Cost_val (by decide) (by norm_num) circle_weight Z_bc
    (by have := xc_pos; linarith)

private theorem sc_green_gc :
    s1Cost .green_circle .green = ENNReal.ofReal ((xc/2) * (1/2 + xc/2)⁻¹) :=
  s1Cost_val (by decide) (by have := xc_pos; linarith) green_weight Z_gc
    (by have := xc_pos; linarith)

private theorem sc_green_gs :
    s1Cost .green_square .green = ENNReal.ofReal ((xc/2) * (1 + xc/2)⁻¹) :=
  s1Cost_val (by decide) (by have := xc_pos; linarith) green_weight Z_gs
    (by have := xc_pos; linarith)

private theorem xc_eq : Real.exp (-2⁻¹) = xc := by
  unfold xc
  norm_num

private theorem qfCf_zero (u : Utterance) : qfCf 0 u = 1 := by
  cases u <;> simp [qfCf, adjCost]

end PMFChain

open scoped ENNReal

-- ============================================================================
-- §10. Structural Properties
-- ============================================================================

/-- "square" uniquely identifies green_square. -/
theorem square_unique :
    Utterance.appliesTo .square .green_square = true ∧
    Utterance.appliesTo .square .blue_circle = false ∧
    Utterance.appliesTo .square .green_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-- "blue" uniquely identifies blue_circle. -/
theorem blue_unique :
    Utterance.appliesTo .blue .blue_circle = true ∧
    Utterance.appliesTo .blue .green_square = false ∧
    Utterance.appliesTo .blue .green_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-- "circle" is ambiguous between blue_circle and green_circle. -/
theorem circle_ambiguous :
    Utterance.appliesTo .circle .blue_circle = true ∧
    Utterance.appliesTo .circle .green_circle = true ∧
    Utterance.appliesTo .circle .green_square = false :=
  ⟨rfl, rfl, rfl⟩

/-- "green" is ambiguous between green_square and green_circle. -/
theorem green_ambiguous :
    Utterance.appliesTo .green .green_square = true ∧
    Utterance.appliesTo .green .green_circle = true ∧
    Utterance.appliesTo .green .blue_circle = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §11. Speaker Predictions (Findings 1–4)
-- ============================================================================

/-- Finding 1: For green_square, S1 prefers "square" (unique, cost=0) over "green"
    (ambiguous, cost=1/2). Both informativity and cost favor "square".
    Evidence: 135/144 speakers chose "square" (Table 1). -/
theorem speaker_prefers_unique_shape :
    s1Cost .green_square .square > s1Cost .green_square .green := by
  unfold s1Cost s1B
  rw [gt_iff_lt, RSA.S1Belief_apply_lt_iff_score_lt]
  simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_square, qfCf_green]
  simp +decide
  rw [half_conv, ← ENNReal.ofReal_mul (by norm_num),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
  rw [xc_eq]
  nlinarith [xc_pos, xc_lt_one]

/-- Finding 2: For blue_circle, S1 prefers "blue" (unique, cost=1/2) over "circle"
    (ambiguous, cost=0). Informativity dominates cost.
    Evidence: 119/144 speakers chose "blue" (Table 1). -/
theorem speaker_prefers_unique_color :
    s1Cost .blue_circle .blue > s1Cost .blue_circle .circle := by
  unfold s1Cost s1B
  rw [gt_iff_lt, RSA.S1Belief_apply_lt_iff_score_lt]
  simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_circle, qfCf_blue]
  simp +decide
  rw [half_conv]
  refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_
  rw [xc_eq]
  exact xc_gt_half

/-- Finding 3: For green_circle, cost breaks the tie between the two ambiguous
    words: S1 prefers "circle" (cost=0) over "green" (cost=1/2). Both are equally
    informative (each applies to 2 objects), so cost is the tiebreaker.
    Evidence: 81/144 chose "circle", 63/144 chose "green" (Table 1;
    not statistically significant: χ²=2.25, p=0.13). -/
theorem cost_breaks_symmetry :
    s1Cost .green_circle .circle > s1Cost .green_circle .green := by
  unfold s1Cost s1B
  rw [gt_iff_lt, RSA.S1Belief_apply_lt_iff_score_lt]
  simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_circle, qfCf_green]
  simp +decide
  rw [half_conv, ← ENNReal.ofReal_mul (by norm_num)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
  rw [xc_eq]
  nlinarith [xc_lt_one, xc_pos]

/-- Finding 4: Without cost, the symmetry is unbroken — neither ambiguous word
    dominates for green_circle. Both "circle" and "green" apply to exactly 2 objects,
    so L0 assigns equal probability, and S1 assigns equal weight. -/
theorem no_cost_symmetry :
    ¬(s1ZeroCost .green_circle .circle > s1ZeroCost .green_circle .green) := by
  have h : s1ZeroCost .green_circle .circle = s1ZeroCost .green_circle .green := by
    refine le_antisymm ?_ ?_ <;>
      · unfold s1ZeroCost s1B
        rw [RSA.S1Belief_apply_le_iff_score_le]
        simp only [ENNReal.rpow_one, qfL0_uniform_apply, qfCf_zero]
        simp +decide
  rw [gt_iff_lt, h]
  exact lt_irrefl _

-- ============================================================================
-- §12. Listener Predictions (Findings 5–6): Salience Reversal
-- ============================================================================

/-! The paper's central contribution: perceptual salience **reverses** L1 predictions.

Under uniform prior (costCfg), pragmatic reasoning dominates: the listener infers
that ambiguous words signal the object without a unique alternative. Under salience
prior (salienceCfg), salience overrides pragmatics: salient objects dominate even
though pragmatics would favor the other.

The listener prior v ∈ {U, S} enters at L1 via `worldPrior`, independent of the
speaker's belief y ∈ {U, S} which enters at L0 via `meaning`. Both costCfg and
salienceCfg use σ_bU (speaker belief = uniform), but differ in the listener's
prior — exactly the comparison the paper runs (Table 4 rows for ρ_bU vs ρ_bS). -/

-- Finding 5: Salience reversal for "circle"
-- Uniform: green_circle > blue_circle (pragmatic narrowing)
-- Salience: blue_circle > green_circle (salience override; matches human 66%)

/-- Uniform L1 for "circle": green_circle > blue_circle.
    Pragmatic reasoning: a speaker wanting blue_circle would say "blue" (unique),
    so saying "circle" signals green_circle. -/
theorem uniform_circle_green_circ :
    l1Cost .circle .green_circle > l1Cost .circle .blue_circle := by
  unfold l1Cost
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt, qfPriorU_apply, qfPriorU_apply,
    sc_circle_bc, sc_circle_gc, third_conv,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by have := xc_pos; positivity)).mpr ?_
  have hx := xc_pos
  have h1 : (0:ℝ) < 1/2 + xc := by linarith
  have h2 : (0:ℝ) < 1/2 + xc/2 := by linarith
  rw [show (1:ℝ)/3 * (1/2 * (1/2 + xc)⁻¹) = (1/6) / (1/2 + xc) from by
      rw [div_eq_mul_inv]; ring,
    show (1:ℝ)/3 * (1/2 * (1/2 + xc/2)⁻¹) = (1/6) / (1/2 + xc/2) from by
      rw [div_eq_mul_inv]; ring,
    div_lt_div_iff₀ h1 h2]
  nlinarith [hx]

/-- Salience L1 for "circle": blue_circle > green_circle.
    Salience (139 vs 30) overrides pragmatic narrowing. Matches human data
    (Table 2: 117/180 = 65% chose blue_circle). -/
theorem salience_circle_blue_circ :
    l1Sal .circle .blue_circle > l1Sal .circle .green_circle := by
  unfold l1Sal
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt, qfPriorS_apply, qfPriorS_apply,
    sc_circle_bc, sc_circle_gc,
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior]),
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior])]
  refine (ENNReal.ofReal_lt_ofReal_iff (by have := xc_pos; norm_num [saliencePrior]; positivity)).mpr ?_
  have hx := xc_pos
  have h1 : (0:ℝ) < 1/2 + xc := by linarith
  have h2 : (0:ℝ) < 1/2 + xc/2 := by linarith
  rw [saliencePrior, saliencePrior]
  rw [show ((30:ℝ)/240) * ((1/2) * (1/2 + xc/2)⁻¹) = (30/480) / (1/2 + xc/2) from by
      rw [div_eq_mul_inv]; ring,
    show ((139:ℝ)/240) * ((1/2) * (1/2 + xc)⁻¹) = (139/480) / (1/2 + xc) from by
      rw [div_eq_mul_inv]; ring,
    div_lt_div_iff₀ h2 h1]
  nlinarith [hx]

/-- Finding 5: Salience reversal for "circle". Uniform and salience priors make
    opposite L1 predictions, and human data matches the salience direction. -/
theorem salience_reversal_circle :
    (l1Cost .circle .green_circle > l1Cost .circle .blue_circle) ∧
    (l1Sal .circle .blue_circle > l1Sal .circle .green_circle) :=
  ⟨uniform_circle_green_circ, salience_circle_blue_circ⟩

-- Finding 6: Salience reversal for "green"
-- Uniform: green_circle > green_square (pragmatic narrowing)
-- Salience: green_square > green_circle (salience override; matches human 56%)

/-- Uniform L1 for "green": green_circle > green_square.
    Pragmatic reasoning: a speaker wanting green_square would say "square" (unique),
    so saying "green" signals green_circle. -/
theorem uniform_green_green_circ :
    l1Cost .green .green_circle > l1Cost .green .green_square := by
  unfold l1Cost
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt, qfPriorU_apply, qfPriorU_apply,
    sc_green_gs, sc_green_gc, third_conv,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by have := xc_pos; positivity)).mpr ?_
  have hx := xc_pos
  have h1 : (0:ℝ) < 1 + xc/2 := by linarith
  have h2 : (0:ℝ) < 1/2 + xc/2 := by linarith
  rw [show (1:ℝ)/3 * (xc/2 * (1 + xc/2)⁻¹) = (xc/6) / (1 + xc/2) from by
      rw [div_eq_mul_inv]; ring,
    show (1:ℝ)/3 * (xc/2 * (1/2 + xc/2)⁻¹) = (xc/6) / (1/2 + xc/2) from by
      rw [div_eq_mul_inv]; ring,
    div_lt_div_iff₀ h1 h2]
  nlinarith [hx]

/-- Salience L1 for "green": green_square > green_circle.
    Salience (71 vs 30) overrides pragmatic narrowing in the model. However,
    human data goes in the opposite (pragmatic) direction: Table 2 shows
    115/180 = 64% chose green_circle. -/
theorem salience_green_green_sq :
    l1Sal .green .green_square > l1Sal .green .green_circle := by
  unfold l1Sal
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt, qfPriorS_apply, qfPriorS_apply,
    sc_green_gs, sc_green_gc,
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior]),
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior])]
  refine (ENNReal.ofReal_lt_ofReal_iff (by have := xc_pos; norm_num [saliencePrior]; positivity)).mpr ?_
  have hx := xc_pos
  have h1 : (0:ℝ) < 1 + xc/2 := by linarith
  have h2 : (0:ℝ) < 1/2 + xc/2 := by linarith
  rw [saliencePrior, saliencePrior]
  rw [show ((30:ℝ)/240) * ((xc/2) * (1/2 + xc/2)⁻¹) = (30 * xc/480) / (1/2 + xc/2) from by
      rw [div_eq_mul_inv]; ring,
    show ((71:ℝ)/240) * ((xc/2) * (1 + xc/2)⁻¹) = (71 * xc/480) / (1 + xc/2) from by
      rw [div_eq_mul_inv]; ring,
    div_lt_div_iff₀ h2 h1]
  nlinarith [hx]

/-- Finding 6: Salience reversal for "green". Uniform and salience priors make
    opposite L1 predictions. Human data matches the *pragmatic* (uniform)
    direction: 115/180 chose green_circle (Table 2). -/
theorem salience_reversal_green :
    (l1Cost .green .green_circle > l1Cost .green .green_square) ∧
    (l1Sal .green .green_square > l1Sal .green .green_circle) :=
  ⟨uniform_green_green_circ, salience_green_green_sq⟩

-- ============================================================================
-- §13. Model Comparison: Alternative Speaker Models
-- ============================================================================

/-! The paper compares 4 speaker models along the speaker-goal × speaker-belief
dimensions (Table 3). Only σ_bU correctly predicts all three speaker preferences.
Each alternative fails on at least one observation:

| Model | green_sq (sq > gr) | blue_circ (bl > ci) | green_circ (ci > gr) | Score |
|-------|-------------------|--------------------|--------------------|-------|
| σ_bU  | ✓                 | ✓                  | ✓                  | 3/3   |
| σ_aU  | ✓                 | = (tie)            | ✓                  | 2/3   |
| σ_bS  | ✓                 | ✗ (ci > bl)        | ✗ (gr > ci)        | 1/3   |
| σ_aS  | ✓                 | ✗ (ci > bl)        | ✓                  | 2/3   |

The discriminating observation is **blue_circle**: only σ_bU predicts "blue" > "circle".
σ_aU ties (equal S1 scores), while σ_bS and σ_aS reverse the preference.

Salience in the speaker is harmful: it inflates L0's posterior for blue_circle given
"circle" (since blue_circle has the highest salience, 139 vs 30), which raises S1's
score for "circle" enough to match or exceed "blue". -/

-- Concrete configs: all use adjCost 1/2 and uniform listener prior.
-- (Listener prior doesn't affect S1, so any prior works for speaker comparison.)

-- §13a. σ_aU: Action-oriented, uniform belief
-- Agrees on green_sq and green_circ; ties on blue_circ.
-- The tie arises because exp/log don't cancel in actionGoalScore:
-- score(blue) = exp(1 * (1 - 1/2)) = exp(1/2)
-- score(circle) = exp(1 * (1/2 - 0)) = exp(1/2)

/-- σ_aU agrees: "square" > "green" for green_square. -/
theorem σ_aU_green_sq :
    s1AU .green_square .square > s1AU .green_square .green := by
  unfold s1AU s1A
  rw [gt_iff_lt, PMF.normalize_lt_iff_lt]
  simp only [qfL0_uniform_apply]
  simp +decide [ENNReal.toReal_inv, adjCost]

/-- σ_aU agrees: "circle" > "green" for green_circle (cost breaks symmetry). -/
theorem σ_aU_green_circ :
    s1AU .green_circle .circle > s1AU .green_circle .green := by
  unfold s1AU s1A
  rw [gt_iff_lt, PMF.normalize_lt_iff_lt]
  simp only [qfL0_uniform_apply]
  simp +decide [ENNReal.toReal_inv, adjCost]

/-- σ_aU fails: "blue" and "circle" are tied for blue_circle.
    This is the key prediction that distinguishes σ_aU from σ_bU.
    Under belief-oriented scoring (σ_bU), the log transform amplifies the
    informativity advantage of "blue" (L0 = 1) over "circle" (L0 = 1/2);
    under action-oriented scoring (σ_aU), the raw difference is exactly
    offset by cost. -/
theorem σ_aU_blue_circ_tie :
    ¬(s1AU .blue_circle .blue > s1AU .blue_circle .circle) ∧
    ¬(s1AU .blue_circle .circle > s1AU .blue_circle .blue) := by
  have h : s1AU .blue_circle .blue = s1AU .blue_circle .circle := by
    unfold s1AU s1A
    rw [PMF.normalize_eq_iff_eq]
    simp only [qfL0_uniform_apply]
    simp +decide [ENNReal.toReal_inv, adjCost]
    norm_num
  exact ⟨by rw [gt_iff_lt, h]; exact lt_irrefl _,
         by rw [gt_iff_lt, h]; exact lt_irrefl _⟩

-- §13b. σ_bS: Belief-oriented, salience belief
-- Agrees on green_sq; reverses on both blue_circ and green_circ.
-- Worst speaker model (1/3).

/-- σ_bS agrees: "square" > "green" for green_square.
    The unique shape word wins regardless of speaker belief, since "square"
    applies to only one object while "green" is ambiguous. -/
theorem σ_bS_green_sq :
    s1BS .green_square .square > s1BS .green_square .green := by
  unfold s1BS s1B
  rw [gt_iff_lt, RSA.S1Belief_apply_lt_iff_score_lt, ENNReal.rpow_one, ENNReal.rpow_one,
    qfL0_salience_true (show Utterance.green.appliesTo .green_square = true from by decide),
    qfL0_salience_true (show Utterance.square.appliesTo .green_square = true from by decide),
    qfCf_square, qfCf_green, mul_one,
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior, extSum])]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num [saliencePrior, extSum])).mpr ?_
  rw [show Real.exp (-(1/2 : ℝ)) = xc from rfl]
  norm_num [saliencePrior, extSum]
  nlinarith [xc_lt_one, xc_pos]

/-- σ_bS reverses blue_circle: predicts "circle" > "blue".
    With salience-weighted L0, blue_circle has the highest salience (139),
    so L0(blue_circ|"circle") = 139/169 ≈ 0.82, making "circle" quite
    informative. Combined with zero cost for "circle" vs cost 1/2 for "blue",
    the pragmatic advantage of "blue" is overcome. -/
theorem σ_bS_blue_circ_reversal :
    s1BS .blue_circle .circle > s1BS .blue_circle .blue := by
  unfold s1BS s1B
  rw [gt_iff_lt, RSA.S1Belief_apply_lt_iff_score_lt, ENNReal.rpow_one, ENNReal.rpow_one,
    qfL0_salience_true (show Utterance.blue.appliesTo .blue_circle = true from by decide),
    qfL0_salience_true (show Utterance.circle.appliesTo .blue_circle = true from by decide),
    qfCf_circle, qfCf_blue, mul_one,
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior, extSum])]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num [saliencePrior, extSum])).mpr ?_
  rw [show Real.exp (-(1/2 : ℝ)) = xc from rfl]
  norm_num [saliencePrior, extSum]
  nlinarith [xc_lt_139_169]

/-- σ_bS reverses green_circle: predicts "green" > "circle".
    With salience weights, L0(green_circ|"green") = 30/101 ≈ 0.30 and
    L0(green_circ|"circle") = 30/169 ≈ 0.18. "green" has higher L0 posterior
    for green_circ, and the log transform in belief-oriented scoring
    amplifies this advantage enough to overcome its cost disadvantage. -/
theorem σ_bS_green_circ_reversal :
    s1BS .green_circle .green > s1BS .green_circle .circle := by
  unfold s1BS s1B
  rw [gt_iff_lt, RSA.S1Belief_apply_lt_iff_score_lt, ENNReal.rpow_one, ENNReal.rpow_one,
    qfL0_salience_true (show Utterance.circle.appliesTo .green_circle = true from by decide),
    qfL0_salience_true (show Utterance.green.appliesTo .green_circle = true from by decide),
    qfCf_circle, qfCf_green, mul_one,
    ← ENNReal.ofReal_mul (by norm_num [saliencePrior, extSum])]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num [saliencePrior, extSum]; positivity)).mpr ?_
  rw [show Real.exp (-(1/2 : ℝ)) = xc from rfl]
  norm_num [saliencePrior, extSum]
  nlinarith [xc_gt_101_169]

-- §13c. σ_aS: Action-oriented, salience belief
-- Agrees on green_sq and green_circ; reverses on blue_circ.

/-- σ_aS agrees: "square" > "green" for green_square. -/
theorem σ_aS_green_sq :
    s1AS .green_square .square > s1AS .green_square .green := by
  unfold s1AS s1A
  rw [gt_iff_lt, PMF.normalize_lt_iff_lt]
  simp +decide [qfL0_salience_true, saliencePrior, extSum, adjCost]
  rw [ENNReal.toReal_ofReal (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
    (Real.exp_lt_exp.mpr (by norm_num))

/-- σ_aS reverses blue_circle: predicts "circle" > "blue".
    Same mechanism as σ_bS: salience inflates L0(blue_circ|"circle") = 139/169.
    Under action-oriented scoring, this raw probability advantage
    (plus zero cost) overcomes "blue"'s informativity. -/
theorem σ_aS_blue_circ_reversal :
    s1AS .blue_circle .circle > s1AS .blue_circle .blue := by
  unfold s1AS s1A
  rw [gt_iff_lt, PMF.normalize_lt_iff_lt]
  simp +decide [qfL0_salience_true, saliencePrior, extSum, adjCost]
  rw [ENNReal.toReal_ofReal (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
    (Real.exp_lt_exp.mpr (by norm_num))

/-- σ_aS agrees: "circle" > "green" for green_circle.
    Unlike σ_bS, the action-oriented scoring doesn't amplify the L0
    advantage of "green" via log, so cost wins for green_circle. -/
theorem σ_aS_green_circ :
    s1AS .green_circle .circle > s1AS .green_circle .green := by
  unfold s1AS s1A
  rw [gt_iff_lt, PMF.normalize_lt_iff_lt]
  simp +decide [qfL0_salience_true, saliencePrior, extSum, adjCost]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
    (Real.exp_lt_exp.mpr (by norm_num))

-- §13d. Capstone: σ_bU is the best speaker model

/-- σ_bU uniquely predicts "blue" > "circle" for blue_circle.

    The blue_circle observation is the decisive test: 119/144 speakers chose "blue"
    over "circle" (Table 1). σ_bU is the only model that predicts this:
    - σ_bU: blue > circle (correct) — log transform amplifies informativity
    - σ_aU: blue = circle (tie) — raw probability and cost exactly cancel
    - σ_bS: circle > blue (reversal) — salience makes "circle" informative
    - σ_aS: circle > blue (reversal) — same salience effect

    This is Q&F's main speaker-side finding: standard RSA (belief-oriented,
    uniform L0) best explains production data. -/
theorem σ_bU_best_speaker_model :
    -- σ_bU correctly predicts blue > circle
    (s1Cost .blue_circle .blue > s1Cost .blue_circle .circle) ∧
    -- σ_aU ties: neither blue > circle nor circle > blue
    (¬(s1AU .blue_circle .blue > s1AU .blue_circle .circle) ∧
     ¬(s1AU .blue_circle .circle > s1AU .blue_circle .blue)) ∧
    -- σ_bS reverses: circle > blue
    (s1BS .blue_circle .circle > s1BS .blue_circle .blue) ∧
    -- σ_aS reverses: circle > blue
    (s1AS .blue_circle .circle > s1AS .blue_circle .blue) :=
  ⟨speaker_prefers_unique_color, σ_aU_blue_circ_tie,
   σ_bS_blue_circ_reversal, σ_aS_blue_circ_reversal⟩

-- ============================================================================
-- §14. Verification
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .speaker_prefers_unique_shape =>
      s1Cost .green_square .square > s1Cost .green_square .green
  | .speaker_prefers_unique_color =>
      s1Cost .blue_circle .blue > s1Cost .blue_circle .circle
  | .cost_breaks_symmetry =>
      s1Cost .green_circle .circle > s1Cost .green_circle .green
  | .no_cost_symmetry =>
      ¬(s1ZeroCost .green_circle .circle > s1ZeroCost .green_circle .green)
  | .salience_reversal_circle =>
      (l1Cost .circle .green_circle > l1Cost .circle .blue_circle) ∧
      (l1Sal .circle .blue_circle > l1Sal .circle .green_circle)
  | .salience_reversal_green =>
      (l1Cost .green .green_circle > l1Cost .green .green_square) ∧
      (l1Sal .green .green_square > l1Sal .green .green_circle)

/-- The RSA model accounts for all 6 qualitative findings from [qing-franke-2015]. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact speaker_prefers_unique_shape
  · exact speaker_prefers_unique_color
  · exact cost_breaks_symmetry
  · exact no_cost_symmetry
  · exact salience_reversal_circle
  · exact salience_reversal_green

-- ============================================================================
-- §15. λ-Independence of Speaker Rankings
-- ============================================================================

/-! The speaker ranking under both belief-oriented and action-oriented scoring
is **completely independent of λ** (the rationality parameter). Since `exp`
is strictly monotone and multiplication by λ > 0 preserves strict order:

    exp(λ · a) > exp(λ · b) ⟺ a > b (for λ > 0)

**Consequence**: The qualitative predictions (findings 1–4) hold for ALL λ > 0.
The paper's strong rejection of λ = 1 (§5) affects only the *magnitude* of
preferences (softmax temperature), not their *direction*. The PMF-face
proofs at λ = 1 establish log(L0) − cost orderings that hold at every
positive λ.

Cost thresholds (the exact c ranges where each finding holds):
- **Finding 1** (sq > gr for green_sq): all c ≥ 0 (log 1 − 0 > log ½ − c)
- **Finding 2** (bl > ci for blue_circ): c < ln 2 ≈ 0.693 (see §16)
- **Finding 3** (ci > gr for green_circ): all c > 0 (log ½ − 0 > log ½ − c)
- **Finding 4** (ci = gr, no cost): equality, independent of everything -/

/-- Belief-oriented score ranking reduces to log L0 minus cost, independent of λ.

    For two truthful utterances (l0 ≠ 0 for both), the beliefGoalScore comparison
    is equivalent to comparing `log L0 − cost`, which has no λ dependence.
    Combined with `RationalAction.policy_gt_of_score_gt`, this means all
    qualitative belief-oriented S1 predictions are λ-independent. -/
theorem beliefGoal_gt_iff
    (cost : Utterance → ℝ) (l0 : Utterance → Object → ℝ)
    (u₁ u₂ : Utterance) (w : Object)
    {α : ℝ} (hα : 0 < α)
    (h1 : l0 u₁ w ≠ 0) (h2 : l0 u₂ w ≠ 0) :
    beliefGoalScore cost l0 α () w u₁ > beliefGoalScore cost l0 α () w u₂ ↔
    log (l0 u₁ w) - cost u₁ > log (l0 u₂ w) - cost u₂ := by
  simp only [beliefGoalScore, if_neg h1, if_neg h2]
  exact ⟨fun h => lt_of_mul_lt_mul_left (exp_lt_exp.mp h) (le_of_lt hα),
         fun h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hα)⟩

/-- Action-oriented score ranking reduces to L0 minus cost, independent of λ.

    Same λ-independence as belief-oriented, but comparing raw L0 rather than
    log L0. The difference between σ_a and σ_b is not λ-sensitivity (both are
    λ-independent) but how they *transform* L0: log compresses the informativity
    scale, amplifying small differences in L0 posterior. -/
theorem actionGoal_gt_iff
    (cost : Utterance → ℝ) (l0 : Utterance → Object → ℝ)
    (u₁ u₂ : Utterance) (w : Object)
    {α : ℝ} (hα : 0 < α) :
    actionGoalScore cost l0 α () w u₁ > actionGoalScore cost l0 α () w u₂ ↔
    l0 u₁ w - cost u₁ > l0 u₂ w - cost u₂ := by
  simp only [actionGoalScore]
  exact ⟨fun h => lt_of_mul_lt_mul_left (exp_lt_exp.mp h) (le_of_lt hα),
         fun h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hα)⟩

-- ============================================================================
-- §16. Cost Thresholds
-- ============================================================================

/-! The σ_aU tie at c = 1/2 (§13a) is the **exact boundary**: σ_aU predicts
"blue" > "circle" for blue_circle iff c < 1/2. Action-oriented scoring uses
raw L0: 1 − c > 1/2 − 0 ⟺ c < 1/2.

Belief-oriented scoring (σ_bU) uses log L0, giving a wider threshold of
c < ln 2 ≈ 0.693: log 1 − c > log(1/2) − 0 ⟺ c < ln 2.

Figure 4 shows that the posterior over c for σ_bU peaks around c ≈ 0.15,
well below the ln 2 ≈ 0.693 threshold. So the MAP cost estimate is
consistent with σ_bU correctly predicting blue > circle. -/

/-- σ_aU cost threshold for blue_circle: "blue" > "circle" ⟺ c < 1/2.

    Given L0(blue_circ|"blue") = 1 and L0(blue_circ|"circle") = 1/2,
    the action-oriented comparison reduces to 1 − c > 1/2. The existing tie
    `σ_aU_blue_circ_tie` is the corollary at c = 1/2. -/
theorem σ_aU_blue_circ_threshold
    {l0 : Utterance → Object → ℝ} {c : ℝ} {α : ℝ} (hα : 0 < α)
    (hbl : l0 .blue .blue_circle = 1) (hci : l0 .circle .blue_circle = 1/2) :
    actionGoalScore (adjCost c) l0 α () .blue_circle .blue >
    actionGoalScore (adjCost c) l0 α () .blue_circle .circle ↔ c < 1/2 := by
  rw [actionGoal_gt_iff _ _ _ _ _ hα]
  simp only [hbl, hci, adjCost]
  constructor <;> intro h <;> linarith

/-- σ_bU cost threshold for blue_circle: "blue" > "circle" ⟺ c < ln 2.

    Belief-oriented scoring uses log, so the threshold is wider than σ_aU's
    (ln 2 ≈ 0.693 > 0.5). This explains why σ_bU accommodates cost better
    than σ_aU: the log transform amplifies informativity differences,
    leaving more room for cost before the ranking flips. -/
theorem σ_bU_blue_circ_threshold
    {l0 : Utterance → Object → ℝ} {c : ℝ} {α : ℝ} (hα : 0 < α)
    (hbl : l0 .blue .blue_circle = 1) (hci : l0 .circle .blue_circle = 1/2)
    (hbl_ne : l0 .blue .blue_circle ≠ 0) (hci_ne : l0 .circle .blue_circle ≠ 0) :
    beliefGoalScore (adjCost c) l0 α () .blue_circle .blue >
    beliefGoalScore (adjCost c) l0 α () .blue_circle .circle ↔ c < log 2 := by
  rw [beliefGoal_gt_iff _ _ _ _ _ hα hbl_ne hci_ne]
  simp only [hbl, hci, adjCost, Real.log_one]
  have hlog : log ((1:ℝ) / 2) = -log 2 := by rw [one_div, Real.log_inv]
  rw [hlog]
  constructor <;> intro h <;> linarith

-- ============================================================================
-- §17. Raw Experimental Data (Tables 1–2)
-- ============================================================================

/-! Production and comprehension counts from the experiment (N = 1032 total:
432 speakers, 600 listeners). These connect model predictions to empirical
observations. -/

/-- Speaker production data from Table 1 (N = 144 per target object).

    - green_square: 135 "square", 9 "green" (93.8% unique shape)
    - blue_circle: 119 "blue", 25 "circle" (82.6% unique color)
    - green_circle: 81 "circle", 63 "green" (56.3% preferred noun; n.s.) -/
def speakerData : Object → Utterance → Nat
  | .green_square, .square => 135
  | .green_square, .green  => 9
  | .blue_circle,  .blue   => 119
  | .blue_circle,  .circle => 25
  | .green_circle, .circle => 81
  | .green_circle, .green  => 63
  | _, _                    => 0

/-- Listener comprehension data from Table 2 (N = 180 per ambiguous utterance).

    - "circle": 117 blue_circle, 62 green_circle, 1 green_square (65% salience)
    - "green": 65 green_square, 115 green_circle (64% pragmatic direction) -/
def listenerData : Utterance → Object → Nat
  | .circle, .blue_circle  => 117
  | .circle, .green_circle => 62
  | .circle, .green_square => 1
  | .green,  .green_square => 65
  | .green,  .green_circle => 115
  | _, _                    => 0

/-- Speaker data sums to N = 144 per target. -/
theorem speakerData_consistent :
    speakerData .green_square .square + speakerData .green_square .green = 144 ∧
    speakerData .blue_circle .blue + speakerData .blue_circle .circle = 144 ∧
    speakerData .green_circle .circle + speakerData .green_circle .green = 144 :=
  ⟨rfl, rfl, rfl⟩

/-- Listener data sums to N = 180 per ambiguous utterance. -/
theorem listenerData_consistent :
    listenerData .circle .blue_circle + listenerData .circle .green_circle
      + listenerData .circle .green_square = 180 ∧
    listenerData .green .green_square + listenerData .green .green_circle = 180 :=
  ⟨rfl, rfl⟩

/-- Speaker majority choice agrees with σ_bU S1 ranking (findings 1–3). -/
theorem speakerData_matches_model :
    speakerData .green_square .square > speakerData .green_square .green ∧
    speakerData .blue_circle .blue > speakerData .blue_circle .circle ∧
    speakerData .green_circle .circle > speakerData .green_circle .green :=
  ⟨by decide, by decide, by decide⟩

/-- For "circle", listener majority matches the salience L1 direction (finding 5):
    blue_circle (117) > green_circle (62). -/
theorem listenerData_circle_matches_salience :
    listenerData .circle .blue_circle > listenerData .circle .green_circle :=
  by decide

/-- For "green", listener majority matches the pragmatic/uniform L1 direction,
    NOT the salience direction: green_circle (115) > green_square (65).
    The paper notes this explicitly (p. 212). -/
theorem listenerData_green_matches_pragmatic :
    listenerData .green .green_circle > listenerData .green .green_square :=
  by decide

-- ============================================================================
-- §18. FG2012 Bridge
-- ============================================================================

/-! σ_bU with zero cost IS [frank-goodman-2012]'s model. FG2012 defines:

    s1Score l0 α _ w u := if l0 u w = 0 then 0 else exp(α * log(l0 u w))

which equals `beliefGoalScore (fun _ => 0)` since `x − 0 = x` (`sub_zero`).

FG2012 uses multiple reference game contexts across 7 conditions; Q&F's
experiment (§4) focuses on one configuration: {green_square, green_circle,
blue_circle}. The scoring rule and compositional pattern are identical —
Q&F's contribution is decomposing along the cost, goal, and salience
dimensions. -/

/-- Zero-cost belief-oriented scoring equals FG2012's scoring rule.

    `beliefGoalScore (fun _ => 0)` reduces to `if l0 = 0 then 0 else exp(α * log l0)`
    by `sub_zero`. This is the formal statement that σ_bU generalizes FG2012
    by adding utterance cost — setting cost to zero recovers the original model. -/
theorem zeroCost_beliefGoal_eq
    (l0 : Utterance → Object → ℝ) (α : ℝ) (w : Object) (u : Utterance) :
    beliefGoalScore (fun _ => (0 : ℝ)) l0 α () w u =
    if l0 u w = 0 then 0 else exp (α * log (l0 u w)) := by
  simp [beliefGoalScore, sub_zero]

/-!
## Summary: the model on the PMF face

1. **Two speaker goals, one chain shape**: the belief-oriented speakers are
   `RSA.S1Belief` (weights `L0 · exp(−Cost)`, eq. 10 at λ = 1); the
   action-oriented speakers are a local softmax over `exp(L0 − Cost)`
   (eq. 9) — positive on false utterances, which is exactly what produces
   the σ_aU tie at the blue circle.

2. **Speaker belief enters as the L0 prior**: uniform vs salience-weighted
   literal listeners are the same `L0LassiterGoodman` construction at
   different priors (`qfPriorU`/`qfPriorS`).

3. **Independent listener prior**: `l1Cost` and `l1Sal` share the σ_bU
   speaker and differ only in the posterior's world prior (eqs. 12–13) —
   the salience-reversal findings are pure prior effects.

4. **Sharp cost regime**: the three genuinely numeric findings need only
   `exp(−1/2) > 1/2` (e < 4), `exp(−1/2) < 139/169`, and
   `exp(−1/2) > 101/169` (e < (169/101)² ≈ 2.7998) — all discharged from
   `Real.exp_one_lt_d9`/`gt_d9`; everything else is generic in the cost
   factor.

5. **λ-independence** (§15): `beliefGoal_gt_iff` and `actionGoal_gt_iff` prove
   that speaker rankings depend only on `log L0 − cost` (or `L0 − cost`),
   not on the rationality parameter λ. The paper's rejection of λ = 1 affects
   only quantitative fit, not qualitative predictions.

8. **Cost thresholds** (§16): `σ_aU_blue_circ_threshold` (c < 1/2) and
   `σ_bU_blue_circ_threshold` (c < ln 2) give the exact cost boundaries
   for each model's blue_circle prediction. The log transform in σ_bU
   widens the viable cost range.

9. **Raw data** (§17): `speakerData` and `listenerData` formalize Tables 1–2.
   `speakerData_matches_model` verifies that speaker majority choices match
   σ_bU predictions. `listenerData_circle_matches_salience` confirms "circle"
   follows salience; `listenerData_green_matches_pragmatic` confirms "green"
   follows pragmatics — a richer pattern than uniform salience dominance.

10. **FG2012 bridge** (§18): `zeroCost_beliefGoal_eq` proves that belief-oriented
    scoring at zero cost recovers [frank-goodman-2012]'s scoring rule.
-/

-- ============================================================================
-- §19. Bridge: Cost = Q2 (Gricean/D&R Connection)
-- ============================================================================

/-! The cost dimension in [qing-franke-2015]'s S1 score decomposition
IS [grice-1975]'s Q2 sub-maxim (brevity):

    σ_b(m|t) ∝ exp(λ · (log L0(t|m) − Cost(m)))
                        ╰── Q1 ──╯   ╰── Q2 ──╯

This connects three frameworks:

- [grice-1975]: Q1 (be informative) and Q2 (be brief) are independent
- [dale-reiter-1995]: No-Brevity = Q2 not enforced (strength = 0)
- [qing-franke-2015]: Cost = 0 ↔ no Q2 pressure ↔ No Brevity

The zero-cost ↔ cost comparison (`no_cost_symmetry` vs `cost_breaks_symmetry`)
directly demonstrates Q2's role: it is the *tiebreaker* when Q1 (informativity)
is equal across alternatives. For green_circle, both "circle" and "green"
have the same L0 informativity (each applies to 2 objects), so Q1 cannot
distinguish them. Only Q2 (cost) breaks the tie. -/

open Pragmatics.GriceanMaxims

/-- Q&F's cost dimension IS Grice's Q2 sub-maxim. Without cost
    (No Brevity regime), ambiguous words with equal informativity are
    symmetric — Q1 alone cannot break the tie. With cost (Q2 active),
    the cheaper word wins. This maps onto [dale-reiter-1995]'s
    No-Brevity interpretation (strength = 0), the weakest Q2. -/
theorem cost_is_q2 :
    -- No cost = no symmetry breaking (No Brevity regime)
    ¬(s1ZeroCost .green_circle .circle > s1ZeroCost .green_circle .green) ∧
    -- With cost = symmetry breaks (Q2 pressure active)
    s1Cost .green_circle .circle > s1Cost .green_circle .green ∧
    -- No Brevity is the weakest Q2 interpretation
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 ∧
    -- Q1 and Q2 are independent sub-maxims
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim :=
  ⟨no_cost_symmetry, cost_breaks_symmetry, rfl, violations_independent⟩

end QingFranke2015
