import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.GriceanMaxims
import Linglib.Studies.DaleReiter1995
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# [qing-franke-2015]
[frank-goodman-2012] [grice-1975] [dale-reiter-1995]

Variations on a Bayesian theme: comparing Bayesian models of referential
reasoning. In *Bayesian Natural Language Semantics and Pragmatics*, 91–117.

One referential game (green square, green circle, blue circle; Fig. 1) and
a family of models decomposed along three design dimensions: the speaker's
goal (belief-oriented log-informativity, eq. 10, vs action-oriented raw
informativity, eq. 9), the speaker's belief about the literal listener
(uniform vs salience prior), and the listener's own prior (eqs. 12–13).
Utterance cost is a constant `c` on adjectives (eq. 11), marginalized over
`(−0.4, 0.4)` in the paper's model comparison.

## Main results

The belief-oriented chain is stated parametrically in the **cost factor**
`k = exp(−c)` (`k < 1` ↔ a noun preference `c > 0`), so each prediction
carries its exact validity region:

* `speaker_prefers_unique_shape` (k < 2) / `speaker_prefers_unique_color`
  (k > 1/2, i.e. c < ln 2) / `cost_breaks_symmetry` (k < 1) /
  `no_cost_symmetry` (k = 1): σ_bU matches all three Table-1 directions on
  the whole noun-preference regime 1/2 < k < 1
  (`σ_bU_matches_speaker_data`).
* `salience_reversal_circle` / `salience_reversal_green`: at **every**
  k > 0, the uniform-prior listener follows pragmatic narrowing while the
  salience-prior listener follows salience — the reversals are pure prior
  effects, needing no cost regime at all.
* `σ_bS_blue_circ_iff` (k vs 139/169) / `σ_bS_green_circ_iff` (k vs
  101/169): the salience-belief speaker's predictions flip *inside* the
  paper's cost support — thresholds, not directions, are that model's
  content.
* `σ_aU_blue_circ_threshold` (c < 1/2) vs `σ_bU_blue_circ_threshold`
  (c < ln 2): the goal dimension shifts the blue-circle boundary; the σ_aU
  tie at c = 1/2 is the boundary case.
* `beliefGoal_gt_iff` / `actionGoal_gt_iff`: speaker rankings are
  λ-independent — the paper's rejection of λ = 1 affects fit, not
  direction.
* `speakerData_matches_model` / `listenerData_circle_matches_salience` /
  `listenerData_green_matches_pragmatic`: Tables 1–2, with "green"
  following the pragmatic direction against salience (p. 212).
* `zeroCost_beliefGoal_eq`: at zero cost the belief-oriented score is
  [frank-goodman-2012]'s scoring rule.
* `cost_is_q2`: the cost dimension is [grice-1975]'s Q2 sub-maxim, in
  [dale-reiter-1995]'s No-Brevity reading at strength 0.

## Implementation notes

At λ = 1 the belief-oriented weight is `L0 · k`, so the chain is rational
in `k` and every prediction is symbolic algebra over
`PMF.normalizeOrUniform` — no transcendental atoms; `c` re-enters only
through the threshold identities (`k = 1/2` ↔ `c = ln 2`).
-/

open scoped ENNReal
open Real (exp log exp_lt_exp)

namespace QingFranke2015

/-- The three objects in the reference game context (Fig. 1): unique shape,
unique color, and both features shared. -/
inductive Object where
  | green_square | blue_circle | green_circle
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty Object := ⟨.green_square⟩

/-- The four single-word utterances (feature predicates). -/
inductive Utterance where
  | square | circle | green | blue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty Utterance := ⟨.square⟩

/-- Boolean semantics ⟦utterance⟧(object) (Fig. 1b). -/
def Utterance.appliesTo : Utterance → Object → Bool
  | .square, .green_square => true
  | .circle, .blue_circle  => true
  | .circle, .green_circle => true
  | .green,  .green_square => true
  | .green,  .green_circle => true
  | .blue,   .blue_circle  => true
  | _, _ => false

/-- "square" and "blue" each denote a single object; "circle" and "green"
are two-ways ambiguous. -/
theorem extension_characterization (w : Object) :
    (Utterance.appliesTo .square w = true ↔ w = .green_square) ∧
    (Utterance.appliesTo .blue w = true ↔ w = .blue_circle) ∧
    (Utterance.appliesTo .circle w = true ↔ w ≠ .green_square) ∧
    (Utterance.appliesTo .green w = true ↔ w ≠ .blue_circle) := by
  cases w <;> decide

/-! ### Empirical data (Tables 1–2) -/

/-- Speaker production data (Table 1, N = 144 per target). -/
def speakerData : Object → Utterance → Nat
  | .green_square, .square => 135
  | .green_square, .green  => 9
  | .blue_circle,  .blue   => 119
  | .blue_circle,  .circle => 25
  | .green_circle, .circle => 81
  | .green_circle, .green  => 63
  | _, _                    => 0

/-- Listener comprehension data (Table 2, N = 180 per ambiguous utterance). -/
def listenerData : Utterance → Object → Nat
  | .circle, .blue_circle  => 117
  | .circle, .green_circle => 62
  | .circle, .green_square => 1
  | .green,  .green_square => 65
  | .green,  .green_circle => 115
  | _, _                    => 0

/-- Salience prior: the salience condition of Table 2 (N = 240), the
paper's empirical estimate of `S(t)`. -/
def saliencePrior : Object → ℝ
  | .green_square => 71
  | .blue_circle  => 139
  | .green_circle => 30

/-- Uniform prior. -/
def uniformPrior : Object → ℝ
  | _ => 1

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

/-! ### Speaker goal types

The goal dimension (eqs. 9–10), generic in the literal listener and λ. -/

/-- Adjective cost (eq. 11): shape words cost 0, color words cost `c`. -/
noncomputable def adjCost (c : ℝ) : Utterance → ℝ
  | .square | .circle => 0
  | .green  | .blue   => c

/-- Belief-oriented S1 score (eq. 10): `exp (λ (log L0 − Cost))`, gated at
false utterances (Lean's `log 0 = 0` would otherwise leak mass). -/
noncomputable def beliefGoalScore (cost : Utterance → ℝ)
    (l0 : Utterance → Object → ℝ) (α : ℝ) (w : Object) (u : Utterance) : ℝ :=
  if l0 u w = 0 then 0 else exp (α * (log (l0 u w) - cost u))

/-- Action-oriented S1 score (eq. 9): `exp (λ (L0 − Cost))` — positive even
on false utterances (the paper's fn. 7 restricts comparisons to truthful
ones). -/
noncomputable def actionGoalScore (cost : Utterance → ℝ)
    (l0 : Utterance → Object → ℝ) (α : ℝ) (w : Object) (u : Utterance) : ℝ :=
  exp (α * (l0 u w - cost u))

/-- Belief-oriented ranking is λ-independent: it compares `log L0 − cost`. -/
theorem beliefGoal_gt_iff (cost : Utterance → ℝ) (l0 : Utterance → Object → ℝ)
    (u₁ u₂ : Utterance) (w : Object) {α : ℝ} (hα : 0 < α)
    (h1 : l0 u₁ w ≠ 0) (h2 : l0 u₂ w ≠ 0) :
    beliefGoalScore cost l0 α w u₁ > beliefGoalScore cost l0 α w u₂ ↔
    log (l0 u₁ w) - cost u₁ > log (l0 u₂ w) - cost u₂ := by
  simp only [beliefGoalScore, if_neg h1, if_neg h2]
  exact ⟨fun h => lt_of_mul_lt_mul_left (exp_lt_exp.mp h) hα.le,
         fun h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hα)⟩

/-- Action-oriented ranking is λ-independent: it compares `L0 − cost`. -/
theorem actionGoal_gt_iff (cost : Utterance → ℝ) (l0 : Utterance → Object → ℝ)
    (u₁ u₂ : Utterance) (w : Object) {α : ℝ} (hα : 0 < α) :
    actionGoalScore cost l0 α w u₁ > actionGoalScore cost l0 α w u₂ ↔
    l0 u₁ w - cost u₁ > l0 u₂ w - cost u₂ := by
  simp only [actionGoalScore]
  exact ⟨fun h => lt_of_mul_lt_mul_left (exp_lt_exp.mp h) hα.le,
         fun h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hα)⟩

/-! ### The belief-oriented chain, parametric in the cost factor

At λ = 1, `exp (log L0 − c) = L0 · exp (−c)`, so the whole σ_b chain is
rational in the cost factor `k = exp (−c)`: `k = 1` is zero cost, `k < 1`
a noun preference, and thresholds in `k` translate back to cost bounds
(`k > 1/2` ↔ `c < ln 2`). -/

/-- Multiplicative cost factor: `1` on shape words, `k` on color words. -/
def cf (k : ℝ) : Utterance → ℝ
  | .square | .circle => 1
  | .green  | .blue   => k

/-- Literal listener at prior `p` (eq. 1): prior conditioned on the
extension. -/
noncomputable def l0 (p : Object → ℝ) (u : Utterance) (w : Object) : ℝ :=
  (if u.appliesTo w then p w else 0) /
    ∑ w', if u.appliesTo w' then p w' else 0

/-- Belief-oriented speaker weight at λ = 1: `L0 · k^cost`. -/
noncomputable def sbScore (p : Object → ℝ) (k : ℝ) (w : Object)
    (u : Utterance) : ℝ :=
  l0 p u w * cf k u

/-- Belief-oriented speaker (eq. 10). -/
noncomputable def s1 (p : Object → ℝ) (k : ℝ) (w : Object) : PMF Utterance :=
  PMF.normalizeOrUniform fun u => ENNReal.ofReal (sbScore p k w u)

/-- Pragmatic-listener score (eqs. 12–13): the listener's own prior times
the σ_bU speaker (the paper's best-supported speaker model). -/
noncomputable def l1Score (prior : Object → ℝ) (k : ℝ) (u : Utterance)
    (w : Object) : ℝ :=
  prior w * (sbScore uniformPrior k w u / ∑ u', sbScore uniformPrior k w u')

/-- Pragmatic listener (eq. 6). -/
noncomputable def l1 (prior : Object → ℝ) (k : ℝ) (u : Utterance) :
    PMF Object :=
  PMF.normalizeOrUniform fun w => ENNReal.ofReal (l1Score prior k u w)

private theorem sumU (f : Utterance → ℝ) :
    ∑ u, f u = f .square + f .circle + f .green + f .blue := by
  rw [show (Finset.univ : Finset Utterance) = {.square, .circle, .green, .blue}
      from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem sumO (f : Object → ℝ) :
    ∑ w, f w = f .green_square + f .blue_circle + f .green_circle := by
  rw [show (Finset.univ : Finset Object)
      = {.green_square, .blue_circle, .green_circle} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

section Parametric

variable {k : ℝ}

/-- The σ_bU weights, symbolically in k. -/
private theorem sbScore_values :
    sbScore uniformPrior k .green_square .square = 1 ∧
    sbScore uniformPrior k .green_square .green = k/2 ∧
    sbScore uniformPrior k .green_square .circle = 0 ∧
    sbScore uniformPrior k .green_square .blue = 0 ∧
    sbScore uniformPrior k .green_circle .circle = 1/2 ∧
    sbScore uniformPrior k .green_circle .green = k/2 ∧
    sbScore uniformPrior k .green_circle .square = 0 ∧
    sbScore uniformPrior k .green_circle .blue = 0 ∧
    sbScore uniformPrior k .blue_circle .blue = k ∧
    sbScore uniformPrior k .blue_circle .circle = 1/2 ∧
    sbScore uniformPrior k .blue_circle .square = 0 ∧
    sbScore uniformPrior k .blue_circle .green = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [sbScore, l0, cf, uniformPrior, sumO, Utterance.appliesTo]
      norm_num
      try ring

private theorem sbScore_nonneg (hk : 0 ≤ k) (p : Object → ℝ)
    (hp : ∀ w, 0 ≤ p w) (w : Object) (u : Utterance) :
    0 ≤ sbScore p k w u := by
  refine mul_nonneg (div_nonneg ?_ (Finset.sum_nonneg fun w' _ => ?_)) ?_
  · split
    exacts [hp _, le_rfl]
  · split
    exacts [hp _, le_rfl]
  · cases u <;> simp only [cf] <;> first | exact zero_le_one | exact hk

/-- Same-target speaker comparison: reduces to the raw weights. -/
private theorem s1_lt (p : Object → ℝ) (hk : 0 ≤ k) (hp : ∀ w, 0 ≤ p w)
    {w : Object} {u₁ u₂ : Utterance}
    (hpos : 0 < ∑ u, sbScore p k w u)
    (h : sbScore p k w u₁ < sbScore p k w u₂) :
    s1 p k w u₁ < s1 p k w u₂ := by
  unfold s1
  exact PMF.normalizeOrUniform_ofReal_lt_cross (sbScore_nonneg hk p hp w)
    (sbScore_nonneg hk p hp w) hpos hpos (div_lt_div_of_pos_right h hpos)

private theorem l1Score_nonneg (hk : 0 ≤ k) (prior : Object → ℝ)
    (hp : ∀ w, 0 ≤ prior w) (u : Utterance) (w : Object) :
    0 ≤ l1Score prior k u w :=
  mul_nonneg (hp w) (div_nonneg
    (sbScore_nonneg hk uniformPrior (fun _ => zero_le_one) w u)
    (Finset.sum_nonneg fun u' _ =>
      sbScore_nonneg hk uniformPrior (fun _ => zero_le_one) w u'))

/-- Same-utterance listener comparison: reduces to the scores. -/
private theorem l1_lt (prior : Object → ℝ) (hk : 0 ≤ k)
    (hp : ∀ w, 0 ≤ prior w) {u : Utterance} {w₁ w₂ : Object}
    (hpos : 0 < ∑ w, l1Score prior k u w)
    (h : l1Score prior k u w₁ < l1Score prior k u w₂) :
    l1 prior k u w₁ < l1 prior k u w₂ := by
  unfold l1
  exact PMF.normalizeOrUniform_ofReal_lt_cross (l1Score_nonneg hk prior hp u)
    (l1Score_nonneg hk prior hp u) hpos hpos (div_lt_div_of_pos_right h hpos)

/-! ### Speaker predictions (Table 1 directions) -/

/-- For the green square, σ_bU prefers the unique "square" over the
ambiguous "green" at every cost factor k < 2 (135/144 speakers, Table 1). -/
theorem speaker_prefers_unique_shape (hk : 0 ≤ k) (hk2 : k < 2) :
    s1 uniformPrior k .green_square .green <
      s1 uniformPrior k .green_square .square := by
  obtain ⟨h1, h2, h3, h4, -⟩ := sbScore_values (k := k)
  exact s1_lt uniformPrior hk (fun _ => zero_le_one)
    (by rw [sumU, h1, h2, h3, h4]; linarith) (by rw [h1, h2]; linarith)

/-- For the blue circle, σ_bU prefers the unique "blue" over "circle" once
the cost factor exceeds 1/2 (c < ln 2); 119/144 speakers chose "blue". -/
theorem speaker_prefers_unique_color (hk : 1/2 < k) :
    s1 uniformPrior k .blue_circle .circle <
      s1 uniformPrior k .blue_circle .blue := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10, h11, h12⟩ := sbScore_values (k := k)
  exact s1_lt uniformPrior (by linarith) (fun _ => zero_le_one)
    (by rw [sumU, h9, h10, h11, h12]; linarith) (by rw [h9, h10]; linarith)

/-- For the green circle, cost is the tiebreaker: any noun preference
(k < 1) favors "circle" over "green" (81 vs 63, Table 1, n.s.). -/
theorem cost_breaks_symmetry (hk : 0 < k) (hk1 : k < 1) :
    s1 uniformPrior k .green_circle .green <
      s1 uniformPrior k .green_circle .circle := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8, -⟩ := sbScore_values (k := k)
  exact s1_lt uniformPrior hk.le (fun _ => zero_le_one)
    (by rw [sumU, h5, h6, h7, h8]; linarith) (by rw [h5, h6]; linarith)

/-- Without cost (k = 1) the green-circle tie is unbroken: Q1 alone cannot
distinguish two equally informative words. -/
theorem no_cost_symmetry :
    sbScore uniformPrior 1 .green_circle .circle =
      sbScore uniformPrior 1 .green_circle .green := by
  simp only [sbScore, l0, cf, uniformPrior, sumO, Utterance.appliesTo]
  norm_num

/-- σ_bU with any noun preference in (1/2, 1) — covering the paper's whole
positive-cost support c ∈ (0, 0.4] — matches all three Table-1 majority
directions. -/
theorem σ_bU_matches_speaker_data (hk : 1/2 < k) (hk1 : k < 1) :
    (s1 uniformPrior k .green_square .green <
      s1 uniformPrior k .green_square .square) ∧
    (s1 uniformPrior k .blue_circle .circle <
      s1 uniformPrior k .blue_circle .blue) ∧
    (s1 uniformPrior k .green_circle .green <
      s1 uniformPrior k .green_circle .circle) :=
  ⟨speaker_prefers_unique_shape (by linarith) (by linarith),
   speaker_prefers_unique_color hk, cost_breaks_symmetry (by linarith) hk1⟩

/-! ### Listener predictions: the salience reversal (Tables 2 and 4)

Both listeners embed the same σ_bU speaker and differ only in their prior
(eqs. 12–13). The reversals hold at **every** k > 0: they are pure prior
effects, independent of the cost regime. -/

/-- The listener scores at the contested cells, symbolically in k. -/
private theorem l1Score_values (hk : 0 < k) :
    l1Score uniformPrior k .circle .green_circle = 1/(1 + k) ∧
    l1Score uniformPrior k .circle .blue_circle = 1/(1 + 2*k) ∧
    l1Score saliencePrior k .circle .green_circle = 30/(1 + k) ∧
    l1Score saliencePrior k .circle .blue_circle = 139/(1 + 2*k) ∧
    l1Score uniformPrior k .green .green_square = k/(2 + k) ∧
    l1Score uniformPrior k .green .green_circle = k/(1 + k) ∧
    l1Score saliencePrior k .green .green_square = 71*k/(2 + k) ∧
    l1Score saliencePrior k .green .green_circle = 30*k/(1 + k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    sbScore_values (k := k)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold l1Score
      rw [sumU]
      first
        | rw [h5, h6, h7, h8] | rw [h9, h10, h11, h12] | rw [h1, h2, h3, h4]
      simp only [uniformPrior, saliencePrior]
      rw [mul_div_assoc', div_eq_div_iff (by linarith) (by linarith)]
      ring

/-- Uniform-prior listener, "circle": pragmatic narrowing favors the green
circle (a blue-circle speaker had "blue"), at every k > 0. -/
theorem uniform_circle_green_circ (hk : 0 < k) :
    l1 uniformPrior k .circle .blue_circle <
      l1 uniformPrior k .circle .green_circle := by
  obtain ⟨h1, h2, -⟩ := l1Score_values hk
  have hgs : (0:ℝ) ≤ l1Score uniformPrior k .circle .green_square :=
    l1Score_nonneg hk.le _ (fun _ => zero_le_one) _ _
  refine l1_lt uniformPrior hk.le (fun _ => zero_le_one) ?_ ?_
  · rw [sumO, h1, h2]
    have : (0:ℝ) < 1/(1 + k) := by positivity
    have : (0:ℝ) < 1/(1 + 2*k) := by positivity
    linarith
  · rw [h1, h2, div_lt_div_iff₀ (by linarith) (by linarith)]
    linarith

/-- Salience-prior listener, "circle": salience (139 vs 30) overrides the
pragmatic direction, at every k > 0. Matches Table 2 (117/180 blue). -/
theorem salience_circle_blue_circ (hk : 0 < k) :
    l1 saliencePrior k .circle .green_circle <
      l1 saliencePrior k .circle .blue_circle := by
  obtain ⟨-, -, h3, h4, -⟩ := l1Score_values hk
  have hp : ∀ w, 0 ≤ saliencePrior w := by
    intro w; cases w <;> simp [saliencePrior]
  have hgs : (0:ℝ) ≤ l1Score saliencePrior k .circle .green_square :=
    l1Score_nonneg hk.le _ hp _ _
  refine l1_lt saliencePrior hk.le hp ?_ ?_
  · rw [sumO, h3, h4]
    have : (0:ℝ) < 30/(1 + k) := by positivity
    have : (0:ℝ) < 139/(1 + 2*k) := by positivity
    linarith
  · rw [h3, h4, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- Finding 5: the salience reversal for "circle", at every k > 0. The
human data follow the salience direction. -/
theorem salience_reversal_circle (hk : 0 < k) :
    (l1 uniformPrior k .circle .blue_circle <
      l1 uniformPrior k .circle .green_circle) ∧
    (l1 saliencePrior k .circle .green_circle <
      l1 saliencePrior k .circle .blue_circle) :=
  ⟨uniform_circle_green_circ hk, salience_circle_blue_circ hk⟩

/-- Uniform-prior listener, "green": pragmatic narrowing favors the green
circle (a green-square speaker had "square"), at every k > 0. -/
theorem uniform_green_green_circ (hk : 0 < k) :
    l1 uniformPrior k .green .green_square <
      l1 uniformPrior k .green .green_circle := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := l1Score_values hk
  have hbc : (0:ℝ) ≤ l1Score uniformPrior k .green .blue_circle :=
    l1Score_nonneg hk.le _ (fun _ => zero_le_one) _ _
  refine l1_lt uniformPrior hk.le (fun _ => zero_le_one) ?_ ?_
  · rw [sumO, h5, h6]
    have : (0:ℝ) < k/(2 + k) := by positivity
    have : (0:ℝ) < k/(1 + k) := by positivity
    linarith
  · rw [h5, h6, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- Salience-prior listener, "green": salience (71 vs 30) overrides the
pragmatic direction, at every k > 0. Here the humans go the *other* way
(115/180 green circle, Table 2; p. 212). -/
theorem salience_green_green_sq (hk : 0 < k) :
    l1 saliencePrior k .green .green_circle <
      l1 saliencePrior k .green .green_square := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := l1Score_values hk
  have hp : ∀ w, 0 ≤ saliencePrior w := by
    intro w; cases w <;> simp [saliencePrior]
  have hbc : (0:ℝ) ≤ l1Score saliencePrior k .green .blue_circle :=
    l1Score_nonneg hk.le _ hp _ _
  refine l1_lt saliencePrior hk.le hp ?_ ?_
  · rw [sumO, h7, h8]
    have : (0:ℝ) < 71*k/(2 + k) := by positivity
    have : (0:ℝ) < 30*k/(1 + k) := by positivity
    linarith
  · rw [h7, h8, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- Finding 6: the salience reversal for "green", at every k > 0. The human
data follow the *pragmatic* direction — no single listener prior gets both
"circle" and "green" right. -/
theorem salience_reversal_green (hk : 0 < k) :
    (l1 uniformPrior k .green .green_square <
      l1 uniformPrior k .green .green_circle) ∧
    (l1 saliencePrior k .green .green_circle <
      l1 saliencePrior k .green .green_square) :=
  ⟨uniform_green_green_circ hk, salience_green_green_sq hk⟩

/-! ### The salience-belief speaker: thresholds inside the cost support

σ_bS replaces the speaker's literal-listener prior with the salience data
(eq. 7). Its blue-circle and green-circle predictions flip at k = 139/169
and k = 101/169 — both *inside* the paper's cost support (c ∈ (0, 0.4) is
k ∈ (0.67, 1)) — so that model's content is a pair of thresholds, not
directions. -/

/-- σ_bS weights at the contested cells: `L0` conditions the salience
prior on the extension. -/
private theorem sbS_values :
    sbScore saliencePrior k .blue_circle .blue = k ∧
    sbScore saliencePrior k .blue_circle .circle = 139/169 ∧
    sbScore saliencePrior k .green_circle .green = 30/101 * k ∧
    sbScore saliencePrior k .green_circle .circle = 30/169 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [sbScore, l0, cf, saliencePrior, sumO, Utterance.appliesTo]
      norm_num

/-- σ_bS prefers "blue" at the blue circle iff k > 139/169. -/
theorem σ_bS_blue_circ_iff :
    sbScore saliencePrior k .blue_circle .circle <
      sbScore saliencePrior k .blue_circle .blue ↔ 139/169 < k := by
  obtain ⟨h1, h2, -⟩ := sbS_values (k := k)
  rw [h1, h2]

/-- σ_bS prefers "green" at the green circle iff k > 101/169. -/
theorem σ_bS_green_circ_iff :
    sbScore saliencePrior k .green_circle .circle <
      sbScore saliencePrior k .green_circle .green ↔ 101/169 < k := by
  obtain ⟨-, -, h3, h4⟩ := sbS_values (k := k)
  rw [h3, h4]
  constructor <;> intro h <;> nlinarith

end Parametric

/-! ### Cost thresholds across the goal dimension

The blue-circle boundary separates the goal types: action-oriented scoring
flips at c = 1/2, belief-oriented at c = ln 2 ≈ 0.693 — the log transform
amplifies informativity differences, widening the viable cost range.
Figure 3's posterior over c peaks well below both. -/

/-- σ_aU threshold: "blue" > "circle" at the blue circle iff c < 1/2; the
σ_aU tie at c = 1/2 is the boundary case. -/
theorem σ_aU_blue_circ_threshold
    {l0 : Utterance → Object → ℝ} {c : ℝ} {α : ℝ} (hα : 0 < α)
    (hbl : l0 .blue .blue_circle = 1) (hci : l0 .circle .blue_circle = 1/2) :
    actionGoalScore (adjCost c) l0 α .blue_circle .blue >
    actionGoalScore (adjCost c) l0 α .blue_circle .circle ↔ c < 1/2 := by
  rw [actionGoal_gt_iff _ _ _ _ _ hα]
  simp only [hbl, hci, adjCost]
  constructor <;> intro h <;> linarith

/-- σ_bU threshold: "blue" > "circle" at the blue circle iff c < ln 2 —
the exponentiated form of `speaker_prefers_unique_color`'s k > 1/2. -/
theorem σ_bU_blue_circ_threshold
    {l0 : Utterance → Object → ℝ} {c : ℝ} {α : ℝ} (hα : 0 < α)
    (hbl : l0 .blue .blue_circle = 1) (hci : l0 .circle .blue_circle = 1/2)
    (hbl_ne : l0 .blue .blue_circle ≠ 0) (hci_ne : l0 .circle .blue_circle ≠ 0) :
    beliefGoalScore (adjCost c) l0 α .blue_circle .blue >
    beliefGoalScore (adjCost c) l0 α .blue_circle .circle ↔ c < log 2 := by
  rw [beliefGoal_gt_iff _ _ _ _ _ hα hbl_ne hci_ne]
  simp only [hbl, hci, adjCost, Real.log_one]
  have hlog : log ((1:ℝ) / 2) = -log 2 := by rw [one_div, Real.log_inv]
  rw [hlog]
  constructor <;> intro h <;> linarith

/-! ### Data–model match -/

/-- Speaker majority choices match the σ_bU rankings (Table 1). -/
theorem speakerData_matches_model :
    speakerData .green_square .square > speakerData .green_square .green ∧
    speakerData .blue_circle .blue > speakerData .blue_circle .circle ∧
    speakerData .green_circle .circle > speakerData .green_circle .green :=
  ⟨by decide, by decide, by decide⟩

/-- For "circle", the listener majority follows the salience direction
(117 vs 62). -/
theorem listenerData_circle_matches_salience :
    listenerData .circle .blue_circle > listenerData .circle .green_circle := by
  decide

/-- For "green", the listener majority follows the pragmatic direction, not
salience (115 vs 65; p. 212). -/
theorem listenerData_green_matches_pragmatic :
    listenerData .green .green_circle > listenerData .green .green_square := by
  decide

/-! ### Bridges -/

/-- At zero cost the belief-oriented score is [frank-goodman-2012]'s
scoring rule — σ_bU generalizes FG2012 by the cost dimension. -/
theorem zeroCost_beliefGoal_eq
    (l0 : Utterance → Object → ℝ) (α : ℝ) (w : Object) (u : Utterance) :
    beliefGoalScore (fun _ => (0 : ℝ)) l0 α w u =
    if l0 u w = 0 then 0 else exp (α * log (l0 u w)) := by
  simp [beliefGoalScore, sub_zero]

open Pragmatics.GriceanMaxims in
/-- The cost dimension is [grice-1975]'s Q2 sub-maxim (brevity): without
cost the equally-informative words tie (Q1 alone cannot break it), any
noun preference breaks it, and zero cost is [dale-reiter-1995]'s
No-Brevity interpretation at strength 0, independent of Q1. -/
theorem cost_is_q2 :
    (sbScore uniformPrior 1 .green_circle .circle =
      sbScore uniformPrior 1 .green_circle .green) ∧
    (∀ k : ℝ, 0 < k → k < 1 →
      s1 uniformPrior k .green_circle .green <
        s1 uniformPrior k .green_circle .circle) ∧
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 ∧
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim :=
  ⟨no_cost_symmetry, fun _ hk hk1 => cost_breaks_symmetry hk hk1, rfl,
   violations_independent⟩

end QingFranke2015
