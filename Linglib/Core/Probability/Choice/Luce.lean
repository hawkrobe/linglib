module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Linglib.Core.Analysis.SpecialFunctions.Softmax

/-!
# The Luce choice model

A `LuceModel` selects actions with probability proportional to a non-negative
score — the **Luce choice rule**, whose choice axiom ([luce-1959], Axiom 1,
p. 6) makes the odds of two actions independent of the rest of the menu. This
is the shared substrate for the library's soft-rational agents: softmax agents
(`LuceModel.fromSoftmax`, with the exponential core in
`Core.Analysis.SpecialFunctions.Softmax` and its variational theory in
`Core.Probability.SoftmaxTheory`), Gumbel random-utility agents
(`Core.Probability.Choice.GumbelLuce`), and signal-detection observers
(`Processing.Psychophysics.SignalDetection`).

## Main definitions

* `LuceModel`, `LuceModel.prob` — score-proportional choice.
* `LuceModel.probOn` — the choice rule restricted to a `Finset` menu.
* `LuceModel.fromSoftmax` — the model with score `exp (α * utility)`, whose
  choice probabilities are `softmax`.
* `pairwiseProb` — the binary Luce (Bradley–Terry) kernel `v x / (v x + v y)`.
* `ChoiceFn` — [luce-1959]'s primitive system of choice probabilities over
  finite menus, with the single-clause axiom forms `ChoiceFn.HasRatioScale`,
  `ChoiceFn.HasProductRule`, `ChoiceFn.HasPairwiseIIA` and the two-clause
  Axiom 1 itself, `ChoiceFn.HasChoiceAxiom`.

## Main results

* `LuceModel.iia`, `LuceModel.product_rule` — the choice axiom for `probOn`.
* `LuceModel.prob_eq_iff_proportional` — two models share their choice
  probabilities iff their scores are proportional: the score is a ratio scale.
* `ChoiceFn.hasRatioScale_iff_hasPairwiseIIA` — the ratio form is equivalent
  to pairwise IIA under strict positivity.
* `ChoiceFn.HasChoiceAxiom.ratioScaleOn` / `ChoiceFn.ratioScaleOn_unique` —
  existence and uniqueness halves of Theorem 3 of [luce-1959] (p. 23): under
  the axiom, imperfect discrimination on a menu yields a local ratio scale,
  unique up to a positive multiple.
* `ChoiceFn.HasChoiceAxiom.binary_mul_cycle` — Theorem 2 of [luce-1959]
  (p. 16): the cyclic product identity for pairwise probabilities.

## Implementation notes

`prob` and `probOn` normalize by a possibly-zero total with no case split, in
the junk-value idiom of `Finset.centerMass`: real division by zero is `0`, so
a model with vanishing total score assigns probability `0` throughout.

`ChoiceFn` is total where [luce-1959] (p. 5) leaves the diagonal to the
notational convention `P(x, x) = ½`: here `binary x x = 1`
(`ChoiceFn.binary_self`), so imperfect discrimination (`ChoiceFn.ImperfectOn`)
and binary ratio scales (`ChoiceFn.BinaryRatioScaleOn`) quantify over distinct
pairs only.

## References

* [R. D. Luce, *Individual Choice Behavior: A Theoretical Analysis* (1959)][luce-1959]
-/

@[expose] public section

namespace Core

open Real Finset

/-! ### The Luce choice rule -/

/-- A Luce choice model: a state-indexed family of non-negative scores over a
finite action type, selecting each action with probability proportional to
`score state action` — the choice rule of [luce-1959]. The `score` function
is unnormalized; `prob` normalizes it.

Concrete scales across the library: `exp (α * utility)`
(`LuceModel.fromSoftmax`), Gumbel random-utility scores
(`LuceModel.fromGumbelRUM`), and power-law sensation magnitudes
(`Studies.Luce1959`). -/
structure LuceModel (State Action : Type*) [Fintype Action] where
  /-- Unnormalized score: `prob (a | s) ∝ score s a`. -/
  score : State → Action → ℝ
  /-- Scores are non-negative. -/
  score_nonneg : ∀ s a, 0 ≤ score s a

variable {S A : Type*} [Fintype A]

namespace LuceModel

/-- Total score across all actions in a state (the normalization constant). -/
noncomputable def totalScore (ra : LuceModel S A) (s : S) : ℝ :=
  ∑ a : A, ra.score s a

theorem totalScore_nonneg (ra : LuceModel S A) (s : S) :
    0 ≤ ra.totalScore s :=
  Finset.sum_nonneg fun a _ ↦ ra.score_nonneg s a

/-- The choice probability `P(a | s) = score s a / ∑ a', score s a'`.
Division by zero makes this `0` when the total score vanishes. -/
noncomputable def prob (ra : LuceModel S A) (s : S) (a : A) : ℝ :=
  ra.score s a / ra.totalScore s

theorem prob_nonneg (ra : LuceModel S A) (s : S) (a : A) :
    0 ≤ ra.prob s a :=
  div_nonneg (ra.score_nonneg s a) (ra.totalScore_nonneg s)

/-- Zero score implies zero probability. -/
theorem prob_eq_zero_of_score_eq_zero (ra : LuceModel S A) (s : S)
    (a : A) (h : ra.score s a = 0) :
    ra.prob s a = 0 := by
  simp [prob, h]

/-- The choice probabilities are a distribution when the total score is
nonzero. -/
theorem prob_sum_eq_one (ra : LuceModel S A) (s : S)
    (h : ra.totalScore s ≠ 0) :
    ∑ a : A, ra.prob s a = 1 := by
  simp only [prob, ← Finset.sum_div]
  exact div_self h

/-- Monotonicity: higher score, higher probability. -/
theorem prob_monotone (ra : LuceModel S A) (s : S)
    (a₁ a₂ : A) (h : ra.score s a₁ ≤ ra.score s a₂) :
    ra.prob s a₁ ≤ ra.prob s a₂ := by
  simp only [prob, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.2 (ra.totalScore_nonneg s))

/-- Strict monotonicity: strictly higher score gives strictly higher
    probability. -/
@[gcongr only]
theorem prob_lt_of_score_lt (ra : LuceModel S A) (s : S)
    (a₁ a₂ : A) (hlt : ra.score s a₁ < ra.score s a₂) :
    ra.prob s a₁ < ra.prob s a₂ := by
  have htot : 0 < ra.totalScore s :=
    lt_of_lt_of_le (lt_of_le_of_lt (ra.score_nonneg s a₁) hlt)
      (Finset.single_le_sum (fun a _ ↦ ra.score_nonneg s a) (Finset.mem_univ a₂))
  exact div_lt_div_of_pos_right hlt htot

/-- At a fixed state, the strict probability ordering coincides with the
    strict score ordering. -/
theorem prob_lt_iff_score_lt (ra : LuceModel S A) (s : S) (a₁ a₂ : A) :
    ra.prob s a₁ < ra.prob s a₂ ↔ ra.score s a₁ < ra.score s a₂ :=
  ⟨fun h ↦ not_le.1 fun hle ↦ not_lt.2 (ra.prob_monotone s a₂ a₁ hle) h,
   ra.prob_lt_of_score_lt s a₁ a₂⟩

/-! ### Luce's choice axiom (IIA)

[luce-1959] characterizes the ratio rule `P(a | T) = v a / ∑ b ∈ T, v b` by
the **independence of irrelevant alternatives**: the odds of two actions do
not depend on which other actions the menu offers (the constant-ratio rule,
Lemma 3, p. 9). `probOn` restricts the Luce rule to a `Finset` menu; `iia`
and `product_rule` relate menus to submenus. -/

/-- Constant ratio rule: `prob a₁ * score a₂ = prob a₂ * score a₁` — the
    odds `prob a₁ / prob a₂` equal the score odds. -/
theorem prob_ratio (ra : LuceModel S A) (s : S) (a₁ a₂ : A) :
    ra.prob s a₁ * ra.score s a₂ = ra.prob s a₂ * ra.score s a₁ := by
  simp only [prob]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm]

/-- Choice probability from a menu:
    `probOn s T a = score s a / ∑ b ∈ T, score s b` for `a ∈ T`, and `0`
    otherwise (`0` as well when the menu total vanishes, by the
    division-by-zero convention). -/
noncomputable def probOn [DecidableEq A] (ra : LuceModel S A) (s : S)
    (T : Finset A) (a : A) : ℝ :=
  if a ∈ T then ra.score s a / ∑ b ∈ T, ra.score s b else 0

/-- On the full menu, `probOn` is `prob`. -/
theorem probOn_univ [DecidableEq A] (ra : LuceModel S A) (s : S) (a : A) :
    ra.probOn s Finset.univ a = ra.prob s a := by
  simp [probOn, prob, totalScore]

theorem probOn_nonneg [DecidableEq A] (ra : LuceModel S A) (s : S)
    (T : Finset A) (a : A) :
    0 ≤ ra.probOn s T a := by
  simp only [probOn]
  split
  · exact div_nonneg (ra.score_nonneg s a)
      (Finset.sum_nonneg fun b _ ↦ ra.score_nonneg s b)
  · exact le_rfl

/-- `probOn` in ratio form on the menu. -/
theorem probOn_eq_div [DecidableEq A] (ra : LuceModel S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T) :
    ra.probOn s T a = ra.score s a / ∑ b ∈ T, ra.score s b := by
  simp only [probOn, ha, ↓reduceIte]

/-- `probOn` sums to 1 over a menu with nonzero total. -/
theorem probOn_sum_eq_one [DecidableEq A] (ra : LuceModel S A) (s : S)
    (T : Finset A) (hT : ∑ b ∈ T, ra.score s b ≠ 0) :
    ∑ a ∈ T, ra.probOn s T a = 1 := by
  rw [Finset.sum_congr rfl fun a ha ↦ ra.probOn_eq_div s T a ha,
    ← Finset.sum_div, div_self hT]

/-- IIA core (Lemma 3 of [luce-1959], p. 9, in cross-product form): within
    any menu, the odds of two actions equal their score odds. -/
theorem probOn_ratio [DecidableEq A] (ra : LuceModel S A) (s : S)
    (T : Finset A) (a₁ a₂ : A) (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) :
    ra.probOn s T a₁ * ra.score s a₂ = ra.probOn s T a₂ * ra.score s a₁ := by
  rw [ra.probOn_eq_div s T a₁ h₁, ra.probOn_eq_div s T a₂ h₂,
    div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm]

/-- `probOn` is positive on members of a menu of positive scores. -/
theorem probOn_pos [DecidableEq A] {ra : LuceModel S A} {s : S}
    {T : Finset A} {a : A} (ha : a ∈ T) (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    0 < ra.probOn s T a := by
  rw [ra.probOn_eq_div s T a ha]
  exact div_pos (hpos a ha) (Finset.sum_pos hpos ⟨a, ha⟩)

/-- Within a menu of positive scores, higher score means higher `probOn`. -/
theorem probOn_lt_of_score_lt [DecidableEq A] {ra : LuceModel S A}
    {s : S} {T : Finset A} {a₁ a₂ : A} (ha₁ : a₁ ∈ T) (ha₂ : a₂ ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) (hlt : ra.score s a₂ < ra.score s a₁) :
    ra.probOn s T a₂ < ra.probOn s T a₁ := by
  rw [ra.probOn_eq_div s T a₁ ha₁, ra.probOn_eq_div s T a₂ ha₂]
  exact div_lt_div_of_pos_right hlt (Finset.sum_pos hpos ⟨a₁, ha₁⟩)

/-- IIA: `P(a | S') = P(a | T) / ∑ b ∈ S', P(b | T)` for `S' ⊆ T` — choice
    from a submenu is choice from the menu conditioned on the submenu. -/
theorem iia [DecidableEq A] (ra : LuceModel S A) (s : S)
    (S' T : Finset A) (hST : S' ⊆ T) (a : A) (ha : a ∈ S')
    (hS : ∑ b ∈ S', ra.score s b ≠ 0) (hT : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.probOn s S' a = ra.probOn s T a / ∑ b ∈ S', ra.probOn s T b := by
  rw [ra.probOn_eq_div s S' a ha, ra.probOn_eq_div s T a (hST ha),
    Finset.sum_congr rfl fun b hb ↦ ra.probOn_eq_div s T b (hST hb),
    ← Finset.sum_div]
  field_simp

/-- Product rule (the shape of part i of Axiom 1, p. 6 of [luce-1959]):
    `P(a | T) = P(a | S') · P(S' | T)` for `a ∈ S' ⊆ T`, where
    `P(S' | T) = ∑ b ∈ S', score b / ∑ b ∈ T, score b`. -/
theorem product_rule [DecidableEq A] (ra : LuceModel S A) (s : S)
    (S' T : Finset A) (hST : S' ⊆ T) (a : A) (ha : a ∈ S')
    (hS : ∑ b ∈ S', ra.score s b ≠ 0) :
    ra.probOn s T a =
      ra.probOn s S' a * ((∑ b ∈ S', ra.score s b) / ∑ b ∈ T, ra.score s b) := by
  rw [ra.probOn_eq_div s T a (hST ha), ra.probOn_eq_div s S' a ha,
    div_mul_div_comm, mul_comm (ra.score s a), mul_div_mul_left _ _ hS]

/-! ### Ratio-scale invariance and uniqueness

The choice probabilities are invariant under scaling all scores by a positive
constant, and conversely two models share their choice probabilities exactly
when their scores are proportional: the score is a ratio scale, the model
form of Theorem 3 of [luce-1959] (p. 23). -/

/-- Proportional scores yield the same choice probabilities. -/
theorem prob_eq_of_proportional (ra ra' : LuceModel S A) (s : S)
    (k : ℝ) (hk : 0 < k) (h : ∀ a, ra'.score s a = k * ra.score s a) (a : A) :
    ra'.prob s a = ra.prob s a := by
  simp only [prob, totalScore, h, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk.ne'

/-- Scale all scores by a positive constant `k`. -/
noncomputable def scaleBy (ra : LuceModel S A) (k : ℝ) (hk : 0 < k) :
    LuceModel S A where
  score s a := k * ra.score s a
  score_nonneg s a := mul_nonneg hk.le (ra.score_nonneg s a)

/-- Scale invariance: scaling scores by `k > 0` preserves the choice
    probabilities. -/
theorem scaleBy_prob (ra : LuceModel S A) (s : S) (a : A)
    (k : ℝ) (hk : 0 < k) :
    (ra.scaleBy k hk).prob s a = ra.prob s a :=
  ra.prob_eq_of_proportional (ra.scaleBy k hk) s k hk (fun _ ↦ rfl) a

/-- Uniqueness of the ratio scale: two models with positive totals and the
    same choice probabilities have proportional scores, with constant
    `totalScore₂ / totalScore₁`. -/
theorem proportional_of_prob_eq (ra₁ ra₂ : LuceModel S A) (s : S)
    (h₁ : 0 < ra₁.totalScore s) (h₂ : 0 < ra₂.totalScore s)
    (hprob : ∀ a, ra₁.prob s a = ra₂.prob s a) :
    ∀ a, ra₂.score s a =
      ra₂.totalScore s / ra₁.totalScore s * ra₁.score s a := by
  intro a
  have h := hprob a
  simp only [prob] at h
  rw [div_eq_div_iff h₁.ne' h₂.ne'] at h
  rw [div_mul_eq_mul_div, eq_div_iff h₁.ne']
  linarith

/-- Two models with positive totals share their choice probabilities iff
    their scores are proportional. -/
theorem prob_eq_iff_proportional (ra₁ ra₂ : LuceModel S A) (s : S)
    (h₁ : 0 < ra₁.totalScore s) (h₂ : 0 < ra₂.totalScore s) :
    (∀ a, ra₁.prob s a = ra₂.prob s a) ↔
      ∃ k : ℝ, 0 < k ∧ ∀ a, ra₂.score s a = k * ra₁.score s a := by
  refine ⟨fun hprob ↦ ⟨ra₂.totalScore s / ra₁.totalScore s, div_pos h₂ h₁,
    ra₁.proportional_of_prob_eq ra₂ s h₁ h₂ hprob⟩, ?_⟩
  rintro ⟨k, hk, hprop⟩ a
  exact (ra₁.prob_eq_of_proportional ra₂ s k hk hprop a).symm

/-! ### The softmax parameterization -/

/-- The model with score `exp (α * utility s a)`: its choice probabilities
    are `softmax (α • utility s)`. -/
noncomputable def fromSoftmax (utility : S → A → ℝ) (α : ℝ) :
    LuceModel S A where
  score s a := exp (α * utility s a)
  score_nonneg _ _ := (exp_pos _).le

/-- The choice probabilities of a softmax model are the softmax of the
    scaled utility. -/
theorem fromSoftmax_prob_eq (utility : S → A → ℝ) (α : ℝ) (s : S) (a : A) :
    (fromSoftmax utility α).prob s a = softmax (α • utility s) a := rfl

end LuceModel

/-! ### The pairwise choice kernel

`pairwiseProb v x y = v x / (v x + v y)` is the binary Luce rule — the
Bradley–Terry kernel. Hypotheses are pointwise (`0 < v x`) so the suite
applies to locally positive scales such as `cf.prob T` produced by
`ChoiceFn.HasChoiceAxiom.ratioScaleOn` below. On an exponential scale the
kernel is the logistic of the utility difference (`pairwiseProb_exp`) —
[luce-1959]'s Fechnerian coordinates `u = log v` (Ch. 2, §2.A.2). -/

section PairwiseProb

variable {A : Type*} {v : A → ℝ} {x y z : A}

/-- The pairwise choice probability `P(x, {x,y})` under a ratio scale `v`:
    `P(x, y) = v x / (v x + v y)` — the Luce model prediction for binary
    forced choice. -/
noncomputable def pairwiseProb (v : A → ℝ) (x y : A) : ℝ :=
  v x / (v x + v y)

/-- Pairwise probabilities are non-negative for non-negative scales. -/
theorem pairwiseProb_nonneg (hx : 0 ≤ v x) (hy : 0 ≤ v y) :
    0 ≤ pairwiseProb v x y :=
  div_nonneg hx (add_nonneg hx hy)

/-- Pairwise probabilities are at most 1 for positive scales. -/
theorem pairwiseProb_le_one (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y ≤ 1 := by
  rw [pairwiseProb, div_le_one (add_pos hx hy)]
  linarith

/-- Complementarity: `P(x, y) + P(y, x) = 1` for positive scales. -/
theorem pairwiseProb_complement (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y + pairwiseProb v y x = 1 := by
  rw [pairwiseProb, pairwiseProb, add_comm (v y), ← add_div,
    div_self (ne_of_gt (add_pos hx hy))]

/-- `P(x, x) = 1/2` for positive scales (indifference with self). -/
theorem pairwiseProb_self (hx : 0 < v x) : pairwiseProb v x x = 1 / 2 := by
  rw [pairwiseProb, div_eq_iff (by linarith : v x + v x ≠ 0)]
  ring

/-- `P(x, y) > 1/2` iff `v x > v y`: the higher-scale alternative is chosen
    more than half the time. -/
theorem pairwiseProb_gt_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    1 / 2 < pairwiseProb v x y ↔ v y < v x := by
  rw [pairwiseProb, lt_div_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) ≥ 1/2` iff `v x ≥ v y`. -/
theorem pairwiseProb_ge_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    1 / 2 ≤ pairwiseProb v x y ↔ v y ≤ v x := by
  rw [pairwiseProb, le_div_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) < 1/2` iff `v x < v y`. -/
theorem pairwiseProb_lt_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y < 1 / 2 ↔ v x < v y := by
  rw [pairwiseProb, div_lt_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) = 1/2` iff `v x = v y`. -/
theorem pairwiseProb_eq_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y = 1 / 2 ↔ v x = v y := by
  rw [pairwiseProb, div_eq_iff (ne_of_gt (add_pos hx hy))]
  constructor <;> intro h <;> linarith

/-- Monotonicity: `P(x, z) ≥ P(y, z)` iff `v x ≥ v y`. The function
    `t ↦ t / (t + c)` is monotone for `c > 0`, so pairwise probabilities
    against any fixed `z` mirror the ordering of scale values. -/
theorem pairwiseProb_mono_iff (hx : 0 < v x) (hy : 0 < v y) (hz : 0 < v z) :
    pairwiseProb v y z ≤ pairwiseProb v x z ↔ v y ≤ v x := by
  rw [pairwiseProb, pairwiseProb,
    div_le_div_iff₀ (add_pos hy hz) (add_pos hx hz)]
  constructor <;> intro h <;> nlinarith

/-- Constant-ratio law: two pairwise probabilities on the same scale agree
    iff the cross products of their scale values do. -/
theorem pairwiseProb_eq_pairwiseProb_iff {x' y' : A} (hx : 0 < v x)
    (hy : 0 < v y) (hx' : 0 < v x') (hy' : 0 < v y') :
    pairwiseProb v x y = pairwiseProb v x' y' ↔ v x * v y' = v x' * v y := by
  rw [pairwiseProb, pairwiseProb,
    div_eq_div_iff (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Fechnerian coordinates ([luce-1959] Ch. 2, §2.A.2, `u = log v`): on an
    exponential scale the pairwise rule is the logistic of the utility
    difference — the bridge from the Luce choice rule to logit choice. -/
theorem pairwiseProb_exp (u : A → ℝ) (x y : A) :
    pairwiseProb (fun a ↦ Real.exp (u a)) x y = Real.sigmoid (u x - u y) := by
  have hx := Real.exp_pos (u x)
  have hy := Real.exp_pos (u y)
  simp only [pairwiseProb, Real.sigmoid, neg_sub, Real.exp_sub]
  rw [inv_eq_one_div, div_eq_div_iff (by positivity) (by positivity)]
  field_simp

end PairwiseProb

/-- Binary choice from a pair: `probOn` on `{x, y}` is the pairwise kernel
    `pairwiseProb` on the model's scores in that state. -/
theorem LuceModel.probOn_pair [DecidableEq A] (ra : LuceModel S A)
    (s : S) {x y : A} (hne : x ≠ y) :
    ra.probOn s {x, y} x = pairwiseProb (ra.score s) x y := by
  rw [ra.probOn_eq_div s _ x (Finset.mem_insert_self x {y}),
    Finset.sum_pair hne]
  rfl

/-! ### Systems of choice probabilities and the forms of the choice axiom

`ChoiceFn` is [luce-1959]'s primitive: for each finite menu `T`, a probability
distribution `prob T` supported on `T`. Three single-clause forms of the
choice axiom for such a system, equivalent under imperfect discrimination:

* `HasRatioScale` — a positive `v` with `P(a | T) = v a / ∑ b ∈ T, v b`, the
  representation delivered by Theorem 3 (p. 23);
* `HasProductRule` — `P(a | T) = P(a | S) · P(S | T)` for `a ∈ S ⊆ T`, the
  shape of part i of Axiom 1 (p. 6);
* `HasPairwiseIIA` — odds ratios preserved in any superset, the
  constant-ratio rule of Lemma 3 (p. 9).

([luce-1959]'s own Appendix 1, "Alternative forms of axiom 1", p. 135, states
a different trio — conditions A–C on the rejection probabilities
`Q_T(S) = 1 − P_T(S)`, equivalent to part i by its Theorem 20 — which is not
formalized here.)

Luce's Axiom 1 itself is two-clause and weaker than the globally positive
ratio form: `ChoiceFn.HasChoiceAxiom` states it in full, and
`ChoiceFn.HasChoiceAxiom.ratioScaleOn` is the existence half of his Theorem 3
(local ratio scales on imperfectly discriminated menus). -/

section ChoiceAxiomForms

/-- A system of choice probabilities over finite menus — the primitive of
    [luce-1959]. For each nonempty menu `T`, `prob T : A → ℝ` is a
    probability distribution supported on `T`. -/
structure ChoiceFn (A : Type*) where
  /-- `prob T a`: the probability of choosing `a` from the menu `T`. -/
  prob : Finset A → A → ℝ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ (T : Finset A) (a : A), 0 ≤ prob T a
  /-- No probability outside the menu. -/
  prob_zero_outside : ∀ (T : Finset A) (a : A), a ∉ T → prob T a = 0
  /-- Probabilities sum to 1 on a nonempty menu. -/
  prob_sum_eq_one : ∀ T : Finset A, T.Nonempty → ∑ a ∈ T, prob T a = 1

namespace ChoiceFn

variable {A : Type*} [DecidableEq A]

/-- Binary forced choice: the probability of choosing `x` from `{x, y}`. -/
def binary (cf : ChoiceFn A) (x y : A) : ℝ := cf.prob {x, y} x

theorem binary_nonneg (cf : ChoiceFn A) (x y : A) : 0 ≤ cf.binary x y :=
  cf.prob_nonneg _ _

theorem binary_le_one (cf : ChoiceFn A) (x y : A) : cf.binary x y ≤ 1 :=
  le_of_le_of_eq
    (Finset.single_le_sum (fun a _ ↦ cf.prob_nonneg {x, y} a)
      (Finset.mem_insert_self x _))
    (cf.prob_sum_eq_one _ ⟨x, Finset.mem_insert_self x _⟩)

/-- Binary complementarity: `P(x, y) + P(y, x) = 1` for `x ≠ y`. -/
theorem binary_complement (cf : ChoiceFn A) {x y : A} (hxy : x ≠ y) :
    cf.binary x y + cf.binary y x = 1 := by
  simp only [binary, Finset.pair_comm y x]
  rw [← Finset.sum_pair hxy]
  exact cf.prob_sum_eq_one _ ⟨x, Finset.mem_insert_self x _⟩

/-- Self-choice is certain: `{x, x} = {x}`, so `binary x x = 1` — where
    [luce-1959] (p. 5) instead sets `P(x, x) = ½` by notational
    convention. -/
theorem binary_self (cf : ChoiceFn A) (x : A) : cf.binary x x = 1 := by
  simpa [binary] using cf.prob_sum_eq_one {x} ⟨x, Finset.mem_singleton_self x⟩

/-- **Ratio form** of the choice axiom: a positive scale `v` with
    `P(a | T) = v a / ∑ b ∈ T, v b` — the representation delivered by
    Theorem 3 of [luce-1959] (p. 23) in the globally imperfect regime. -/
def HasRatioScale (cf : ChoiceFn A) : Prop :=
  ∃ v : A → ℝ, (∀ a, 0 < v a) ∧
    ∀ (T : Finset A) (a : A), a ∈ T → cf.prob T a = v a / ∑ b ∈ T, v b

/-- **Product rule** form of the choice axiom:
    `P(a | T) = P(a | S) · P(S | T)` for `a ∈ S ⊆ T`, where
    `P(S | T) = ∑ b ∈ S, P(b | T)` — the shape of part i of Axiom 1
    ([luce-1959], p. 6). -/
def HasProductRule (cf : ChoiceFn A) : Prop :=
  ∀ S T : Finset A, S ⊆ T → S.Nonempty →
    ∀ a ∈ S, cf.prob T a = cf.prob S a * ∑ b ∈ S, cf.prob T b

/-- **Pairwise IIA** form of the choice axiom (the constant-ratio rule,
    Lemma 3 of [luce-1959], p. 9): odds ratios are preserved in any
    superset — `P(a | T) · P(b | {a,b}) = P(b | T) · P(a | {a,b})`. -/
def HasPairwiseIIA (cf : ChoiceFn A) : Prop :=
  ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
    cf.prob T a * cf.prob {a, b} b = cf.prob T b * cf.prob {a, b} a

omit [DecidableEq A] in
/-- The ratio form implies the product rule. -/
theorem HasRatioScale.hasProductRule {cf : ChoiceFn A}
    (h : cf.HasRatioScale) : cf.HasProductRule := by
  intro S T hST hS a ha
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  rw [hv_rule T a (hST ha), hv_rule S a ha,
    Finset.sum_congr rfl fun b hb ↦ hv_rule T b (hST hb), ← Finset.sum_div]
  have hS_ne : (∑ b ∈ S, v b) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun b _ ↦ hv_pos b) hS)
  have hT_ne : (∑ b ∈ T, v b) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun b _ ↦ hv_pos b) (hS.mono hST))
  field_simp

/-- The ratio form implies pairwise IIA. -/
theorem HasRatioScale.hasPairwiseIIA {cf : ChoiceFn A}
    (h : cf.HasRatioScale) : cf.HasPairwiseIIA := by
  intro T a b ha hb
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  rw [hv_rule T a ha, hv_rule T b hb, hv_rule {a, b} b (by simp),
    hv_rule {a, b} a (Finset.mem_insert_self a _)]
  ring

/-- Pairwise IIA implies the ratio form, given strict positivity on every
    menu. The scale is built from a reference element `x₀` as
    `v x = P(x | {x, x₀}) / P(x₀ | {x, x₀})` — the chain construction of
    Theorem 4 of [luce-1959] (p. 25) in the one-link case. -/
theorem HasPairwiseIIA.hasRatioScale [Inhabited A] {cf : ChoiceFn A}
    (hIIA : cf.HasPairwiseIIA)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < cf.prob T a) :
    cf.HasRatioScale := by
  have hsum := cf.prob_sum_eq_one
  set x₀ := (default : A)
  set v := fun a ↦ cf.prob {a, x₀} a / cf.prob {a, x₀} x₀ with hv_def
  have hv_pos : ∀ a, 0 < v a := fun a ↦
    div_pos (hpos _ a (mem_insert.mpr (Or.inl rfl))) (hpos _ x₀ (by simp))
  have ratio_mul : ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
      cf.prob T a * cf.prob {b, x₀} b * cf.prob {a, x₀} x₀ =
      cf.prob T b * cf.prob {a, x₀} a * cf.prob {b, x₀} x₀ := by
    intro T a b ha hb
    set T' := insert x₀ T
    have ha' : a ∈ T' := mem_insert_of_mem ha
    have hb' : b ∈ T' := mem_insert_of_mem hb
    have hx₀' : x₀ ∈ T' := mem_insert_self x₀ T
    have hT := hIIA T a b ha hb
    have hT'ab := hIIA T' a b ha' hb'
    have hT'ax₀ := hIIA T' a x₀ ha' hx₀'
    have hT'bx₀ := hIIA T' b x₀ hb' hx₀'
    have hB : cf.prob T' a * cf.prob {a, x₀} x₀ * cf.prob {b, x₀} b =
              cf.prob T' b * cf.prob {b, x₀} x₀ * cf.prob {a, x₀} a := by
      linear_combination cf.prob {b, x₀} b * hT'ax₀ - cf.prob {a, x₀} a * hT'bx₀
    have hA_mul : (cf.prob T a * cf.prob T' b - cf.prob T b * cf.prob T' a) *
                  cf.prob {a, b} b = 0 := by
      linear_combination cf.prob T' b * hT - cf.prob T b * hT'ab
    have hA : cf.prob T a * cf.prob T' b = cf.prob T b * cf.prob T' a := by
      rcases mul_eq_zero.mp hA_mul with h | h
      · linarith
      · exact absurd h (ne_of_gt (hpos _ b (by simp)))
    have hT'b_ne : cf.prob T' b ≠ 0 := ne_of_gt (hpos T' b hb')
    have h1 : cf.prob T' b *
          (cf.prob T a * cf.prob {b, x₀} b * cf.prob {a, x₀} x₀) =
        cf.prob T' b *
          (cf.prob T b * cf.prob {a, x₀} a * cf.prob {b, x₀} x₀) := by
      linear_combination
        cf.prob {b, x₀} b * cf.prob {a, x₀} x₀ * hA + cf.prob T b * hB
    exact mul_left_cancel₀ hT'b_ne h1
  refine ⟨v, hv_pos, fun T a ha ↦ ?_⟩
  have hT_ne : T.Nonempty := ⟨a, ha⟩
  have hsum_v_pos : 0 < ∑ b ∈ T, v b :=
    Finset.sum_pos (fun b _ ↦ hv_pos b) hT_ne
  rw [eq_div_iff (ne_of_gt hsum_v_pos)]
  have swap : ∀ b ∈ T, cf.prob T a * v b = v a * cf.prob T b := by
    intro b hb
    simp only [hv_def]
    have hrm := ratio_mul T a b ha hb
    have hne_a : cf.prob {a, x₀} x₀ ≠ 0 := ne_of_gt (hpos _ x₀ (by simp))
    have hne_b : cf.prob {b, x₀} x₀ ≠ 0 := ne_of_gt (hpos _ x₀ (by simp))
    field_simp
    linarith
  calc cf.prob T a * ∑ b ∈ T, v b
      = ∑ b ∈ T, cf.prob T a * v b := mul_sum T v (cf.prob T a)
    _ = ∑ b ∈ T, v a * cf.prob T b := sum_congr rfl swap
    _ = v a * ∑ b ∈ T, cf.prob T b := (mul_sum T (cf.prob T) (v a)).symm
    _ = v a * 1 := by rw [hsum T hT_ne]
    _ = v a := mul_one _

/-- Equivalence of the ratio form and pairwise IIA, under strict positivity
    on each menu. -/
theorem hasRatioScale_iff_hasPairwiseIIA [Inhabited A] (cf : ChoiceFn A)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < cf.prob T a) :
    cf.HasRatioScale ↔ cf.HasPairwiseIIA :=
  ⟨HasRatioScale.hasPairwiseIIA, fun h ↦ h.hasRatioScale hpos⟩

/-- A positive binary ratio scale on a set `S`: binary choice between
    distinct elements of `S` follows the Luce rule
    `P(x, y) = v x / (v x + v y)`.

    This is the binary trace of `HasRatioScale` restricted to `S`
    (`ChoiceFn.HasRatioScale.binaryRatioScaleOn`). Keeping `S` local matters
    for [luce-1959]'s Chapter 3, which mixes imperfect discrimination (a
    ratio scale on a small set of gambles, via Theorem 4) with perfect
    discrimination (`P ∈ {0, 1}`) elsewhere — a global positive scale forces
    every binary probability into `(0, 1)`. Restricting to distinct pairs
    matters because `binary x x = 1 ≠ 1/2` (`ChoiceFn.binary_self`). -/
def BinaryRatioScaleOn (cf : ChoiceFn A) (S : Set A) (v : A → ℝ) : Prop :=
  (∀ x ∈ S, 0 < v x) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → cf.binary x y = pairwiseProb v x y

/-- A global ratio scale restricts to a binary ratio scale on every set. -/
theorem HasRatioScale.binaryRatioScaleOn {cf : ChoiceFn A}
    (h : cf.HasRatioScale) :
    ∃ v : A → ℝ, ∀ S : Set A, cf.BinaryRatioScaleOn S v := by
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  refine ⟨v, fun S ↦ ⟨fun x _ ↦ hv_pos x, fun x _ y _ hxy ↦ ?_⟩⟩
  rw [ChoiceFn.binary, hv_rule {x, y} x (Finset.mem_insert_self x _),
    Finset.sum_pair hxy, pairwiseProb]

/-! ### The choice axiom in full -/

/-- Discrimination is imperfect throughout `T`: `0 < P(x, y) < 1` for
    distinct `x, y ∈ T` ([luce-1959]'s "`P(x, y) ≠ 0, 1` for all
    `x, y ∈ T`"). The diagonal is excluded because [luce-1959] (p. 5) sets
    `P(x, x) = ½` by pure notational convention, whereas a total `ChoiceFn`
    has `binary x x = 1` (`ChoiceFn.binary_self`). -/
def ImperfectOn (cf : ChoiceFn A) (T : Finset A) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 0 < cf.binary x y ∧ cf.binary x y < 1

/-- **Luce's choice axiom**, both clauses (Axiom 1, p. 6 of [luce-1959],
    with `P_T(S) = ∑ a ∈ S, P_T(a)`):

    (i) `product_rule`: under imperfect discrimination throughout `T`,
    nested-menu probabilities compose multiplicatively —
    `P_T(R) = P_S(R) · P_T(S)` for `R ⊆ S ⊆ T`;

    (ii) `deletion`: an alternative `x` never chosen over some `y` may be
    deleted — `P_T(S) = P_{T∖{x}}(S∖{x})` for every `S ⊆ T`.

    Unlike the globally positive `HasRatioScale`, clause (ii) lets the axiom
    govern menus mixing perfect and imperfect discrimination — the regime of
    [luce-1959] Chapter 3, where the three-class theorems force `Q ∈ {0, 1}`
    between extreme event classes. -/
structure HasChoiceAxiom (cf : ChoiceFn A) : Prop where
  product_rule : ∀ T : Finset A, cf.ImperfectOn T → ∀ R S : Finset A,
    R ⊆ S → S ⊆ T →
    ∑ a ∈ R, cf.prob T a = (∑ a ∈ R, cf.prob S a) * ∑ a ∈ S, cf.prob T a
  deletion : ∀ T : Finset A, ∀ x ∈ T, ∀ y ∈ T, x ≠ y → cf.binary x y = 0 →
    ∀ S ⊆ T, ∑ a ∈ S, cf.prob T a = ∑ a ∈ S.erase x, cf.prob (T.erase x) a

/-- A global ratio scale satisfies the full choice axiom: clause (i) by
    ratio arithmetic, clause (ii) vacuously (no discrimination is
    perfect). -/
theorem HasRatioScale.hasChoiceAxiom {cf : ChoiceFn A}
    (h : cf.HasRatioScale) : cf.HasChoiceAxiom := by
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  constructor
  · intro T _ R S hRS hST
    rcases R.eq_empty_or_nonempty with rfl | hR
    · simp
    have hS : S.Nonempty := hR.mono hRS
    have hSne : (∑ b ∈ S, v b) ≠ 0 :=
      ne_of_gt (Finset.sum_pos (fun b _ ↦ hv_pos b) hS)
    have hTne : (∑ b ∈ T, v b) ≠ 0 :=
      ne_of_gt (Finset.sum_pos (fun b _ ↦ hv_pos b) (hS.mono hST))
    have eT : ∀ W : Finset A, W ⊆ T →
        ∑ a ∈ W, cf.prob T a = (∑ a ∈ W, v a) / ∑ b ∈ T, v b := by
      intro W hW
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a ha ↦ hv_rule T a (hW ha)
    have eS : ∑ a ∈ R, cf.prob S a = (∑ a ∈ R, v a) / ∑ b ∈ S, v b := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a ha ↦ hv_rule S a (hRS ha)
    rw [eT R (hRS.trans hST), eT S hST, eS]
    field_simp
  · intro T x hx y hy hxy h0 S hS
    have hb : cf.binary x y = v x / (v x + v y) := by
      rw [ChoiceFn.binary, hv_rule {x, y} x (Finset.mem_insert_self x _),
        Finset.sum_pair hxy]
    rw [hb] at h0
    exact absurd h0
      (ne_of_gt (div_pos (hv_pos x) (add_pos (hv_pos x) (hv_pos y))))

/-- Existence half of **Theorem 3** of [luce-1959] (p. 23): under the choice
    axiom, on any finite `T` with imperfect discrimination throughout, the
    restricted choice probabilities are a ratio scale — with `v = P_T`
    itself as the scale, Luce's own construction. The uniqueness half is
    `ChoiceFn.ratioScaleOn_unique`. -/
theorem HasChoiceAxiom.ratioScaleOn {cf : ChoiceFn A}
    (h : cf.HasChoiceAxiom) {T : Finset A} (hT : T.Nonempty)
    (himp : cf.ImperfectOn T) :
    ∃ v : A → ℝ, (∀ x ∈ T, 0 < v x) ∧
      ∀ S ⊆ T, ∀ a ∈ S, cf.prob S a = v a / ∑ b ∈ S, v b := by
  have hpos : ∀ x ∈ T, 0 < cf.prob T x := by
    intro x hx
    rcases lt_or_eq_of_le (cf.prob_nonneg T x) with hlt | heq
    · exact hlt
    -- a zero propagates to every element of T, contradicting the unit sum
    have hall : ∀ y ∈ T, cf.prob T y = 0 := by
      intro y hy
      rcases eq_or_ne y x with rfl | hyx
      · exact heq.symm
      have hsub : ({x, y} : Finset A) ⊆ T :=
        Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
      have hprod := h.product_rule T himp {x} {x, y} (by simp) hsub
      rw [Finset.sum_singleton, Finset.sum_singleton,
        Finset.sum_pair (Ne.symm hyx)] at hprod
      have hbin : 0 < cf.prob {x, y} x := (himp x hx y hy (Ne.symm hyx)).1
      have h0 : cf.prob {x, y} x * cf.prob T y = 0 := by
        rw [← heq] at hprod
        linarith [hprod]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (ne_of_gt hbin)
      · exact h'
    have hsum := cf.prob_sum_eq_one T hT
    rw [Finset.sum_eq_zero hall] at hsum
    exact absurd hsum (by norm_num)
  refine ⟨cf.prob T, hpos, fun S hS a ha ↦ ?_⟩
  have hSpos : (0 : ℝ) < ∑ b ∈ S, cf.prob T b :=
    Finset.sum_pos (fun b hb ↦ hpos b (hS hb)) ⟨a, ha⟩
  have hprod := h.product_rule T himp {a} S (Finset.singleton_subset_iff.mpr ha) hS
  rw [Finset.sum_singleton, Finset.sum_singleton] at hprod
  rw [eq_div_iff (ne_of_gt hSpos)]
  linarith [hprod]

omit [DecidableEq A] in
/-- Uniqueness half of **Theorem 3** of [luce-1959] (p. 23): two positive
    scales representing the same choice probabilities on the menu `T` agree
    on `T` up to a positive multiple. -/
theorem ratioScaleOn_unique {cf : ChoiceFn A} {T : Finset A} (hT : T.Nonempty)
    {v v' : A → ℝ} (hv : ∀ x ∈ T, 0 < v x) (hv' : ∀ x ∈ T, 0 < v' x)
    (hrule : ∀ a ∈ T, cf.prob T a = v a / ∑ b ∈ T, v b)
    (hrule' : ∀ a ∈ T, cf.prob T a = v' a / ∑ b ∈ T, v' b) :
    ∃ k : ℝ, 0 < k ∧ ∀ a ∈ T, v' a = k * v a := by
  have hsv : (0 : ℝ) < ∑ b ∈ T, v b := Finset.sum_pos hv hT
  have hsv' : (0 : ℝ) < ∑ b ∈ T, v' b := Finset.sum_pos hv' hT
  refine ⟨(∑ b ∈ T, v' b) / ∑ b ∈ T, v b, div_pos hsv' hsv, fun a ha ↦ ?_⟩
  have h := (hrule a ha).symm.trans (hrule' a ha)
  rw [div_eq_div_iff (ne_of_gt hsv) (ne_of_gt hsv')] at h
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hsv)]
  linarith

/-- Binary form of Theorem 3: the choice axiom plus imperfect discrimination
    on `T` yield a binary ratio scale on `T`. -/
theorem HasChoiceAxiom.binaryRatioScaleOn {cf : ChoiceFn A}
    (h : cf.HasChoiceAxiom) {T : Finset A} (hT : T.Nonempty)
    (himp : cf.ImperfectOn T) :
    ∃ v : A → ℝ, cf.BinaryRatioScaleOn ↑T v := by
  obtain ⟨v, hvpos, hrule⟩ := h.ratioScaleOn hT himp
  refine ⟨v, fun x hx ↦ hvpos x (Finset.mem_coe.mp hx),
    fun x hx y hy hxy ↦ ?_⟩
  have hsub : ({x, y} : Finset A) ⊆ T :=
    Finset.insert_subset (Finset.mem_coe.mp hx)
      (Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hy))
  rw [ChoiceFn.binary, hrule {x, y} hsub x (Finset.mem_insert_self x _),
    Finset.sum_pair hxy, pairwiseProb]

/-- **Theorem 2** of [luce-1959] (p. 16): under the choice axiom, imperfect
    pairwise discrimination on a triple forces the cyclic product identity
    `P(x,y)P(y,z)P(z,x) = P(x,z)P(z,y)P(y,x)` — a stochastic intransitivity
    is exactly as probable as its reverse. -/
theorem HasChoiceAxiom.binary_mul_cycle {cf : ChoiceFn A}
    (h : cf.HasChoiceAxiom) {x y z : A} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) (himp : cf.ImperfectOn {x, y, z}) :
    cf.binary x y * cf.binary y z * cf.binary z x =
      cf.binary x z * cf.binary z y * cf.binary y x := by
  obtain ⟨v, hpos, hrule⟩ :=
    h.binaryRatioScaleOn ⟨x, Finset.mem_insert_self x _⟩ himp
  have mx : x ∈ (↑({x, y, z} : Finset A) : Set A) := by simp
  have my : y ∈ (↑({x, y, z} : Finset A) : Set A) := by simp
  have mz : z ∈ (↑({x, y, z} : Finset A) : Set A) := by simp
  have px := hpos x mx
  have py := hpos y my
  have pz := hpos z mz
  have n1 : v x + v y ≠ 0 := ne_of_gt (add_pos px py)
  have n2 : v y + v z ≠ 0 := ne_of_gt (add_pos py pz)
  have n3 : v z + v x ≠ 0 := ne_of_gt (add_pos pz px)
  have n4 : v x + v z ≠ 0 := ne_of_gt (add_pos px pz)
  have n5 : v z + v y ≠ 0 := ne_of_gt (add_pos pz py)
  have n6 : v y + v x ≠ 0 := ne_of_gt (add_pos py px)
  rw [hrule x mx y my hxy, hrule y my z mz hyz, hrule z mz x mx (Ne.symm hxz),
    hrule x mx z mz hxz, hrule z mz y my (Ne.symm hyz),
    hrule y my x mx (Ne.symm hxy)]
  simp only [pairwiseProb]
  field_simp
  ring

end ChoiceFn

end ChoiceAxiomForms

end Core
