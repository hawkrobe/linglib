/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Discourse.CommonGround
import Linglib.Core.Probability.Constructions
import Linglib.Core.Probability.Entropy

/-!
# Distributional Common Ground

[anderson-2021]

A probability distribution over worlds representing the state of the
conversation. The probabilistic counterpart of [stalnaker-2002]'s sharp
set-membership context set: instead of a membership predicate (`W → Prop`),
the common ground assigns graded plausibility that **sums to one**
(Anderson 2021, §3.2: *"I model the Common Ground as a distribution over
worlds reflecting the state of the conversation"*).

## Carrier

`DistributionalCG W` wraps mathlib's `PMF W` — a genuine probability mass
function, not an unnormalised weight. This makes Anderson's success
criterion expressible: §3.2 measures conversational progress by the
**entropy** of the common ground (*"In a successful conversation, the
entropy of the Common Ground should decrease"*), and footnote 15 names KL
divergence as the perspective-alignment objective. Both `PMF.entropy` and
`PMF.klDiv` are available on the carrier.

## Substrate role

This file hosts:
- The `DistributionalCG W` structure over `PMF W`.
- `weight`/`weight_nonneg`/`sum_weight` — the ℝ-valued view of the masses
  (via `PMF.toRealFn`), the interface every RSA consumer reads.
- `toContextSet` projecting to the positive-mass worlds, with
  `toContextSet_eq_support` identifying it with mathlib's `PMF.support`.
- `uniform` — the genuine `1/|W|` distribution (`PMF.uniformOfFintype`),
  Anderson's empty/maximally-uncertain common ground.
- `ofWeights` — the renormalising constructor from non-negative weights
  (Anderson 2021, footnote 3: *"At each step, the probabilities are
  renormalized"*), built on `PMF.ofRealWeightFn`.
- The `HasContextSet (DistributionalCG W) W` instance.

The Anderson 2021 study (`Studies/Anderson2021.lean`) imports this
substrate and adds the conversation-update + RSA-bridge content on top.

## Non-monotonicity

Unlike Stalnaker's context set — where worlds, once excluded, stay
excluded — the distributional common ground is non-monotonic by design
(Anderson 2021, footnote 7: *"worlds can regain probability"*). The
classical set-intersection update is recovered only in the degenerate
limit; see `Anderson2021.lr_one_excludes_false_worlds` for the one
direction that survives, and `Anderson2021.graded_update_keeps_false_world`
for the divergence the graded model insists on.
-/

namespace Discourse

open CommonGround (ContextSet HasContextSet)

-- ════════════════════════════════════════════════════
-- § 1. DistributionalCG
-- ════════════════════════════════════════════════════

/-- A distributional common ground: a probability distribution over worlds
    ([anderson-2021], §3.2). The probabilistic counterpart of
    [stalnaker-2002]'s context set — instead of a sharp membership
    predicate (`W → Prop`), the common ground is a genuine `PMF W`,
    assigning graded plausibility that sums to one. -/
structure DistributionalCG (W : Type*) where
  /-- The probability distribution over worlds. -/
  dist : PMF W

namespace DistributionalCG

variable {W : Type*}

@[ext]
theorem ext {cg₁ cg₂ : DistributionalCG W} (h : cg₁.dist = cg₂.dist) :
    cg₁ = cg₂ := by
  cases cg₁; cases cg₂; simp_all

/-- The ℝ-valued masses of the common ground (via `PMF.toRealFn`). This is
    the interface every RSA consumer reads: it plugs directly into
    `RSAConfig.worldPrior`/`meaning`, which expect `W → ℝ`. -/
noncomputable def weight (cg : DistributionalCG W) : W → ℝ := cg.dist.toRealFn

@[simp] theorem weight_def (cg : DistributionalCG W) (w : W) :
    cg.weight w = (cg.dist w).toReal := rfl

/-- The masses are non-negative — *derived* from `PMF`, not stipulated as a
    structural invariant. -/
theorem weight_nonneg (cg : DistributionalCG W) (w : W) : 0 ≤ cg.weight w :=
  cg.dist.toRealFn_nonneg w

/-- Each mass is at most one. -/
theorem weight_le_one (cg : DistributionalCG W) (w : W) : cg.weight w ≤ 1 :=
  cg.dist.toRealFn_le_one w

/-- The masses sum to one — the normalisation Anderson's entropy/KL criteria
    depend on. -/
theorem sum_weight [Fintype W] (cg : DistributionalCG W) :
    ∑ w, cg.weight w = 1 :=
  cg.dist.sum_toRealFn_eq_one

/-- Shannon entropy of the common ground (Anderson 2021, §3.2: the success
    criterion is that this *decreases* over a conversation). -/
noncomputable def entropy [Fintype W] (cg : DistributionalCG W) : ℝ :=
  cg.dist.entropy

theorem entropy_nonneg [Fintype W] (cg : DistributionalCG W) : 0 ≤ cg.entropy :=
  cg.dist.entropy_nonneg

/-- Bridge to classical context set: a world is "in the context" iff its
    mass is positive. Recovers [stalnaker-2002]'s set-membership view from
    the distributional representation. -/
def toContextSet (cg : DistributionalCG W) : ContextSet W :=
  fun w => 0 < cg.weight w

@[simp] theorem toContextSet_apply (cg : DistributionalCG W) (w : W) :
    cg.toContextSet w ↔ 0 < cg.weight w := Iff.rfl

/-- The positive-mass projection coincides with mathlib's `PMF.support`. -/
theorem toContextSet_eq_support (cg : DistributionalCG W) :
    cg.toContextSet = cg.dist.support := by
  ext w
  show 0 < cg.weight w ↔ w ∈ cg.dist.support
  rw [weight_def, PMF.mem_support_iff, ENNReal.toReal_pos_iff, pos_iff_ne_zero]
  exact and_iff_left (lt_top_iff_ne_top.mpr (cg.dist.apply_ne_top w))

/-- A world with zero mass is excluded from the classical context set. -/
theorem zero_weight_excluded (cg : DistributionalCG W) (w : W)
    (h : cg.weight w = 0) : ¬cg.toContextSet w := by
  rw [toContextSet_apply, h]; exact lt_irrefl 0

-- ════════════════════════════════════════════════════
-- § 2. Uniform common ground
-- ════════════════════════════════════════════════════

/-- The uniform common ground: every world equally plausible at `1/|W|`
    (Anderson 2021: `CG = Uniform(worlds)`, the empty/maximally-uncertain
    starting point). A genuine distribution, via `PMF.uniformOfFintype`. -/
noncomputable def uniform [Fintype W] [Nonempty W] : DistributionalCG W :=
  ⟨PMF.uniformOfFintype W⟩

@[simp] theorem uniform_weight [Fintype W] [Nonempty W] (w : W) :
    (uniform : DistributionalCG W).weight w = (Fintype.card W : ℝ)⁻¹ := by
  show ((PMF.uniformOfFintype W) w).toReal = _
  rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The uniform common ground maps to the trivial (universal) context set:
    every world has positive mass. -/
theorem uniform_toContextSet [Fintype W] [Nonempty W] :
    (uniform : DistributionalCG W).toContextSet = ContextSet.trivial := by
  ext w
  show 0 < (uniform : DistributionalCG W).weight w ↔ w ∈ ContextSet.trivial
  rw [uniform_weight]
  simp only [ContextSet.trivial, Set.mem_univ, iff_true]
  positivity

-- ════════════════════════════════════════════════════
-- § 3. Renormalising constructor
-- ════════════════════════════════════════════════════

/-- Build a common ground from non-negative `ℝ` weights by renormalising
    (Anderson 2021, footnote 3: *"the probabilities are renormalized"*).
    Routes through `PMF.ofRealWeightFn`; the positivity witness is derived
    from the positive total. -/
noncomputable def ofWeights [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) : DistributionalCG W :=
  have hex : ∃ w, 0 < f w := by
    by_contra h
    push_neg at h
    exact absurd hpos (not_lt.mpr (Finset.sum_nonpos fun w _ => h w))
  ⟨PMF.ofRealWeightFn f hn hex.choose hex.choose_spec⟩

/-- The support of a renormalised common ground is the set of
    strictly-positive weights — normalisation preserves the support. -/
theorem ofWeights_toContextSet [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) :
    (ofWeights f hn hpos).toContextSet = {w | 0 < f w} := by
  rw [toContextSet_eq_support, ofWeights, PMF.support_ofRealWeightFn]

/-- Closed form of a renormalised mass: each weight divided by the total.
    Anderson's renormalisation made explicit (`CG(w) = f(w) / Σ f`). -/
theorem ofWeights_weight_eq [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) (w : W) :
    (ofWeights f hn hpos).weight w = f w / (∑ x, f x) := by
  simp only [weight_def, ofWeights, PMF.ofRealWeightFn_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hn w),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => hn x), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hpos.le, div_eq_mul_inv]

/-- Renormalisation preserves the strict ordering of weights — the same
    positive total divides both sides. Drives the "beliefs favour world
    `w`" comparisons. -/
theorem ofWeights_weight_lt_iff [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) (w₁ w₂ : W) :
    (ofWeights f hn hpos).weight w₁ < (ofWeights f hn hpos).weight w₂ ↔
      f w₁ < f w₂ := by
  rw [ofWeights_weight_eq, ofWeights_weight_eq, div_lt_div_iff_of_pos_right hpos]

/-- Renormalising an already-normalised weight vector recovers it exactly. -/
theorem ofWeights_weight [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) (hsum : ∑ w, f w = 1) (w : W) :
    (ofWeights f hn hpos).weight w = f w := by
  rw [ofWeights_weight_eq, hsum, div_one]

end DistributionalCG

/-- A distributional common ground projects to a context set: the worlds
    with positive mass. -/
instance {W : Type*} : HasContextSet (DistributionalCG W) W where
  toContextSet := DistributionalCG.toContextSet

end Discourse
