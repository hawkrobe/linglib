import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Core.Probability.Choice.Learning
import Linglib.Discourse.CommonGround
import Linglib.Core.Probability.Constructions
import Linglib.Core.Probability.Entropy

/-!
# Anderson (2021): Conversation Update for RSA

[anderson-2021]

A system for multi-turn conversation update in the Rational Speech Acts
framework. The core contributions:

1. **Common ground as distribution**: the CommonGround is a probability distribution
   over worlds, substituted directly for the RSA world prior
2. **Learning-rate update**: CommonGround evolves via convex combination with
   Pragmatic Listener posteriors
3. **Shared vs. approximate CommonGround**: two models differing in whether
   participants share a single CommonGround representation
4. **Observation sampling**: weighted, thresholded, and difference-based
   strategies for cooperative speaker behavior

## Key Connections

The CommonGround update rule `CommonGround'(w) = (1-lr)·CommonGround(w) + lr·post(w)` is algebraically
identical to [luce-1959]'s linear learning rule with retention rate
`1-lr` and reinforcement target `post`. This connects RSA pragmatics to
learning theory: multi-turn conversation IS iterated learning over
distributions.

The distributional CommonGround refines [stalnaker-2002]'s classical context set:
worlds with zero weight are excluded from the context, recovering
set-intersection update as a special case.

## BToM Connection

Anderson's distributional CommonGround has the type expected by `BToMModel.sharedUpdate`
(`Shared → Action → World → Shared`). Setting `Shared := DistributionalCG W`
instantiates BToM's discourse dynamics for the first time in linglib — the
shared state is a distribution that evolves after each utterance via the
learning-rate update.

## MutualFriends Domain

The paper illustrates predictions using the MutualFriends dataset, where
worlds are individuals characterized by features (major, location) and
utterances describe those features.
-/

/-!### Distributional Common Ground

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
    ℝ-valued consumers (`updateCG`, the samplers), which expect `W → ℝ`. -/
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
    push Not at h
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


namespace Anderson2021

open CommonGround (ContextSet)

-- ════════════════════════════════════════════════════
-- § 1. MutualFriends Domain
-- ════════════════════════════════════════════════════

/-- Worlds in the MutualFriends domain: four individuals with different
feature combinations. -/
inductive MFWorld where
  | ina    -- Astronomy, Indoors
  | katie  -- Astronomy, Outdoors
  | nancy  -- German, Outdoors
  | sally  -- German, Indoors
  deriving DecidableEq, Repr, Inhabited

instance : Fintype MFWorld where
  elems := {.ina, .katie, .nancy, .sally}
  complete x := by cases x <;> simp

theorem card_mfworld : Fintype.card MFWorld = 4 := by decide

inductive Major where | astronomy | german
  deriving DecidableEq, Repr

inductive Location where | indoors | outdoors
  deriving DecidableEq, Repr

def worldMajor : MFWorld → Major
  | .ina | .katie => .astronomy
  | .nancy | .sally => .german

def worldLocation : MFWorld → Location
  | .ina | .sally => .indoors
  | .katie | .nancy => .outdoors

/-- Utterances available to speakers. Includes a null utterance for
passing when the speaker has no confident observation to share. -/
inductive MFUtterance where
  | studyHumanity   -- "They study a humanity"
  | studyScience    -- "They study a science"
  | likeIndoors     -- "They like being indoors"
  | likeOutdoors    -- "They like being outdoors"
  | null            -- Speaker passes
  deriving DecidableEq, Repr, Inhabited

instance : Fintype MFUtterance where
  elems := {.studyHumanity, .studyScience, .likeIndoors, .likeOutdoors, .null}
  complete x := by cases x <;> simp

/-- Truth-conditional semantics for MutualFriends utterances. -/
def mfMeaning : MFUtterance → MFWorld → Bool
  | .studyHumanity, w => worldMajor w == .german
  | .studyScience, w => worldMajor w == .astronomy
  | .likeIndoors, w => worldLocation w == .indoors
  | .likeOutdoors, w => worldLocation w == .outdoors
  | .null, _ => true

example : mfMeaning .studyHumanity .nancy = true := rfl
example : mfMeaning .studyScience .nancy = false := rfl
example : mfMeaning .likeOutdoors .katie = true := rfl
example : mfMeaning .null .ina = true := rfl

/-- Each non-null utterance partitions the world space in half. -/
theorem studyHumanity_partition :
    (mfMeaning .studyHumanity .nancy = true) ∧
    (mfMeaning .studyHumanity .sally = true) ∧
    (mfMeaning .studyHumanity .ina = false) ∧
    (mfMeaning .studyHumanity .katie = false) := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Distributional Common Ground (re-exported from substrate)
-- ════════════════════════════════════════════════════

/-! `DistributionalCG` (a `PMF W` over worlds), its `weight`/`toContextSet`
    projections, the `uniform` distribution, the `ofWeights` renormaliser,
    and the `HasContextSet` instance are all hosted in the substrate file
    the substrate section above. The Anderson study below builds the
    conversation-update + RSA-bridge content on those primitives. -/

open Discourse (DistributionalCG)

-- ════════════════════════════════════════════════════
-- § 3. CommonGround Update
-- ════════════════════════════════════════════════════

/-- Convex-combination update for distributional common ground:

    CommonGround'(w) = (1 - lr) · CommonGround(w) + lr · posterior(w)

Both inputs are genuine distributions, so the `lr`-weighted mixture is
automatically a distribution (no renormalisation needed) — built as a
`PMF.ofFintype` mixture, exactly mirroring `PMF.midPMF`'s `1/2` case. The
learning rate `lr ∈ [0,1]` controls how much weight is given to new
information vs. the existing CommonGround. -/
noncomputable def updateCG {W : Type*} [Fintype W] (cg post : DistributionalCG W)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) : DistributionalCG W :=
  ⟨PMF.ofFintype
    (fun w => ENNReal.ofReal (1 - lr) * cg.dist w + ENNReal.ofReal lr * post.dist w)
    (by
      have hcg : (∑ w, cg.dist w) = 1 :=
        (tsum_eq_sum (fun w (h : w ∉ Finset.univ) =>
          absurd (Finset.mem_univ w) h)).symm.trans (PMF.tsum_coe cg.dist)
      have hpost : (∑ w, post.dist w) = 1 :=
        (tsum_eq_sum (fun w (h : w ∉ Finset.univ) =>
          absurd (Finset.mem_univ w) h)).symm.trans (PMF.tsum_coe post.dist)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcg, hpost,
        mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) hlr, sub_add_cancel,
        ENNReal.ofReal_one])⟩

/-- The CommonGround update is the convex combination
`(1 - lr) · CommonGround(w) + lr · posterior(w)`, exactly — both inputs sum
to one, so the mixture preserves total mass with no rescaling. -/
theorem updateCG_eq {W : Type*} [Fintype W] (cg post : DistributionalCG W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg post lr h0 h1).weight w =
    (1 - lr) * cg.weight w + lr * post.weight w := by
  simp only [DistributionalCG.weight_def, updateCG, PMF.ofFintype_apply]
  rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (cg.dist.apply_ne_top w))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (post.dist.apply_ne_top w)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - lr), ENNReal.toReal_ofReal h0]

/-- **Bridge to [luce-1959] linear learning**: the CommonGround update has the same
algebraic form as `LinearLearner.update` with retention rate `1 - lr` and
reinforcement target `posterior`:

    CommonGround'(w) = (1 - lr) · CommonGround(w) + lr · posterior(w)     [Anderson]
    v'(a)  = α · v(a) + (1 - α) · r(a)                [Luce §4.C]

Setting `α = 1 - lr` and `r = posterior` makes the formulas identical.
Multi-turn conversation IS iterated learning over distributions. -/
theorem updateCG_matches_linear_learning {W : Type*} [Fintype W]
    (cg post : DistributionalCG W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg post lr h0 h1).weight w =
    ((1 - lr) * cg.weight w + (1 - (1 - lr)) * post.weight w : ℝ) := by
  rw [updateCG_eq]; ring

/-- With learning rate 0, the CommonGround is unchanged (full retention). -/
theorem updateCG_lr_zero {W : Type*} [Fintype W] (cg post : DistributionalCG W)
    (w : W) :
    (updateCG cg post 0 (le_refl 0) zero_le_one).weight w = cg.weight w := by
  rw [updateCG_eq]; ring

/-- With learning rate 1, the CommonGround is replaced by the posterior. -/
theorem updateCG_lr_one {W : Type*} [Fintype W] (cg post : DistributionalCG W)
    (w : W) :
    (updateCG cg post 1 zero_le_one (le_refl 1)).weight w = post.weight w := by
  rw [updateCG_eq]; ring

-- ════════════════════════════════════════════════════
-- § 4. Conversation State
-- ════════════════════════════════════════════════════

/-- The state of a two-participant conversation (Figure 2).

Tracks the common ground (distributional), each participant's private
beliefs, and the learning rate for updates. In the **shared CommonGround** model
(§5.1, Figure 4), both participants access the same `cg`. In the
**approximate CommonGround** model (§5.2, Figure 6), each maintains a separate
approximation (not yet formalized).

The distributional CommonGround enters the RSA model at two points
(Figure 4): inside the literal listener and as the pragmatic listener's
prior. At each turn the chain is rebuilt at the current CommonGround
(`cgS1Total`/`conversationStep`). -/
structure ConversationState (W : Type*) where
  cg : DistributionalCG W
  belA : DistributionalCG W
  belB : DistributionalCG W
  lr : ℝ
  speakerIsA : Bool

/-- Initial conversation state: uniform CommonGround, specified beliefs, A speaks first. -/
noncomputable def ConversationState.initial {W : Type*} [Fintype W] [Nonempty W]
    (belA belB : DistributionalCG W) (lr : ℝ) : ConversationState W where
  cg := DistributionalCG.uniform
  belA := belA
  belB := belB
  lr := lr
  speakerIsA := true

-- ════════════════════════════════════════════════════
-- § 5. Observation Sampling
-- ════════════════════════════════════════════════════

/-- **Weighted sampling**: sample a world proportional to the speaker's belief.
Biased toward truth (zero-probability worlds are never sampled) but can
lead to flip-flopping when the speaker has no strong beliefs. -/
noncomputable def weightedSample {W : Type*} (bel : DistributionalCG W) : W → ℝ :=
  bel.weight

/-- **Thresholded sampling**: filter out worlds below a confidence threshold.
If no world exceeds the threshold, the speaker produces the null utterance
(passes). Prevents noncommittal speakers from making random assertions. -/
noncomputable def thresholdedSample {W : Type*}
    (bel : DistributionalCG W) (θ : ℝ) : W → ℝ :=
  λ w => if bel.weight w ≥ θ then bel.weight w else 0

/-- **Difference-based sampling**: weight worlds by the positive difference
between the speaker's belief and the current CommonGround. Worlds already established
in the CommonGround get downweighted, favoring informative (non-redundant) contributions.

    weight(w) = max(0, Bel(w) - CommonGround(w))

This implements a pressure toward Gricean Quantity: don't repeat what's
already in the common ground. -/
noncomputable def differenceSample {W : Type*}
    (bel cg : DistributionalCG W) : W → ℝ :=
  λ w => max 0 (bel.weight w - cg.weight w)

theorem differenceSample_nonneg {W : Type*}
    (bel cg : DistributionalCG W) (w : W) :
    0 ≤ differenceSample bel cg w :=
  le_max_left 0 _

-- ════════════════════════════════════════════════════
-- § 6. BToM Shared-State Update
-- ════════════════════════════════════════════════════

/-- Anderson's CommonGround update expressed as a BToM shared-state update.

Given a fixed posterior-computation function (from RSA inference), the CommonGround
update has the type required by `BToMModel.sharedUpdate`:

    Shared → Action → World → Shared

with `Shared := DistributionalCG W` and `Action := U`.

The `World` parameter is unused: the listener doesn't know the true world,
so the CommonGround update depends on the *posterior* (derived from the utterance),
not the true world directly. -/
noncomputable def toBToMSharedUpdate {W U : Type*} [Fintype W]
    (posteriorFn : U → DistributionalCG W)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    DistributionalCG W → U → W → DistributionalCG W :=
  fun cg u _w => updateCG cg (posteriorFn u) lr hlr hlr1

-- ════════════════════════════════════════════════════
-- § 7. Example Beliefs
-- ════════════════════════════════════════════════════

/-- The unnormalised belief weights: `peak` on one world, `1` elsewhere.
Their total over the four MutualFriends worlds is `6`. -/
private theorem mfWorld_sum_peak (peak : ℝ) (p : MFWorld) :
    (∑ x : MFWorld, if x = p then peak else 1) = peak + 3 := by
  rw [show (Finset.univ : Finset MFWorld) = {.ina, .katie, .nancy, .sally} from rfl]
  cases p <;>
    simp [Finset.sum_insert, Finset.mem_insert] <;> ring

/-- A believes the person is Nancy: (unnormalised) weight 3 on Nancy, 1 on
others — renormalised to the distribution `[1/6, 1/6, 1/2, 1/6]`. -/
noncomputable def beliefsA : DistributionalCG MFWorld :=
  DistributionalCG.ofWeights (fun w => if w = .nancy then 3 else 1)
    (fun w => by split <;> norm_num)
    (Finset.sum_pos' (fun w _ => by split <;> norm_num)
      ⟨.nancy, Finset.mem_univ _, by rw [if_pos rfl]; norm_num⟩)

/-- B believes the person is Katie: (unnormalised) weight 3 on Katie, 1 on
others — renormalised to the distribution `[1/6, 1/2, 1/6, 1/6]`. -/
noncomputable def beliefsB : DistributionalCG MFWorld :=
  DistributionalCG.ofWeights (fun w => if w = .katie then 3 else 1)
    (fun w => by split <;> norm_num)
    (Finset.sum_pos' (fun w _ => by split <;> norm_num)
      ⟨.katie, Finset.mem_univ _, by rw [if_pos rfl]; norm_num⟩)

/-- Closed form of A's renormalised beliefs: `3/6` on Nancy, `1/6` elsewhere. -/
theorem beliefsA_weight (w : MFWorld) :
    beliefsA.weight w = (if w = .nancy then 3 else 1) / 6 := by
  rw [beliefsA, DistributionalCG.ofWeights_weight_eq, mfWorld_sum_peak]; norm_num

/-- Closed form of B's renormalised beliefs: `3/6` on Katie, `1/6` elsewhere. -/
theorem beliefsB_weight (w : MFWorld) :
    beliefsB.weight w = (if w = .katie then 3 else 1) / 6 := by
  rw [beliefsB, DistributionalCG.ofWeights_weight_eq, mfWorld_sum_peak]; norm_num

/-- A's beliefs favor Nancy over all other worlds. -/
theorem beliefsA_favors_nancy (w : MFWorld) (hw : w ≠ .nancy) :
    beliefsA.weight w < beliefsA.weight .nancy := by
  rw [beliefsA_weight w, beliefsA_weight .nancy, if_neg hw, if_pos rfl]; norm_num

/-- B's beliefs favor Katie over all other worlds. -/
theorem beliefsB_favors_katie (w : MFWorld) (hw : w ≠ .katie) :
    beliefsB.weight w < beliefsB.weight .katie := by
  rw [beliefsB_weight w, beliefsB_weight .katie, if_neg hw, if_pos rfl]; norm_num

/-- Under difference-based sampling, A initially prioritizes Nancy
(highest positive difference from uniform CommonGround). -/
noncomputable def aDiffFromUniform : MFWorld → ℝ :=
  differenceSample beliefsA DistributionalCG.uniform

theorem a_diff_nancy_positive :
    0 < aDiffFromUniform .nancy := by
  rw [aDiffFromUniform, differenceSample, lt_max_iff]
  right
  rw [beliefsA_weight, DistributionalCG.uniform_weight, card_mfworld]
  norm_num

-- ════════════════════════════════════════════════════
-- § 8. The Figure-4 model on mathlib PMF
-- ════════════════════════════════════════════════════

open RSA

/-! Anderson's Shared CommonGround model ([anderson-2021] Figure 4) uses the
distributional CommonGround at BOTH ends of the chain:

    L0(w|u) ∝ ⟦u⟧(w) · CG(w)    -- CG enters the literal listener
    S1(u|w) ∝ L0(w|u)           -- speaker = renormalised L0 row (fn. 3:
                                --   softmax omitted, α = 1, no cost)
    L1(w|u) ∝ S1(u|w) · CG(w)   -- CG enters the pragmatic listener

At turn 1 the CommonGround is uniform, so the CG factor drops out of L0 and
the meaning reduces to Boolean semantics. The chain below implements this on
mathlib `PMF`, parameterized by the CommonGround. -/

-- ════════════════════════════════════════════════════
-- § 8b. PMF chain (CG-parameterized; local pending the RSA API pass)
-- ════════════════════════════════════════════════════

section PMFChain

open scoped ENNReal

/-- Every utterance is satisfiable (each has two true worlds; `null` four). -/
private theorem mfMeaning_sat : ∀ u : MFUtterance, ∃ w, mfMeaning u w = true := by
  decide

private theorem cgL0_pos (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0) (u : MFUtterance) :
    (∑' w, cg w * (if mfMeaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  obtain ⟨w, hw⟩ := mfMeaning_sat u
  exact ENNReal.summable.tsum_ne_zero_iff.mpr
    ⟨w, by rw [hw]; simpa using hcg w⟩

/-- CG-weighted literal listener ([anderson-2021] Figure 4: `L0 ∝ ⟦u⟧·CG`). -/
private noncomputable def cgL0 (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (u : MFUtterance) : PMF MFWorld :=
  RSA.L0LassiterGoodman cg mfMeaning u (cgL0_pos cg hcg u)

private theorem cgL0_null (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0) (w : MFWorld) :
    cgL0 cg hcg .null w = cg w := by
  unfold cgL0
  exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _

/-- Pragmatic speaker ([anderson-2021] Figure 4: `S1 ∝ LitList`; fn. 3: the
softmax terms are omitted and probabilities renormalized, i.e. `α = 1` and
no cost — the speaker weight IS the literal-listener value). -/
private noncomputable def cgS1 (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (w : MFWorld) : PMF MFUtterance :=
  RSA.S1Belief (cgL0 cg hcg) (fun _ => 1) 1 w
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, by
      rw [cgL0_null cg hcg w]
      exact mul_ne_zero
        ((ENNReal.rpow_pos (pos_iff_ne_zero.mpr (hcg w)) (PMF.apply_ne_top _ _)).ne')
        one_ne_zero⟩)
    (ENNReal.tsum_ne_top_of_fintype fun u =>
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
        ENNReal.one_ne_top)

private theorem cgS1_marginal_pos (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (u : MFUtterance) : PMF.marginal (cgS1 cg hcg) cg u ≠ 0 := by
  obtain ⟨w, hw⟩ := mfMeaning_sat u
  refine PMF.marginal_ne_zero _ _ _ (hcg w) ?_
  have hL0 : cgL0 cg hcg u w ≠ 0 := by
    unfold cgL0
    rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
    exact ⟨hcg w, hw⟩
  unfold cgS1
  exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 one_ne_zero

/-- Pragmatic listener ([anderson-2021] Figure 4: `L1 ∝ PragSpeak·CG`). -/
private noncomputable def cgL1 (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (u : MFUtterance) : PMF MFWorld :=
  PMF.posterior (cgS1 cg hcg) cg u (cgS1_marginal_pos cg hcg u)

/-- Endorsement speaker: `S2(u|w) ∝ L1(w|u)` (uniform utterance prior),
the standard endorsement inversion of L1 over utterances. -/
private noncomputable def cgS2 (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (w : MFWorld) : PMF MFUtterance :=
  PMF.normalize (fun u => cgL1 cg hcg u w)
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, by
      unfold cgL1
      rw [← PMF.mem_support_iff, PMF.mem_support_posterior_iff]
      refine ⟨hcg w, ?_⟩
      unfold cgS1
      exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _
        (by rw [cgL0_null cg hcg w]; exact hcg w) one_ne_zero⟩)
    (ENNReal.tsum_ne_top_of_fintype fun _ => PMF.apply_ne_top _ _)

/-- Turn-1 Common Ground: uniform ([anderson-2021] Figure 2:
`CG = Uniform(worlds)`). -/
private noncomputable def cgUniform : PMF MFWorld := PMF.uniformOfFintype MFWorld

private theorem cgUniform_pos (w : MFWorld) : cgUniform w ≠ 0 := by
  rw [cgUniform, PMF.uniformOfFintype_apply]
  simp

private theorem quarter_eq_half_div : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ / 2 := by
  rw [div_eq_mul_inv, ← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

private theorem quarter_add_quarter : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
  rw [quarter_eq_half_div, ENNReal.add_halves]

private theorem four_quarters : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 1 := by
  rw [show (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = (4⁻¹ + 4⁻¹) + (4⁻¹ + 4⁻¹) from by ring,
    quarter_add_quarter, ENNReal.inv_two_add_inv_two]

private theorem quarter_mul_two : (4 : ℝ≥0∞)⁻¹ * 2 = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

private theorem cgUniform_apply (w : MFWorld) : cgUniform w = 4⁻¹ := by
  rw [cgUniform, PMF.uniformOfFintype_apply, card_mfworld]
  norm_num

private theorem sumWorlds (f : MFWorld → ℝ≥0∞) :
    ∑' w, f w = f .ina + f .katie + f .nancy + f .sally := by
  rw [tsum_fintype,
    show (Finset.univ : Finset MFWorld) = {.ina, .katie, .nancy, .sally} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Uniform extension masses: `1` for `null`, `1/2` for each specific
utterance (true at exactly two of the four worlds). -/
private theorem uniformMass (u : MFUtterance) :
    (∑' w, cgUniform w * (if mfMeaning u w then (1 : ℝ≥0∞) else 0))
      = if u = .null then 1 else 2⁻¹ := by
  rw [sumWorlds]
  simp only [cgUniform_apply]
  cases u
  case null =>
    simp only [show ∀ w, mfMeaning .null w = true from fun _ => rfl, if_true,
      mul_one]
    exact four_quarters
  case studyHumanity =>
    rw [show mfMeaning .studyHumanity .ina = false from rfl,
      show mfMeaning .studyHumanity .katie = false from rfl,
      show mfMeaning .studyHumanity .nancy = true from rfl,
      show mfMeaning .studyHumanity .sally = true from rfl]
    simp only [reduceIte, reduceCtorEq, mul_one, mul_zero, zero_add, add_zero]
    exact quarter_add_quarter
  case studyScience =>
    rw [show mfMeaning .studyScience .ina = true from rfl,
      show mfMeaning .studyScience .katie = true from rfl,
      show mfMeaning .studyScience .nancy = false from rfl,
      show mfMeaning .studyScience .sally = false from rfl]
    simp only [reduceIte, reduceCtorEq, mul_one, mul_zero, add_zero]
    exact quarter_add_quarter
  case likeIndoors =>
    rw [show mfMeaning .likeIndoors .ina = true from rfl,
      show mfMeaning .likeIndoors .katie = false from rfl,
      show mfMeaning .likeIndoors .nancy = false from rfl,
      show mfMeaning .likeIndoors .sally = true from rfl]
    simp only [reduceIte, reduceCtorEq, mul_one, mul_zero, add_zero]
    rw [show ((4 : ℝ≥0∞)⁻¹ + 4⁻¹) = 4⁻¹ + 4⁻¹ from rfl]
    exact quarter_add_quarter
  case likeOutdoors =>
    rw [show mfMeaning .likeOutdoors .ina = false from rfl,
      show mfMeaning .likeOutdoors .katie = true from rfl,
      show mfMeaning .likeOutdoors .nancy = true from rfl,
      show mfMeaning .likeOutdoors .sally = false from rfl]
    simp only [reduceIte, reduceCtorEq, mul_one, mul_zero, zero_add, add_zero]
    exact quarter_add_quarter

/-- Literal-listener values under the uniform CG: `1/2` on a specific true
utterance (mass `1/2` doubles the `1/4` prior), `1/4` on `null`, `0` off
support. -/
private theorem cgL0_uniform_apply (u : MFUtterance) (w : MFWorld) :
    cgL0 cgUniform cgUniform_pos u w
      = if mfMeaning u w then (if u = .null then 4⁻¹ else 2⁻¹) else 0 := by
  unfold cgL0
  rw [RSA.L0LassiterGoodman_apply,
    show (∑' w', cgUniform w' * (if mfMeaning u w' then (1 : ℝ≥0∞) else 0))
      = if u = .null then 1 else 2⁻¹ from uniformMass u, cgUniform_apply]
  by_cases hw : mfMeaning u w = true
  · rw [hw]
    by_cases hn : u = .null <;>
      simp only [hn, if_true, if_false, mul_one, inv_one, inv_inv]
    exact quarter_mul_two
  · rw [Bool.not_eq_true] at hw
    rw [hw]
    simp

private theorem sumUtts (f : MFUtterance → ℝ≥0∞) :
    ∑' u, f u = f .studyHumanity + f .studyScience + f .likeIndoors +
      f .likeOutdoors + f .null := by
  rw [tsum_fintype,
    show (Finset.univ : Finset MFUtterance)
      = {.studyHumanity, .studyScience, .likeIndoors, .likeOutdoors, .null} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem half_conv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/2) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private theorem quarter_conv : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/4) := by
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from (ENNReal.ofReal_ofNat 4).symm,
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The turn-1 speaker normaliser at every world: `1/2 + 1/2 + 1/4 = 5/4`
(two true specific utterances plus `null`). -/
private theorem Z_uniform (w : MFWorld) :
    (∑' u, ((cgL0 cgUniform cgUniform_pos u w : ℝ≥0∞)) ^ (1 : ℝ) * 1)
      = ENNReal.ofReal (5/4) := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [sumUtts]
  simp only [cgL0_uniform_apply]
  cases w <;>
    · simp +decide
      rw [half_conv, quarter_conv, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

/-- Turn-1 chain. -/
noncomputable def s1Turn1 : MFWorld → PMF MFUtterance := cgS1 cgUniform cgUniform_pos

private theorem Z_uniform' (w : MFWorld) :
    (∑' u, cgL0 cgUniform cgUniform_pos u w) = ENNReal.ofReal (5/4) := by
  have h := Z_uniform w
  simpa [ENNReal.rpow_one] using h

private theorem s1_val_arith :
    (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (5/4))⁻¹ = ENNReal.ofReal (2/5) := by
  rw [half_conv, ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

private theorem s1_null_arith :
    (4 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (5/4))⁻¹ = ENNReal.ofReal (1/5) := by
  rw [quarter_conv, ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Turn-1 speaker value on a true specific utterance: `2/5` — identical at
every world (each satisfies exactly two specific utterances plus `null`).
Derived from the Figure-4 equations; [anderson-2021]'s Figure 5 reports the
qualitative multi-move profile. -/
private theorem cgS1_uniform_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) (hn : u ≠ .null) :
    cgS1 cgUniform cgUniform_pos w u = ENNReal.ofReal (2/5) := by
  unfold cgS1
  rw [RSA.S1Belief_apply]
  simp only [ENNReal.rpow_one, mul_one]
  rw [Z_uniform' w, cgL0_uniform_apply, hw]
  simp only [if_true]
  rw [if_neg hn]
  exact s1_val_arith

/-- Turn-1 speaker value on `null`: `1/5` at every world. -/
private theorem cgS1_uniform_null (w : MFWorld) :
    cgS1 cgUniform cgUniform_pos w .null = ENNReal.ofReal (1/5) := by
  unfold cgS1
  rw [RSA.S1Belief_apply]
  simp only [ENNReal.rpow_one, mul_one]
  rw [Z_uniform' w, cgL0_uniform_apply]
  simp only [show mfMeaning .null w = true from rfl, if_true]
  exact s1_null_arith

/-- Turn-1 speaker value off support: `0`. -/
private theorem cgS1_uniform_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) : cgS1 cgUniform cgUniform_pos w u = 0 := by
  unfold cgS1
  rw [RSA.S1Belief_apply]
  simp only [ENNReal.rpow_one, mul_one]
  rw [cgL0_uniform_apply, hw]
  simp

/-- Turn-1 speaker values ([anderson-2021] Figure-4 equations at the uniform
CG; derived exact rationals — Figure 5 reports the qualitative profile):
`2/5` on each true specific utterance, `1/5` on `null`, `0` off support. -/
theorem s1Turn1_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) (hn : u ≠ .null) :
    s1Turn1 w u = ENNReal.ofReal (2/5) := cgS1_uniform_true hw hn

theorem s1Turn1_null (w : MFWorld) : s1Turn1 w .null = ENNReal.ofReal (1/5) :=
  cgS1_uniform_null w

theorem s1Turn1_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) : s1Turn1 w u = 0 := cgS1_uniform_false hw

/-- The utterance marginal at turn 1 is `1/5` for every utterance: specific
utterances collect `2 · (1/4)·(2/5)`, `null` collects `4 · (1/4)·(1/5)`. -/
private theorem marginal_uniform (u : MFUtterance) :
    PMF.marginal (cgS1 cgUniform cgUniform_pos) cgUniform u = ENNReal.ofReal (1/5) := by
  show (cgUniform.bind (cgS1 cgUniform cgUniform_pos)) u = _
  rw [PMF.bind_apply, sumWorlds]
  simp only [cgUniform_apply]
  cases u
  case null =>
    rw [cgS1_uniform_null, cgS1_uniform_null, cgS1_uniform_null, cgS1_uniform_null,
      quarter_conv, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  all_goals
    first
    | (rw [cgS1_uniform_false (by decide), cgS1_uniform_false (by decide),
          cgS1_uniform_true (by decide) (by decide),
          cgS1_uniform_true (by decide) (by decide),
          quarter_conv, ← ENNReal.ofReal_mul (by norm_num)]
       simp only [mul_zero, zero_add, add_zero]
       rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       norm_num)
    | (rw [cgS1_uniform_true (by decide) (by decide),
          cgS1_uniform_true (by decide) (by decide),
          cgS1_uniform_false (by decide), cgS1_uniform_false (by decide),
          quarter_conv, ← ENNReal.ofReal_mul (by norm_num)]
       simp only [mul_zero, add_zero]
       rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       norm_num)
    | (rw [cgS1_uniform_true (by decide) (by decide),
          cgS1_uniform_false (by decide), cgS1_uniform_false (by decide),
          cgS1_uniform_true (by decide) (by decide),
          quarter_conv, ← ENNReal.ofReal_mul (by norm_num)]
       simp only [mul_zero, add_zero]
       rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       norm_num)
    | (rw [cgS1_uniform_false (by decide),
          cgS1_uniform_true (by decide) (by decide),
          cgS1_uniform_true (by decide) (by decide),
          cgS1_uniform_false (by decide),
          quarter_conv, ← ENNReal.ofReal_mul (by norm_num)]
       simp only [mul_zero, zero_add, add_zero]
       rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       norm_num)
noncomputable def l1Turn1 : MFUtterance → PMF MFWorld := cgL1 cgUniform cgUniform_pos

private theorem l1_arith_true :
    (4 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (2/5) * (ENNReal.ofReal (1/5))⁻¹
      = ENNReal.ofReal (1/2) := by
  rw [quarter_conv, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

private theorem l1_arith_null :
    (4 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (1/5) * (ENNReal.ofReal (1/5))⁻¹
      = ENNReal.ofReal (1/4) := by
  rw [quarter_conv, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Turn-1 listener values (derived; `L1 ∝ PragSpeak·CG`, Figure 4): `1/2`
on each world satisfying a specific utterance, `1/4` on every world after
`null`, `0` off support. -/
theorem l1Turn1_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) (hn : u ≠ .null) :
    l1Turn1 u w = ENNReal.ofReal (1/2) := by
  unfold l1Turn1 cgL1
  rw [PMF.posterior_apply, marginal_uniform, cgUniform_apply, cgS1_uniform_true hw hn]
  exact l1_arith_true

theorem l1Turn1_null (w : MFWorld) : l1Turn1 .null w = ENNReal.ofReal (1/4) := by
  unfold l1Turn1 cgL1
  rw [PMF.posterior_apply, marginal_uniform, cgUniform_apply, cgS1_uniform_null]
  exact l1_arith_null

theorem l1Turn1_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) : l1Turn1 u w = 0 := by
  unfold l1Turn1 cgL1
  rw [PMF.posterior_apply, cgS1_uniform_false hw, mul_zero, zero_mul]
noncomputable def s2Turn1 : MFWorld → PMF MFUtterance := cgS2 cgUniform cgUniform_pos

end PMFChain

-- ════════════════════════════════════════════════════
-- § 9. Turn 1: S1 Predictions
-- ════════════════════════════════════════════════════

/-- A speaker who knows the person is Nancy prefers "studyHumanity" over
"studyScience". Nancy studies German (a humanity), so "studyScience" has
L0(nancy|studyScience) = 0, while "studyHumanity" has L0(nancy|studyHumanity) = 1/2. -/
theorem s1_nancy_prefers_humanity :
    s1Turn1 .nancy .studyHumanity > s1Turn1 .nancy .studyScience := by
  rw [s1Turn1_true (by decide) (by decide), s1Turn1_false (by decide)]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- A speaker who knows it's Nancy prefers "likeOutdoors" over "likeIndoors".
Nancy likes being outdoors. -/
theorem s1_nancy_prefers_outdoors :
    s1Turn1 .nancy .likeOutdoors > s1Turn1 .nancy .likeIndoors := by
  rw [s1Turn1_true (by decide) (by decide), s1Turn1_false (by decide)]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- A speaker who knows it's Ina prefers "studyScience" over "studyHumanity".
Ina studies Astronomy (a science). -/
theorem s1_ina_prefers_science :
    s1Turn1 .ina .studyScience > s1Turn1 .ina .studyHumanity := by
  rw [s1Turn1_true (by decide) (by decide), s1Turn1_false (by decide)]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- A speaker who knows it's Ina is indifferent between "studyScience" and
"likeIndoors": both are true of exactly 2 worlds, giving equal L0 posteriors.
-/
theorem s1_ina_science_eq_indoors :
    s1Turn1 .ina .studyScience = s1Turn1 .ina .likeIndoors := by
  rw [s1Turn1_true (by decide) (by decide), s1Turn1_true (by decide) (by decide)]

/-- The null utterance is always suboptimal: a speaker who knows it's Nancy
strictly prefers any true specific utterance over saying nothing.
Null is true of all 4 worlds (L0 = 1/4), while "studyHumanity" is true of
only 2 (L0 = 1/2). -/
theorem s1_null_suboptimal :
    s1Turn1 .nancy .studyHumanity > s1Turn1 .nancy .null := by
  rw [s1Turn1_true (by decide) (by decide), s1Turn1_null]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Symmetry: S1(studyHumanity|nancy) = S1(likeOutdoors|nancy).
Both utterances partition the 4 worlds into 2 true + 2 false, so
L0(nancy|studyHumanity) = L0(nancy|likeOutdoors) = 1/2, hence equal S1. -/
theorem s1_nancy_humanity_eq_outdoors :
    s1Turn1 .nancy .studyHumanity = s1Turn1 .nancy .likeOutdoors := by
  rw [s1Turn1_true (by decide) (by decide), s1Turn1_true (by decide) (by decide)]

/-- False utterances get zero S1 probability.
"studyScience" is false of Nancy (she studies German), so S1 = 0.
-/
theorem s1_nancy_science_not_gt_null :
    ¬(s1Turn1 .nancy .studyScience > s1Turn1 .nancy .null) := by
  rw [gt_iff_lt,
    s1Turn1_false (show mfMeaning .studyScience .nancy = false from by decide)]
  simp

-- ════════════════════════════════════════════════════
-- § 10. Turn 1: L1 Predictions
-- ════════════════════════════════════════════════════

/-- After hearing "studyHumanity", L1 assigns higher probability to Nancy
than to Ina. Nancy studies a humanity; Ina studies a science. -/
theorem l1_humanity_favors_nancy :
    l1Turn1 .studyHumanity .nancy > l1Turn1 .studyHumanity .ina := by
  rw [l1Turn1_true (by decide) (by decide), l1Turn1_false (by decide)]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- After hearing "likeOutdoors", L1 favors Nancy over Sally.
Nancy likes outdoors; Sally likes indoors. -/
theorem l1_outdoors_favors_nancy :
    l1Turn1 .likeOutdoors .nancy > l1Turn1 .likeOutdoors .sally := by
  rw [l1Turn1_true (by decide) (by decide), l1Turn1_false (by decide)]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- After hearing "studyHumanity", L1 assigns equal probability to Nancy
and Sally — both study a humanity, and S1 scores are symmetric. -/
theorem l1_humanity_nancy_eq_sally :
    l1Turn1 .studyHumanity .nancy = l1Turn1 .studyHumanity .sally := by
  rw [l1Turn1_true (by decide) (by decide), l1Turn1_true (by decide) (by decide)]

/-- After hearing "studyScience", L1 assigns equal probability to Ina
and Katie — both study a science. -/
theorem l1_science_ina_eq_katie :
    l1Turn1 .studyScience .ina = l1Turn1 .studyScience .katie := by
  rw [l1Turn1_true (by decide) (by decide), l1Turn1_true (by decide) (by decide)]

/-- The null utterance conveys no information: L1 assigns equal probability
to all worlds. Every world has S1(null|w) = 1/5 by the domain's symmetry
(each world makes exactly 2 non-null utterances true). -/
theorem l1_null_uniform (w₁ w₂ : MFWorld) :
    l1Turn1 .null w₁ = l1Turn1 .null w₂ := by
  rw [l1Turn1_null, l1Turn1_null]

-- ════════════════════════════════════════════════════
-- § 11. Turn 2 (Post-Update Prior)
-- ════════════════════════════════════════════════════

/-- CommonGround weights after hearing "studyHumanity" at turn 1.

After L1 processes "studyHumanity" with uniform prior, the posterior
concentrates on nancy and sally (the German-studying worlds):
L1(studyHumanity) = [0, 0, 1/2, 1/2]. Updating the normalized uniform
CommonGround [1/4, 1/4, 1/4, 1/4] via `updateCG` with lr=0.2 (footnote 9) gives:

    CommonGround'(w) = 0.8 · 1/4 + 0.2 · L1(w)
    CommonGround' = [1/5, 1/5, 3/10, 3/10]

The weights [2, 2, 3, 3] are proportional to [1/5, 1/5, 3/10, 3/10],
which is the exact post-update CommonGround from the paper's Figure 5, panel 1A.
Since RSA normalizes, proportional weights give identical predictions. -/
def cgTurn2 : MFWorld → ℝ
  | .ina | .katie => 2
  | .nancy | .sally => 3


section PMFChain

open scoped ENNReal

/-- Turn-2 Common Ground as a PMF: the normalised `[2,2,3,3]` weights
(= `0.8·uniform + 0.2·L1(studyHumanity)`, [anderson-2021] fn. 9's lr = 0.2). -/
private noncomputable def cgTurn2PMF : PMF MFWorld :=
  PMF.normalize (fun w => ENNReal.ofReal (cgTurn2 w))
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.ina, by
      rw [ENNReal.ofReal_ne_zero_iff]
      norm_num [cgTurn2]⟩)
    (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)

private theorem cgTurn2PMF_pos (w : MFWorld) : cgTurn2PMF w ≠ 0 := by
  rw [cgTurn2PMF, PMF.normalize_apply]
  refine mul_ne_zero ?_ (ENNReal.inv_ne_zero.mpr
    (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top))
  rw [ENNReal.ofReal_ne_zero_iff]
  cases w <;> norm_num [cgTurn2]

/-- Turn-2 chain. -/
noncomputable def s1Turn2 : MFWorld → PMF MFUtterance := cgS1 cgTurn2PMF cgTurn2PMF_pos
noncomputable def l1Turn2 : MFUtterance → PMF MFWorld := cgL1 cgTurn2PMF cgTurn2PMF_pos

private theorem t2_sum : (∑' w, ENNReal.ofReal (cgTurn2 w)) = ENNReal.ofReal 10 := by
  rw [sumWorlds]
  norm_num [cgTurn2]

private theorem cgTurn2PMF_apply (w : MFWorld) :
    cgTurn2PMF w = ENNReal.ofReal (cgTurn2 w / 10) := by
  rw [cgTurn2PMF, PMF.normalize_apply, t2_sum,
    ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_mul (by cases w <;> norm_num [cgTurn2])]
  rw [div_eq_mul_inv]

/-- Turn-2 masses: `3/5` for humanity, `2/5` for science, `1/2` for each
location, `1` for `null` (weights `[2,2,3,3]/10`). -/
private noncomputable def t2MassQ : MFUtterance → ℝ
  | .studyHumanity => 3/5
  | .studyScience  => 2/5
  | .likeIndoors   => 1/2
  | .likeOutdoors  => 1/2
  | .null          => 1

private theorem t2Mass (u : MFUtterance) :
    (∑' w, cgTurn2PMF w * (if mfMeaning u w then (1 : ℝ≥0∞) else 0))
      = ENNReal.ofReal (t2MassQ u) := by
  rw [sumWorlds]
  simp only [cgTurn2PMF_apply]
  cases u <;>
    · simp +decide [cgTurn2, t2MassQ]
      try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      first
        | (rw [half_conv]; congr 1; norm_num)
        | norm_num

private theorem cgL0_t2_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) :
    cgL0 cgTurn2PMF cgTurn2PMF_pos u w
      = ENNReal.ofReal (cgTurn2 w / 10 / t2MassQ u) := by
  unfold cgL0
  rw [RSA.L0LassiterGoodman_apply, hw, t2Mass, cgTurn2PMF_apply]
  simp only [if_true, mul_one]
  rw [← ENNReal.ofReal_inv_of_pos (by cases u <;> norm_num [t2MassQ]),
    ← ENNReal.ofReal_mul (by cases w <;> norm_num [cgTurn2])]
  congr 1

private theorem cgL0_t2_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) :
    cgL0 cgTurn2PMF cgTurn2PMF_pos u w = 0 := by
  unfold cgL0
  rw [RSA.L0LassiterGoodman_apply, hw]
  simp

/-- Turn-2 speaker normalisers: `7/5` at the high-CG worlds (nancy, sally),
`11/10` at the low-CG worlds (ina, katie). -/
private noncomputable def Zt2Q : MFWorld → ℝ
  | .ina | .katie => 11/10
  | .nancy | .sally => 7/5

private theorem Z_t2 (w : MFWorld) :
    (∑' u, cgL0 cgTurn2PMF cgTurn2PMF_pos u w) = ENNReal.ofReal (Zt2Q w) := by
  rw [sumUtts]
  cases w <;>
    · first
      | rw [cgL0_t2_false (by decide), cgL0_t2_true (by decide),
          cgL0_t2_true (by decide), cgL0_t2_false (by decide),
          cgL0_t2_true (by decide)]
      | rw [cgL0_t2_false (by decide), cgL0_t2_true (by decide),
          cgL0_t2_false (by decide), cgL0_t2_true (by decide),
          cgL0_t2_true (by decide)]
      | rw [cgL0_t2_true (by decide), cgL0_t2_false (by decide),
          cgL0_t2_false (by decide), cgL0_t2_true (by decide),
          cgL0_t2_true (by decide)]
      | rw [cgL0_t2_true (by decide), cgL0_t2_false (by decide),
          cgL0_t2_true (by decide), cgL0_t2_false (by decide),
          cgL0_t2_true (by decide)]
      simp only [cgTurn2, t2MassQ, Zt2Q, zero_add, add_zero]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

/-- Generic turn-2 speaker value on support. -/
private theorem cgS1_t2_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) :
    cgS1 cgTurn2PMF cgTurn2PMF_pos w u
      = ENNReal.ofReal (cgTurn2 w / 10 / t2MassQ u / Zt2Q w) := by
  unfold cgS1
  rw [RSA.S1Belief_apply]
  simp only [ENNReal.rpow_one, mul_one]
  rw [show (∑' u', cgL0 cgTurn2PMF cgTurn2PMF_pos u' w) = ENNReal.ofReal (Zt2Q w)
      from Z_t2 w,
    cgL0_t2_true hw,
    ← ENNReal.ofReal_inv_of_pos (by cases w <;> norm_num [Zt2Q]),
    ← ENNReal.ofReal_mul (by cases u <;> cases w <;> norm_num [cgTurn2, t2MassQ])]
  congr 1

private theorem cgS1_t2_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) :
    cgS1 cgTurn2PMF cgTurn2PMF_pos w u = 0 := by
  unfold cgS1
  rw [RSA.S1Belief_apply]
  simp only [ENNReal.rpow_one, mul_one]
  rw [cgL0_t2_false hw]
  simp

end PMFChain


-- ════════════════════════════════════════════════════
-- § 12. Turn 2 Predictions
-- ════════════════════════════════════════════════════

/-- After CommonGround update from "studyHumanity", L1("likeOutdoors") now favors
Nancy over Katie. In turn 1, they were symmetric (both like outdoors).
The updated prior (3 vs 1) breaks the tie — Nancy's higher CommonGround weight
makes her more probable. This is the key multi-turn prediction. -/
theorem l1_turn2_outdoors_favors_nancy :
    l1Turn2 .likeOutdoors .nancy > l1Turn2 .likeOutdoors .katie := by
  unfold l1Turn2 cgL1
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt, cgTurn2PMF_apply, cgTurn2PMF_apply,
    cgS1_t2_true (by decide), cgS1_t2_true (by decide),
    ← ENNReal.ofReal_mul (by norm_num [cgTurn2]),
    ← ENNReal.ofReal_mul (by norm_num [cgTurn2])]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [cgTurn2, t2MassQ, Zt2Q])).mpr
    (by norm_num [cgTurn2, t2MassQ, Zt2Q])

/-- After CommonGround update, "likeIndoors" favors Sally over Ina. Both like
indoors, but Sally has higher prior (3 vs 1) from the CommonGround shift. -/
theorem l1_turn2_indoors_favors_sally :
    l1Turn2 .likeIndoors .sally > l1Turn2 .likeIndoors .ina := by
  unfold l1Turn2 cgL1
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt, cgTurn2PMF_apply, cgTurn2PMF_apply,
    cgS1_t2_true (by decide), cgS1_t2_true (by decide),
    ← ENNReal.ofReal_mul (by norm_num [cgTurn2]),
    ← ENNReal.ofReal_mul (by norm_num [cgTurn2])]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [cgTurn2, t2MassQ, Zt2Q])).mpr
    (by norm_num [cgTurn2, t2MassQ, Zt2Q])

/-- After CommonGround update, "studyScience" still treats Ina and Katie equally:
both study a science and both have equal prior weight (1). -/
theorem l1_turn2_science_ina_eq_katie :
    l1Turn2 .studyScience .ina = l1Turn2 .studyScience .katie := by
  unfold l1Turn2 cgL1
  have h : cgTurn2PMF .ina * cgS1 cgTurn2PMF cgTurn2PMF_pos .ina .studyScience
      = cgTurn2PMF .katie * cgS1 cgTurn2PMF cgTurn2PMF_pos .katie .studyScience := by
    rw [cgTurn2PMF_apply, cgTurn2PMF_apply, cgS1_t2_true (by decide),
      cgS1_t2_true (by decide)]
    norm_num [cgTurn2, Zt2Q]
  exact le_antisymm ((PMF.posterior_le_iff_score_le _ _ _ _ _ _).mpr h.le)
    ((PMF.posterior_le_iff_score_le _ _ _ _ _ _).mpr h.ge)

/-- After CommonGround update, "studyHumanity" still treats Nancy and Sally equally:
both study a humanity and both have equal updated prior (3). -/
theorem l1_turn2_humanity_nancy_eq_sally :
    l1Turn2 .studyHumanity .nancy = l1Turn2 .studyHumanity .sally := by
  unfold l1Turn2 cgL1
  have h : cgTurn2PMF .nancy * cgS1 cgTurn2PMF cgTurn2PMF_pos .nancy .studyHumanity
      = cgTurn2PMF .sally * cgS1 cgTurn2PMF cgTurn2PMF_pos .sally .studyHumanity := by
    rw [cgTurn2PMF_apply, cgTurn2PMF_apply, cgS1_t2_true (by decide),
      cgS1_t2_true (by decide)]
    norm_num [cgTurn2, Zt2Q]
  exact le_antisymm ((PMF.posterior_le_iff_score_le _ _ _ _ _ _).mpr h.le)
    ((PMF.posterior_le_iff_score_le _ _ _ _ _ _).mpr h.ge)

/-- CommonGround update breaks turn-1 symmetry: in turn 1, L1("likeOutdoors")
assigned equal weight to Nancy and Katie. After the CommonGround shift, Nancy
is favored. Multi-turn conversation enriches inference. -/
theorem turn2_breaks_symmetry :
    l1Turn1 .likeOutdoors .nancy = l1Turn1 .likeOutdoors .katie ∧
    l1Turn2 .likeOutdoors .nancy > l1Turn2 .likeOutdoors .katie :=
  ⟨by rw [l1Turn1_true (by decide) (by decide), l1Turn1_true (by decide) (by decide)],
   l1_turn2_outdoors_favors_nancy⟩

-- ════════════════════════════════════════════════════
-- § 12b. Turn 2: S1 CommonGround-Adapted Speaker
-- ════════════════════════════════════════════════════

/-! With CommonGround entering L0 (Figure 4), the speaker at turn 2 adapts to what's
already in the common ground. After "studyHumanity" establishes the major
dimension, utterances that disambiguate within the high-CommonGround subspace become
more informative. This section verifies that the CommonGround-weighted S1 captures
Anderson's cooperative contribution mechanism. -/

/-- **CommonGround-adapted informativity**: At turn 2, the speaker who knows it's Nancy
prefers "likeOutdoors" over "studyHumanity". At turn 1, these were equal
(both partition the 4-world space into 2+2). After the CommonGround shifts toward
nancy/sally (weights [2,2,3,3]), "likeOutdoors" discriminates within
the high-weight subspace (L0(nancy|likeOutdoors) = 3/5) while
"studyHumanity" merely re-asserts what's already established
(L0(nancy|studyHumanity) = 1/2).

This is Anderson's key insight: the CommonGround-weighted L0 makes speakers prefer
*new* information over *redundant* information. -/
theorem s1_turn2_nancy_prefers_outdoors :
    s1Turn2 .nancy .likeOutdoors > s1Turn2 .nancy .studyHumanity := by
  show cgS1 _ _ _ _ > cgS1 _ _ _ _
  rw [cgS1_t2_true (by decide), cgS1_t2_true (by decide)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [cgTurn2, t2MassQ, Zt2Q])).mpr
    (by norm_num [cgTurn2, t2MassQ, Zt2Q])

/-- At turn 1, the same two utterances were equal (pre-CommonGround-adaptation). -/
theorem s1_turn1_nancy_humanity_eq_outdoors :
    s1Turn1 .nancy .studyHumanity = s1Turn1 .nancy .likeOutdoors :=
  s1_nancy_humanity_eq_outdoors

/-- CommonGround adaptation works differently for low-CommonGround worlds: at turn 2,
Ina (weight 2) prefers "studyScience" over "likeIndoors" because
sally (weight 3) dominates the indoor partition, making
L0(ina|likeIndoors) = 2/5 < L0(ina|studyScience) = 1/2. The CommonGround shift
makes the major dimension MORE informative for low-CommonGround worlds, the opposite
of the high-CommonGround case (nancy, §12b above). -/
theorem s1_turn2_ina_prefers_science :
    s1Turn2 .ina .studyScience > s1Turn2 .ina .likeIndoors := by
  show cgS1 _ _ _ _ > cgS1 _ _ _ _
  rw [cgS1_t2_true (by decide), cgS1_t2_true (by decide)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [cgTurn2, t2MassQ, Zt2Q])).mpr
    (by norm_num [cgTurn2, t2MassQ, Zt2Q])

-- ════════════════════════════════════════════════════
-- § 13. S2: Endorsement Predictions
-- ════════════════════════════════════════════════════

/-- S2 endorsement: given world Nancy, the pragmatic speaker endorses
"studyHumanity" over "studyScience". S2(u|w) ∝ L1(w|u), and
L1(nancy|studyHumanity) > 0 = L1(nancy|studyScience). -/
theorem s2_nancy_endorses_humanity :
    s2Turn1 .nancy .studyHumanity > s2Turn1 .nancy .studyScience := by
  unfold s2Turn1 cgS2
  rw [gt_iff_lt, PMF.normalize_lt_iff_lt]
  show l1Turn1 .studyScience .nancy < l1Turn1 .studyHumanity .nancy
  rw [l1Turn1_false (by decide), l1Turn1_true (by decide) (by decide)]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- S2 endorsement: given world Nancy, "studyHumanity" and "likeOutdoors"
are equally endorsed (symmetric L1 posteriors). -/
theorem s2_nancy_humanity_eq_outdoors :
    s2Turn1 .nancy .studyHumanity = s2Turn1 .nancy .likeOutdoors := by
  unfold s2Turn1 cgS2
  rw [PMF.normalize_eq_iff_eq]
  show l1Turn1 .studyHumanity .nancy = l1Turn1 .likeOutdoors .nancy
  rw [l1Turn1_true (by decide) (by decide), l1Turn1_true (by decide) (by decide)]

-- ════════════════════════════════════════════════════
-- § 14. Parametric RSA and Conversation Step
-- ════════════════════════════════════════════════════

section PMFChain

open scoped ENNReal

/-- Total literal listener at an arbitrary CommonGround (dite fallback for
utterances whose extension has zero CG mass). -/
noncomputable def cgL0Total (cg : PMF MFWorld) (u : MFUtterance) : PMF MFWorld :=
  if h : (∑' w, cg w * (if mfMeaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0 then
    RSA.L0LassiterGoodman cg mfMeaning u h
  else PMF.uniformOfFintype MFWorld

/-- Total speaker at an arbitrary CommonGround — the general Figure-4
production model used by the conversation loop (fallback to `null` at
zero-support worlds). -/
noncomputable def cgS1Total (cg : PMF MFWorld) (w : MFWorld) : PMF MFUtterance :=
  if h : (∑' u, ((cgL0Total cg u) w : ℝ≥0∞) ^ (1 : ℝ) * 1) ≠ 0 then
    RSA.S1Belief (cgL0Total cg) (fun _ => 1) 1 w h
      (ENNReal.tsum_ne_top_of_fintype fun _ =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          ENNReal.one_ne_top)
  else PMF.pure .null

end PMFChain

/-- One step of the Shared CommonGround conversation loop (Figure 2).

Given the current CommonGround and an utterance:
1. Build the speaker chain at the current CommonGround (`cgS1Total`)
2. Compute L1 posteriors: the pragmatic listener's world beliefs
3. Update the CommonGround via convex combination with the posteriors

This closes the loop: RSA inference → CommonGround update → new RSA model.
The returned CommonGround serves as the world prior for the next turn's model.

**Renormalisation** is now intrinsic: `PMF.posterior` IS the renormalised
listener ([anderson-2021] fn. 3: *"the probabilities are renormalized"*), so
`updateCG` is a genuine convex combination of distributions by construction.
The guard handles the degenerate case of an utterance contradicting the
entire common ground (marginal 0, e.g. `studyHumanity` against a CG
concentrated on Ina): the posterior carries no information and the
CommonGround is left unchanged — matching Anderson's null-utterance "skip
the update" behaviour (§7.1). -/
noncomputable def conversationStep
    (cg : DistributionalCG MFWorld) (u : MFUtterance)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    DistributionalCG MFWorld :=
  if h : PMF.marginal (cgS1Total cg.dist) cg.dist u ≠ 0 then
    updateCG cg ⟨PMF.posterior (cgS1Total cg.dist) cg.dist u h⟩ lr hlr hlr1
  else cg

/-- The conversation step preserves CommonGround non-negativity (now free:
the result is a genuine distribution). -/
theorem conversationStep_nonneg (cg : DistributionalCG MFWorld)
    (u : MFUtterance) (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) (w : MFWorld) :
    0 ≤ (conversationStep cg u lr hlr hlr1).weight w :=
  (conversationStep cg u lr hlr hlr1).weight_nonneg w

/-- With lr = 0, the conversation step leaves the CommonGround unchanged. -/
theorem conversationStep_lr_zero (cg : DistributionalCG MFWorld) (u : MFUtterance) (w : MFWorld) :
    (conversationStep cg u 0 (le_refl 0) zero_le_one).weight w = cg.weight w := by
  unfold conversationStep
  split
  · exact updateCG_lr_zero cg _ w
  · rfl

-- ════════════════════════════════════════════════════
-- § 15. Qualitative information-sharing properties
-- ════════════════════════════════════════════════════

/-! The RSA predictions above verify the qualitative properties of
successful information sharing:

1. **Contributions informative**: S1 prefers specific utterances over null
   (§9, `s1_null_suboptimal`).

2. **Uncertainty decreases**: L1 concentrates probability after hearing
   an informative utterance (this section).

3. **CommonGround-adapted contributions**: At turn 2, S1 adapts to what's already
   in the CommonGround, preferring non-redundant information (§12b). -/

/-- L1 concentrates probability after an informative utterance:
L1(nancy|studyHumanity) > L1(nancy|null). The null utterance gives
uniform L1 (= 1/4), while "studyHumanity" concentrates on the 2
German-studying worlds (= 1/2). -/
theorem l1_concentrates_after_utterance :
    l1Turn1 .studyHumanity .nancy > l1Turn1 .null .nancy := by
  rw [l1Turn1_true (by decide) (by decide), l1Turn1_null]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Informed speakers are informative: S1 assigns higher probability
to a true specific utterance than to null. -/
theorem s1_informed_speaker_is_informative :
    s1Turn1 .nancy .studyHumanity > s1Turn1 .nancy .null :=
  s1_null_suboptimal

-- ════════════════════════════════════════════════════
-- § 16. Bridge to Classical CommonGround Update
-- ════════════════════════════════════════════════════

/-- Anderson's distributional CommonGround update subsumes [stalnaker-2002]'s
set-intersection update **only in the degenerate `lr = 1` limit**: when the
whole prior CommonGround is discarded (`lr = 1`) and the posterior assigns
zero mass to a world, that world drops out of the context set — recovering
classical elimination.

This is the *one* direction of the Stalnaker bridge that survives. The
graded model diverges for every `lr < 1`; see
`graded_update_keeps_false_world`. -/
theorem lr_one_excludes_false_worlds (cg post : DistributionalCG MFWorld)
    (w : MFWorld) (h : post.weight w = 0) :
    ¬(updateCG cg post 1 zero_le_one (le_refl 1)).toContextSet w := by
  apply DistributionalCG.zero_weight_excluded
  rw [updateCG_lr_one]; exact h

/-- **The divergence the graded model insists on** (Anderson 2021, footnote
7: *"worlds can regain probability"*). For any `lr < 1`, a world the
utterance rules out (`post.weight w = 0`) is **not** excluded from the
context set — the prior CommonGround keeps it alive with mass
`(1 - lr) · cg.weight w`. This is exactly where Anderson's distributional
update parts ways with Stalnaker's monotone set-intersection: graded
interpolation never deletes a world unless it is *already* dead in the prior.
Linglib surfaces the incompatibility rather than papering over it. -/
theorem graded_update_keeps_false_world (cg post : DistributionalCG MFWorld)
    (w : MFWorld) (hcg : 0 < cg.weight w) (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr < 1) :
    (updateCG cg post lr h0 h1.le).toContextSet w := by
  rw [DistributionalCG.toContextSet_apply, updateCG_eq]
  have : 0 < (1 - lr) * cg.weight w := mul_pos (by linarith) hcg
  have : 0 ≤ lr * post.weight w :=
    mul_nonneg h0 (DistributionalCG.weight_nonneg _ _)
  linarith

-- ════════════════════════════════════════════════════
-- § 17. Exact Numerical Predictions (turn 1)
-- ════════════════════════════════════════════════════

/-! Exact rational values for the turn-1 RSA computations, derived from
the Figure-4 equations at the uniform CommonGround. (The paper's Figure 5
is a qualitative bar chart of a four-move conversation; these exact
fractions are the formalization's own kernel-checked arithmetic, not
printed paper values.) The domain's 2×2 feature symmetry gives clean
fractions: each non-null utterance is true of exactly 2 worlds
(L0 = 1/2), null is true of all 4 (L0 = 1/4), and each world makes
exactly 2 non-null utterances true, giving
S1(true u|w) = (1/2)/(5/4) = 2/5 and S1(null|w) = (1/4)/(5/4) = 1/5. -/

-- S1(·|nancy): production probabilities given obs = Nancy

theorem s1_nancy_studyHumanity_val :
    s1Turn1 .nancy .studyHumanity = ENNReal.ofReal (2/5) :=
  s1Turn1_true (by decide) (by decide)

theorem s1_nancy_studyScience_val :
    s1Turn1 .nancy .studyScience = 0 :=
  s1Turn1_false (by decide)

theorem s1_nancy_likeIndoors_val :
    s1Turn1 .nancy .likeIndoors = 0 :=
  s1Turn1_false (by decide)

theorem s1_nancy_likeOutdoors_val :
    s1Turn1 .nancy .likeOutdoors = ENNReal.ofReal (2/5) :=
  s1Turn1_true (by decide) (by decide)

theorem s1_nancy_null_val :
    s1Turn1 .nancy .null = ENNReal.ofReal (1/5) :=
  s1Turn1_null .nancy

-- L1(·|studyHumanity): posteriors used in CommonGround update → Figure 5 panel 1A

theorem l1_studyHumanity_nancy_val :
    l1Turn1 .studyHumanity .nancy = ENNReal.ofReal (1/2) :=
  l1Turn1_true (by decide) (by decide)

theorem l1_studyHumanity_sally_val :
    l1Turn1 .studyHumanity .sally = ENNReal.ofReal (1/2) :=
  l1Turn1_true (by decide) (by decide)

theorem l1_studyHumanity_ina_val :
    l1Turn1 .studyHumanity .ina = 0 :=
  l1Turn1_false (by decide)

theorem l1_studyHumanity_katie_val :
    l1Turn1 .studyHumanity .katie = 0 :=
  l1Turn1_false (by decide)

/-- Null gives uniform L1: every world has the same S1(null|w) by the
domain's symmetry, so L1(w|null) = CommonGround(w)/Σ CommonGround = 1/4. -/
theorem l1_null_val (w : MFWorld) :
    l1Turn1 .null w = ENNReal.ofReal (1/4) :=
  l1Turn1_null w

-- ════════════════════════════════════════════════════
-- § 18. Approximate CommonGround Model (§5.2, Figure 6)
-- ════════════════════════════════════════════════════

/-! The Approximate Common Ground model relaxes the shared-CommonGround assumption:
each participant maintains their own CommonGround approximation. The speaker uses
CG_S in production; the listener uses CG_L in comprehension with their
private beliefs B_L as the L1 world prior.

Key difference from shared CommonGround (Figure 4):
- Shared:  L1(w|u) ∝ S1(u|w) · CommonGround(w)     — same CommonGround for everyone
- Approx:  L1(w|u) ∝ S1(u|w) · B_L(w)    — listener's own beliefs

This models realistic divergence: participants with different priors
hear the same utterance but reach different posteriors, causing their
CommonGround approximations to drift apart (Figure 7). -/

/-- State for the Approximate CommonGround model (§5.2, Figure 6). -/
structure ApproxCGState (W : Type*) where
  cgA : DistributionalCG W
  cgB : DistributionalCG W
  belA : DistributionalCG W
  belB : DistributionalCG W
  lr : ℝ
  speakerIsA : Bool

noncomputable def ApproxCGState.initial {W : Type*} [Fintype W] [Nonempty W]
    (belA belB : DistributionalCG W) (lr : ℝ) : ApproxCGState W where
  cgA := DistributionalCG.uniform
  cgB := DistributionalCG.uniform
  belA := belA
  belB := belB
  lr := lr
  speakerIsA := true

private theorem cgS1_marginal_pos' (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (bel : PMF MFWorld) (hbel : ∀ w, bel w ≠ 0) (u : MFUtterance) :
    PMF.marginal (cgS1 cg hcg) bel u ≠ 0 := by
  obtain ⟨w, hw⟩ := mfMeaning_sat u
  refine PMF.marginal_ne_zero _ _ _ (hbel w) ?_
  have hL0 : cgL0 cg hcg u w ≠ 0 := by
    unfold cgL0
    rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
    exact ⟨hcg w, hw⟩
  unfold cgS1
  exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 one_ne_zero

/-- Approximate comprehension listener ([anderson-2021] Figure 6): L0/S1 run
over the listener's CommonGround approximation `CG_L`, but the Bayesian
inversion uses the listener's private beliefs `B_L` as the prior. Stated for
everywhere-positive `CG_L`/`B_L` (the degenerate-support cases go through
the total conversation-loop constructions above). -/
noncomputable def approxL1 (cgL : PMF MFWorld) (hcgL : ∀ w, cgL w ≠ 0)
    (belL : PMF MFWorld) (hbelL : ∀ w, belL w ≠ 0) (u : MFUtterance) : PMF MFWorld :=
  PMF.posterior (cgS1 cgL hcgL) belL u (cgS1_marginal_pos' cgL hcgL belL hbelL u)

/-- When beliefs equal the CommonGround, the approximate model reduces to the
shared CommonGround model — the split is only meaningful when they diverge. -/
theorem approx_reduces_to_shared (cg : PMF MFWorld) (hcg : ∀ w, cg w ≠ 0)
    (u : MFUtterance) : approxL1 cg hcg cg hcg u = cgL1 cg hcg u := rfl

-- ════════════════════════════════════════════════════
-- § 19. Belief Update Model (§6, Figure 8)
-- ════════════════════════════════════════════════════

/-! The belief update model extends the conversation system by also
updating participants' private beliefs. After comprehension, the
listener updates their beliefs via the same linear rule as CommonGround update:

    Bel'(w) = (1 - lr_bel) · Bel(w) + lr_bel · posterior(w)

The speaker does not update beliefs (they already knew the info).
Different learning rates for CommonGround vs beliefs allow modeling:
- §6.2: skeptical listeners (low belief lr, high CommonGround lr)
- §6.3: uncertainty-based rates (lr scales with entropy) -/

/-- State for the belief update model (Figure 8).
Extends approximate CommonGround with separate learning rates for CommonGround and beliefs. -/
structure BeliefUpdateState (W : Type*) where
  cgA : DistributionalCG W
  cgB : DistributionalCG W
  belA : DistributionalCG W
  belB : DistributionalCG W
  /-- Learning rate for CommonGround updates. -/
  cgLR : ℝ
  /-- Learning rate for belief updates (may be lower for skeptical agents). -/
  belLR : ℝ
  speakerIsA : Bool

noncomputable def BeliefUpdateState.initial {W : Type*} [Fintype W] [Nonempty W]
    (belA belB : DistributionalCG W) (cgLR belLR : ℝ) :
    BeliefUpdateState W where
  cgA := DistributionalCG.uniform
  cgB := DistributionalCG.uniform
  belA := belA
  belB := belB
  cgLR := cgLR
  belLR := belLR
  speakerIsA := true

/-- Belief update is algebraically identical to CommonGround update — both are
instances of [luce-1959]'s linear learning rule. The only difference
is the learning rate parameter and the interpretation (private vs shared). -/
theorem belief_update_is_linear_learning {W : Type*} [Fintype W]
    (bel post : DistributionalCG W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG bel post lr h0 h1).weight w =
    (1 - lr) * bel.weight w + lr * post.weight w :=
  updateCG_eq bel post lr h0 h1 w

-- ════════════════════════════════════════════════════
-- § 20. Noncommittal Speaker Problem (§7.1)
-- ════════════════════════════════════════════════════

/-! A speaker with uniform beliefs (no private information) assigns equal
weight to all worlds under weighted sampling. Since no observation is
more probable than any other, the speaker makes random assertions about
worlds they don't know, causing the CommonGround to flip-flop (Figure 12).

Solutions:
1. **Threshold sampling** (§7.1.1): filter out low-confidence worlds;
   a noncommittal speaker passes (null utterance) instead of guessing.
2. **Uncertainty-based lr** (§6.3): scale the CommonGround update rate by the
   listener's uncertainty, so confident listeners resist random input. -/

/-- Uniform beliefs assign equal weight to all worlds under weighted
sampling — a noncommittal speaker has no basis for choosing. -/
theorem uniform_weighted_constant (w₁ w₂ : MFWorld) :
    weightedSample (DistributionalCG.uniform : DistributionalCG MFWorld) w₁ =
    weightedSample (DistributionalCG.uniform : DistributionalCG MFWorld) w₂ := by
  simp only [weightedSample, DistributionalCG.uniform_weight]

/-- Threshold sampling filters out all worlds when beliefs don't exceed
the threshold. Every mass of a distribution is `≤ 1`, so any `θ > 1`
produces zero weight everywhere — the speaker passes (Figure 13). -/
theorem threshold_filters_uniform (θ : ℝ) (hθ : 1 < θ) (w : MFWorld) :
    thresholdedSample (DistributionalCG.uniform : DistributionalCG MFWorld) θ w = 0 := by
  have hle : (DistributionalCG.uniform : DistributionalCG MFWorld).weight w ≤ 1 :=
    DistributionalCG.weight_le_one _ _
  simp only [thresholdedSample]
  rw [if_neg (by linarith)]

/-- Threshold preserves confident worlds: weights above θ pass through. -/
theorem threshold_preserves_confident {W : Type*}
    (bel : DistributionalCG W) (θ : ℝ) (w : W) (h : bel.weight w ≥ θ) :
    thresholdedSample bel θ w = bel.weight w := if_pos h

-- ════════════════════════════════════════════════════
-- § 21. Redundancy and Difference Sampling (§7.2)
-- ════════════════════════════════════════════════════

/-! Under weighted sampling, a speaker whose beliefs match the CommonGround keeps
repeating already-shared information (Figure 14). Difference-based
sampling fixes this by weighting worlds by `max(0, Bel(w) - CommonGround(w))`:
worlds already established in the CommonGround get zero weight.

Combined with thresholding, **thresholded difference-based sampling**
gives the best behavior (Figure 15): informed speakers contribute new
information, noncommittal speakers pass. -/

/-- When beliefs match the CommonGround exactly, difference sampling assigns zero
weight to all worlds — nothing new to contribute. -/
theorem difference_zero_when_aligned {W : Type*}
    (cg : DistributionalCG W) (w : W) :
    differenceSample cg cg w = 0 := by
  simp only [differenceSample, sub_self, max_self]

/-- Difference sampling assigns positive weight when belief exceeds CommonGround —
these worlds carry new information not yet in the common ground. -/
theorem difference_positive_when_exceeds {W : Type*}
    (bel cg : DistributionalCG W) (w : W) (h : cg.weight w < bel.weight w) :
    0 < differenceSample bel cg w := by
  simp only [differenceSample]
  exact lt_of_lt_of_le (by linarith : (0 : ℝ) < bel.weight w - cg.weight w) (le_max_right 0 _)

/-- A's initial difference from uniform CommonGround: Nancy has the highest
positive difference (belief 3 vs CommonGround 1), so A's first contribution
should describe Nancy — matching the stochastic trace in Figure 5. -/
theorem a_initial_diff_nancy_highest :
    aDiffFromUniform .nancy > aDiffFromUniform .ina ∧
    aDiffFromUniform .nancy > aDiffFromUniform .katie ∧
    aDiffFromUniform .nancy > aDiffFromUniform .sally := by
  have hn : aDiffFromUniform .nancy = 1 / 4 := by
    simp only [aDiffFromUniform, differenceSample, beliefsA_weight,
      DistributionalCG.uniform_weight, card_mfworld, if_pos]
    rw [max_eq_right (by norm_num)]; norm_num
  have ho : ∀ w : MFWorld, w ≠ .nancy → aDiffFromUniform w = 0 := by
    intro w hw
    simp only [aDiffFromUniform, differenceSample, beliefsA_weight,
      DistributionalCG.uniform_weight, card_mfworld, if_neg hw]
    rw [max_eq_left (by norm_num)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [hn]
  · rw [ho .ina (by decide)]; norm_num
  · rw [ho .katie (by decide)]; norm_num
  · rw [ho .sally (by decide)]; norm_num

end Anderson2021

