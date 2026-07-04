import Linglib.Core.Probability.Choice.Learning
import Linglib.Core.Probability.Constructions
import Linglib.Core.Probability.Entropy
import Linglib.Core.Probability.Scores
import Linglib.Discourse.CommonGround

/-!
# [anderson-2021]: conversation update for RSA
[luce-1959] [stalnaker-2002] [frank-goodman-2012]

Tell me everything you know (SCiL 2021, 244–253): multi-turn conversation
in RSA. The common ground is a probability distribution over worlds
substituted for the RSA world prior (Figure 4), updated each turn by
convex combination with the pragmatic-listener posterior at a learning
rate, with weighted, thresholded, and difference sampling for cooperative
observation selection.

## Main results

* `updateCG_matches_linear_learning`: the update rule is [luce-1959]'s
  linear learning rule — multi-turn conversation is iterated learning
  over distributions.
* `lr_one_excludes_false_worlds` / `graded_update_keeps_false_world`:
  set-intersection update is the lr = 1 degenerate limit; the graded
  common ground is non-monotonic by design (fn. 7).
* Turn-1 and turn-2 predictions over the MutualFriends worlds
  (individuals typed by major × location), including
  `turn2_breaks_symmetry`: an updated common ground changes what the
  same utterance conveys.
* `toBToMSharedUpdate`: `Shared := PMF W` instantiates
  `BToMModel.sharedUpdate` — BToM discourse dynamics with a
  distributional shared state.

## Implementation notes

The Figure-4 chain is exact ℚ≥0, parameterized by common-ground weights:
each agent (`l0Score`/`s1Score`/`l1Score`/`s2Score`) is one
`PMF.normalizeScores` application over the agent below it, the
distributions are `PMF.ofScores`, and every prediction closes by the
`ofScores` comparison family with one kernel certificate.
-/
/-! ### Distributional common ground

`PMF W` wraps `PMF W`: [stalnaker-2002]'s context set with
graded plausibility summing to one (§3.2), so entropy — Anderson's
success criterion — and KL divergence are available on the carrier.
`toContextSet` projects to the positive-mass worlds (`PMF.support`),
`PMF.uniformOfFintype` is the empty common ground; `ofWeights` renormalizes
non-negative weights (fn. 3). Unlike the classical context set, worlds
can regain probability (fn. 7); intersection update survives only at
lr = 1. -/
namespace Discourse

open CommonGround (ContextSet HasContextSet)

/-! ### The common ground as a distribution

Anderson's distributional common ground *is* a `PMF W` ([anderson-2021]
§3.2): graded plausibility summing to one, with `PMF.entropy` — the
success criterion — and `PMF.toRealFn` (the ℝ-valued masses every RSA
consumer reads) already on the carrier. The classical context set is the
support. -/

/-- A distribution projects to [stalnaker-2002]'s context set: the
    positive-mass worlds. -/
instance {W : Type*} : HasContextSet (PMF W) W := ⟨fun p w => w ∈ p.support⟩

@[simp] theorem pmf_toContextSet {W : Type*} (p : PMF W) (w : W) :
    HasContextSet.toContextSet p w ↔ 0 < p.toRealFn w := by
  show w ∈ p.support ↔ _
  rw [PMF.mem_support_iff, PMF.toRealFn, ENNReal.toReal_pos_iff,
    pos_iff_ne_zero]
  exact (and_iff_left (lt_top_iff_ne_top.mpr (p.apply_ne_top w))).symm

/-- Mass of the uniform distribution, in ℝ. -/
@[simp] theorem _root_.PMF.uniformOfFintype_toRealFn (W : Type*) [Fintype W]
    [Nonempty W] (w : W) :
    (PMF.uniformOfFintype W).toRealFn w = (Fintype.card W : ℝ)⁻¹ := by
  show ((PMF.uniformOfFintype W) w).toReal = _
  rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-! ### Renormalising constructor -/

variable {W : Type*}

/-- Build a common ground from non-negative `ℝ` weights by renormalising
    (Anderson 2021, footnote 3: *"the probabilities are renormalized"*).
    Routes through `PMF.ofRealWeightFn`; the positivity witness is derived
    from the positive total. -/
noncomputable def ofWeights [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) : PMF W :=
  have hex : ∃ w, 0 < f w := by
    by_contra h
    push Not at h
    exact absurd hpos (not_lt.mpr (Finset.sum_nonpos fun w _ => h w))
  PMF.ofRealWeightFn f hn hex.choose hex.choose_spec

/-- Closed form of a renormalised mass: each weight divided by the total.
    Anderson's renormalisation made explicit (`CG(w) = f(w) / Σ f`). -/
theorem ofWeights_weight_eq [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) (w : W) :
    (ofWeights f hn hpos).toRealFn w = f w / (∑ x, f x) := by
  simp only [PMF.toRealFn, ofWeights, PMF.ofRealWeightFn_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hn w),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => hn x), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hpos.le, div_eq_mul_inv]

/-- Renormalisation preserves the strict ordering of weights — the same
    positive total divides both sides. Drives the "beliefs favour world
    `w`" comparisons. -/
theorem ofWeights_weight_lt_iff [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) (w₁ w₂ : W) :
    (ofWeights f hn hpos).toRealFn w₁ < (ofWeights f hn hpos).toRealFn w₂ ↔
      f w₁ < f w₂ := by
  rw [ofWeights_weight_eq, ofWeights_weight_eq, div_lt_div_iff_of_pos_right hpos]

/-- Renormalising an already-normalised weight vector recovers it exactly. -/
theorem ofWeights_weight [Fintype W] (f : W → ℝ) (hn : ∀ w, 0 ≤ f w)
    (hpos : 0 < ∑ w, f w) (hsum : ∑ w, f w = 1) (w : W) :
    (ofWeights f hn hpos).toRealFn w = f w := by
  rw [ofWeights_weight_eq, hsum, div_one]

end Discourse

namespace Anderson2021

open CommonGround (ContextSet)
open scoped ENNReal NNReal NNRat

/-! ### MutualFriends Domain -/

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

/-! ### Distributional Common Ground (re-exported from substrate) -/

/-! The `PMF` substrate above supplies the weights; the
conversation-update and RSA content below consume them. -/

/-! ### CommonGround Update -/

/-- Convex-combination update for distributional common ground:

    CommonGround'(w) = (1 - lr) · CommonGround(w) + lr · posterior(w)

Both inputs are genuine distributions, so the `lr`-weighted mixture is
automatically a distribution (no renormalisation needed) — built as a
`PMF.ofFintype` mixture, exactly mirroring `PMF.midPMF`'s `1/2` case. The
learning rate `lr ∈ [0,1]` controls how much weight is given to new
information vs. the existing CommonGround. -/
noncomputable def updateCG {W : Type*} [Fintype W] (cg post : PMF W)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) : PMF W :=
  (PMF.ofFintype
    (fun w => ENNReal.ofReal (1 - lr) * cg w + ENNReal.ofReal lr * post w)
    (by
      have hcg : (∑ w, cg w) = 1 :=
        (tsum_eq_sum (fun w (h : w ∉ Finset.univ) =>
          absurd (Finset.mem_univ w) h)).symm.trans (PMF.tsum_coe cg)
      have hpost : (∑ w, post w) = 1 :=
        (tsum_eq_sum (fun w (h : w ∉ Finset.univ) =>
          absurd (Finset.mem_univ w) h)).symm.trans (PMF.tsum_coe post)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcg, hpost,
        mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) hlr, sub_add_cancel,
        ENNReal.ofReal_one]))

/-- The CommonGround update is the convex combination
`(1 - lr) · CommonGround(w) + lr · posterior(w)`, exactly — both inputs sum
to one, so the mixture preserves total mass with no rescaling. -/
theorem updateCG_eq {W : Type*} [Fintype W] (cg post : PMF W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg post lr h0 h1).toRealFn w =
    (1 - lr) * cg.toRealFn w + lr * post.toRealFn w := by
  simp only [PMF.toRealFn, updateCG, PMF.ofFintype_apply]
  rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (cg.apply_ne_top w))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (post.apply_ne_top w)),
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
    (cg post : PMF W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg post lr h0 h1).toRealFn w =
    ((1 - lr) * cg.toRealFn w + (1 - (1 - lr)) * post.toRealFn w : ℝ) := by
  rw [updateCG_eq]; ring

/-- With learning rate 0, the CommonGround is unchanged (full retention). -/
theorem updateCG_lr_zero {W : Type*} [Fintype W] (cg post : PMF W)
    (w : W) :
    (updateCG cg post 0 (le_refl 0) zero_le_one).toRealFn w = cg.toRealFn w := by
  rw [updateCG_eq]; ring

/-- With learning rate 1, the CommonGround is replaced by the posterior. -/
theorem updateCG_lr_one {W : Type*} [Fintype W] (cg post : PMF W)
    (w : W) :
    (updateCG cg post 1 zero_le_one (le_refl 1)).toRealFn w = post.toRealFn w := by
  rw [updateCG_eq]; ring

/-! ### Conversation State -/

/-- The state of a two-participant conversation (Figure 2).

Tracks the common ground (distributional), each participant's private
beliefs, and the learning rate for updates. In the **shared CommonGround** model
(§5.1, Figure 4), both participants access the same `cg`. In the
**approximate CommonGround** model (§5.2, Figure 6), each maintains a separate
approximation (not yet formalized).

The distributional CommonGround enters the RSA model at two points
(Figure 4): inside the literal listener and as the pragmatic listener's
prior. At each turn the chain is rebuilt at the current CommonGround
(`conversationStep`). -/
structure ConversationState (W : Type*) where
  cg : PMF W
  belA : PMF W
  belB : PMF W
  lr : ℝ
  speakerIsA : Bool

/-- Initial conversation state: uniform CommonGround, specified beliefs, A speaks first. -/
noncomputable def ConversationState.initial {W : Type*} [Fintype W] [Nonempty W]
    (belA belB : PMF W) (lr : ℝ) : ConversationState W where
  cg := PMF.uniformOfFintype W
  belA := belA
  belB := belB
  lr := lr
  speakerIsA := true

/-! ### Observation Sampling -/

/-- **Weighted sampling**: sample a world proportional to the speaker's belief.
Biased toward truth (zero-probability worlds are never sampled) but can
lead to flip-flopping when the speaker has no strong beliefs. -/
noncomputable def weightedSample {W : Type*} (bel : PMF W) : W → ℝ :=
  bel.toRealFn

/-- **Thresholded sampling**: filter out worlds below a confidence threshold.
If no world exceeds the threshold, the speaker produces the null utterance
(passes). Prevents noncommittal speakers from making random assertions. -/
noncomputable def thresholdedSample {W : Type*}
    (bel : PMF W) (θ : ℝ) : W → ℝ :=
  λ w => if bel.toRealFn w ≥ θ then bel.toRealFn w else 0

/-- **Difference-based sampling**: weight worlds by the positive difference
between the speaker's belief and the current CommonGround. Worlds already established
in the CommonGround get downweighted, favoring informative (non-redundant) contributions.

    weight(w) = max(0, Bel(w) - CommonGround(w))

This implements a pressure toward Gricean Quantity: don't repeat what's
already in the common ground. -/
noncomputable def differenceSample {W : Type*}
    (bel cg : PMF W) : W → ℝ :=
  λ w => max 0 (bel.toRealFn w - cg.toRealFn w)

theorem differenceSample_nonneg {W : Type*}
    (bel cg : PMF W) (w : W) :
    0 ≤ differenceSample bel cg w :=
  le_max_left 0 _

/-! ### BToM Shared-State Update -/

/-- Anderson's CommonGround update expressed as a BToM shared-state update.

Given a fixed posterior-computation function (from RSA inference), the CommonGround
update has the type required by `BToMModel.sharedUpdate`:

    Shared → Action → World → Shared

with `Shared := PMF W` and `Action := U`.

The `World` parameter is unused: the listener doesn't know the true world,
so the CommonGround update depends on the *posterior* (derived from the utterance),
not the true world directly. -/
noncomputable def toBToMSharedUpdate {W U : Type*} [Fintype W]
    (posteriorFn : U → PMF W)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    PMF W → U → W → PMF W :=
  fun cg u _w => updateCG cg (posteriorFn u) lr hlr hlr1

/-! ### Example Beliefs -/

/-- The unnormalised belief weights: `peak` on one world, `1` elsewhere.
Their total over the four MutualFriends worlds is `6`. -/
private theorem mfWorld_sum_peak (peak : ℝ) (p : MFWorld) :
    (∑ x : MFWorld, if x = p then peak else 1) = peak + 3 := by
  rw [show (Finset.univ : Finset MFWorld) = {.ina, .katie, .nancy, .sally} from rfl]
  cases p <;>
    simp [Finset.sum_insert, Finset.mem_insert] <;> ring

/-- A believes the person is Nancy: (unnormalised) weight 3 on Nancy, 1 on
others — renormalised to the distribution `[1/6, 1/6, 1/2, 1/6]`. -/
noncomputable def beliefsA : PMF MFWorld :=
  Discourse.ofWeights (fun w => if w = .nancy then 3 else 1)
    (fun w => by split <;> norm_num)
    (Finset.sum_pos' (fun w _ => by split <;> norm_num)
      ⟨.nancy, Finset.mem_univ _, by rw [if_pos rfl]; norm_num⟩)

/-- B believes the person is Katie: (unnormalised) weight 3 on Katie, 1 on
others — renormalised to the distribution `[1/6, 1/2, 1/6, 1/6]`. -/
noncomputable def beliefsB : PMF MFWorld :=
  Discourse.ofWeights (fun w => if w = .katie then 3 else 1)
    (fun w => by split <;> norm_num)
    (Finset.sum_pos' (fun w _ => by split <;> norm_num)
      ⟨.katie, Finset.mem_univ _, by rw [if_pos rfl]; norm_num⟩)

/-- Closed form of A's renormalised beliefs: `3/6` on Nancy, `1/6` elsewhere. -/
theorem beliefsA_weight (w : MFWorld) :
    beliefsA.toRealFn w = (if w = .nancy then 3 else 1) / 6 := by
  rw [beliefsA, Discourse.ofWeights_weight_eq, mfWorld_sum_peak]; norm_num

/-- Closed form of B's renormalised beliefs: `3/6` on Katie, `1/6` elsewhere. -/
theorem beliefsB_weight (w : MFWorld) :
    beliefsB.toRealFn w = (if w = .katie then 3 else 1) / 6 := by
  rw [beliefsB, Discourse.ofWeights_weight_eq, mfWorld_sum_peak]; norm_num

/-- A's beliefs favor Nancy over all other worlds. -/
theorem beliefsA_favors_nancy (w : MFWorld) (hw : w ≠ .nancy) :
    beliefsA.toRealFn w < beliefsA.toRealFn .nancy := by
  rw [beliefsA_weight w, beliefsA_weight .nancy, if_neg hw, if_pos rfl]; norm_num

/-- B's beliefs favor Katie over all other worlds. -/
theorem beliefsB_favors_katie (w : MFWorld) (hw : w ≠ .katie) :
    beliefsB.toRealFn w < beliefsB.toRealFn .katie := by
  rw [beliefsB_weight w, beliefsB_weight .katie, if_neg hw, if_pos rfl]; norm_num

/-- Under difference-based sampling, A initially prioritizes Nancy
(highest positive difference from uniform CommonGround). -/
noncomputable def aDiffFromUniform : MFWorld → ℝ :=
  differenceSample beliefsA (PMF.uniformOfFintype MFWorld)

theorem a_diff_nancy_positive :
    0 < aDiffFromUniform .nancy := by
  rw [aDiffFromUniform, differenceSample, lt_max_iff]
  right
  rw [beliefsA_weight, PMF.uniformOfFintype_toRealFn, card_mfworld]
  norm_num

/-! ### The Figure-4 model on ℚ≥0 scores -/

/-! ### The Figure-4 chain

Shared-CG RSA: `L0 ∝ ⟦u⟧·CG`, `S1 ∝ LitList` (α = 1, fn. 3), `L1 ∝
PragSpeak·CG`, with the endorsement speaker `S2 ∝ L1`. -/
/-! ### b. Score chain (CG-parameterized) -/

/-- CG-weighted literal listener ([anderson-2021] Figure 4: `L0 ∝ ⟦u⟧·CG`). -/
def l0Score (cg : MFWorld → ℚ≥0) (u : MFUtterance) : MFWorld → ℚ≥0 :=
  PMF.normalizeScores fun w => if mfMeaning u w then cg w else 0

/-- Pragmatic speaker ([anderson-2021] Figure 4: `S1 ∝ LitList`; fn. 3: the
softmax terms are omitted and probabilities renormalized, i.e. `α = 1` and
no cost — the speaker weight IS the literal-listener value). -/
def s1Score (cg : MFWorld → ℚ≥0) (w : MFWorld) : MFUtterance → ℚ≥0 :=
  PMF.normalizeScores fun u => l0Score cg u w

/-- Pragmatic listener ([anderson-2021] Figure 4: `L1 ∝ PragSpeak·CG`). -/
def l1Score (cg : MFWorld → ℚ≥0) (u : MFUtterance) : MFWorld → ℚ≥0 :=
  PMF.normalizeScores fun w => cg w * s1Score cg w u

/-- Endorsement speaker: `S2(u|w) ∝ L1(w|u)` (uniform utterance prior),
the standard endorsement inversion of L1 over utterances. -/
def s2Score (cg : MFWorld → ℚ≥0) (w : MFWorld) : MFUtterance → ℚ≥0 :=
  PMF.normalizeScores fun u => l1Score cg u w

/-- Turn-1 speaker (uniform CommonGround, [anderson-2021] Figure 2:
`CG = Uniform(worlds)`). -/
noncomputable def s1Turn1 : MFWorld → PMF MFUtterance :=
  fun w => .ofScores .uniform (s1Score (fun _ => 1) w)

/-- Turn-1 pragmatic listener. -/
noncomputable def l1Turn1 : MFUtterance → PMF MFWorld :=
  fun u => .ofScores .uniform (l1Score (fun _ => 1) u)

/-- Turn-1 endorsement speaker. -/
noncomputable def s2Turn1 : MFWorld → PMF MFUtterance :=
  fun w => .ofScores .uniform (s2Score (fun _ => 1) w)

/-- Turn-1 speaker values ([anderson-2021] Figure-4 equations at the uniform
CG; derived exact rationals — Figure 5 reports the qualitative profile):
`2/5` on each true specific utterance, `1/5` on `null`, `0` off support. -/
theorem s1Turn1_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) (hn : u ≠ .null) :
    s1Turn1 w u = (((2/5 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_eq_ratCast _ (by revert hw hn; cases u <;> cases w <;> decide +kernel)

theorem s1Turn1_null (w : MFWorld) : s1Turn1 w .null = (((1/5 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_eq_ratCast _ (by cases w <;> decide +kernel)

theorem s1Turn1_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) : s1Turn1 w u = 0 := by
  show PMF.ofScores .uniform (s1Score (fun _ => 1) w) u = 0
  rw [PMF.ofScores_apply]
  exact_mod_cast (by revert hw; cases u <;> cases w <;> decide +kernel :
    PMF.scoresWith .uniform (s1Score (fun _ => 1) w) u = 0)

/-- Turn-1 listener values (derived; `L1 ∝ PragSpeak·CG`, Figure 4): `1/2`
on each world satisfying a specific utterance, `1/4` on every world after
`null`, `0` off support. -/
theorem l1Turn1_true {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = true) (hn : u ≠ .null) :
    l1Turn1 u w = (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_eq_ratCast _ (by revert hw hn; cases u <;> cases w <;> decide +kernel)

theorem l1Turn1_null (w : MFWorld) : l1Turn1 .null w = (((1/4 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_eq_ratCast _ (by cases w <;> decide +kernel)

theorem l1Turn1_false {u : MFUtterance} {w : MFWorld}
    (hw : mfMeaning u w = false) : l1Turn1 u w = 0 := by
  show PMF.ofScores .uniform (l1Score (fun _ => 1) u) w = 0
  rw [PMF.ofScores_apply]
  exact_mod_cast (by revert hw; cases u <;> cases w <;> decide +kernel :
    PMF.scoresWith .uniform (l1Score (fun _ => 1) u) w = 0)

/-! ### Turn 1: S1 Predictions -/

/-- A speaker who knows the person is Nancy prefers "studyHumanity" over
"studyScience". Nancy studies German (a humanity), so "studyScience" has
L0(nancy|studyScience) = 0, while "studyHumanity" has L0(nancy|studyHumanity) = 1/2. -/
theorem s1_nancy_prefers_humanity :
    s1Turn1 .nancy .studyScience < s1Turn1 .nancy .studyHumanity :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- A speaker who knows it's Nancy prefers "likeOutdoors" over "likeIndoors".
Nancy likes being outdoors. -/
theorem s1_nancy_prefers_outdoors :
    s1Turn1 .nancy .likeIndoors < s1Turn1 .nancy .likeOutdoors :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- A speaker who knows it's Ina prefers "studyScience" over "studyHumanity".
Ina studies Astronomy (a science). -/
theorem s1_ina_prefers_science :
    s1Turn1 .ina .studyHumanity < s1Turn1 .ina .studyScience :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- A speaker who knows it's Ina is indifferent between "studyScience" and
"likeIndoors": both are true of exactly 2 worlds, giving equal L0 posteriors.
-/
theorem s1_ina_science_eq_indoors :
    s1Turn1 .ina .studyScience = s1Turn1 .ina .likeIndoors :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-- The null utterance is always suboptimal: a speaker who knows it's Nancy
strictly prefers any true specific utterance over saying nothing.
Null is true of all 4 worlds (L0 = 1/4), while "studyHumanity" is true of
only 2 (L0 = 1/2). -/
theorem s1_null_suboptimal :
    s1Turn1 .nancy .null < s1Turn1 .nancy .studyHumanity :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- Symmetry: S1(studyHumanity|nancy) = S1(likeOutdoors|nancy).
Both utterances partition the 4 worlds into 2 true + 2 false, so
L0(nancy|studyHumanity) = L0(nancy|likeOutdoors) = 1/2, hence equal S1. -/
theorem s1_nancy_humanity_eq_outdoors :
    s1Turn1 .nancy .studyHumanity = s1Turn1 .nancy .likeOutdoors :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-- False utterances get zero S1 probability.
"studyScience" is false of Nancy (she studies German), so S1 = 0.
-/
theorem s1_nancy_science_not_gt_null :
    ¬(s1Turn1 .nancy .null < s1Turn1 .nancy .studyScience) :=
  not_lt.mpr (PMF.ofScores_le_cross _ _ (by decide +kernel))

/-! ### Turn 1: L1 Predictions -/

/-- After hearing "studyHumanity", L1 assigns higher probability to Nancy
than to Ina. Nancy studies a humanity; Ina studies a science. -/
theorem l1_humanity_favors_nancy :
    l1Turn1 .studyHumanity .ina < l1Turn1 .studyHumanity .nancy :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- After hearing "likeOutdoors", L1 favors Nancy over Sally.
Nancy likes outdoors; Sally likes indoors. -/
theorem l1_outdoors_favors_nancy :
    l1Turn1 .likeOutdoors .sally < l1Turn1 .likeOutdoors .nancy :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- After hearing "studyHumanity", L1 assigns equal probability to Nancy
and Sally — both study a humanity, and S1 scores are symmetric. -/
theorem l1_humanity_nancy_eq_sally :
    l1Turn1 .studyHumanity .nancy = l1Turn1 .studyHumanity .sally :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-- After hearing "studyScience", L1 assigns equal probability to Ina
and Katie — both study a science. -/
theorem l1_science_ina_eq_katie :
    l1Turn1 .studyScience .ina = l1Turn1 .studyScience .katie :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-- The null utterance conveys no information: L1 assigns equal probability
to all worlds. Every world has S1(null|w) = 1/5 by the domain's symmetry
(each world makes exactly 2 non-null utterances true). -/
theorem l1_null_uniform (w₁ w₂ : MFWorld) :
    l1Turn1 .null w₁ = l1Turn1 .null w₂ := by
  rw [l1Turn1_null, l1Turn1_null]

/-! ### Turn 2 (Post-Update Prior) -/

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
def cgTurn2 : MFWorld → ℚ≥0
  | .ina | .katie => 2
  | .nancy | .sally => 3

/-- Turn-2 speaker at the post-update CommonGround. -/
noncomputable def s1Turn2 : MFWorld → PMF MFUtterance :=
  fun w => .ofScores .uniform (s1Score cgTurn2 w)

/-- Turn-2 pragmatic listener. -/
noncomputable def l1Turn2 : MFUtterance → PMF MFWorld :=
  fun u => .ofScores .uniform (l1Score cgTurn2 u)

/-! ### Turn 2 Predictions -/

/-- After CommonGround update from "studyHumanity", L1("likeOutdoors") now favors
Nancy over Katie. In turn 1, they were symmetric (both like outdoors).
The updated prior (3 vs 1) breaks the tie — Nancy's higher CommonGround weight
makes her more probable. This is the key multi-turn prediction. -/
theorem l1_turn2_outdoors_favors_nancy :
    l1Turn2 .likeOutdoors .katie < l1Turn2 .likeOutdoors .nancy :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- After CommonGround update, "likeIndoors" favors Sally over Ina. Both like
indoors, but Sally has higher prior (3 vs 1) from the CommonGround shift. -/
theorem l1_turn2_indoors_favors_sally :
    l1Turn2 .likeIndoors .ina < l1Turn2 .likeIndoors .sally :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- After CommonGround update, "studyScience" still treats Ina and Katie equally:
both study a science and both have equal prior weight (1). -/
theorem l1_turn2_science_ina_eq_katie :
    l1Turn2 .studyScience .ina = l1Turn2 .studyScience .katie :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-- After CommonGround update, "studyHumanity" still treats Nancy and Sally equally:
both study a humanity and both have equal updated prior (3). -/
theorem l1_turn2_humanity_nancy_eq_sally :
    l1Turn2 .studyHumanity .nancy = l1Turn2 .studyHumanity .sally :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-- CommonGround update breaks turn-1 symmetry: in turn 1, L1("likeOutdoors")
assigned equal weight to Nancy and Katie. After the CommonGround shift, Nancy
is favored. Multi-turn conversation enriches inference. -/
theorem turn2_breaks_symmetry :
    l1Turn1 .likeOutdoors .nancy = l1Turn1 .likeOutdoors .katie ∧
    l1Turn2 .likeOutdoors .katie < l1Turn2 .likeOutdoors .nancy :=
  ⟨PMF.ofScores_eq_cross _ _ (by decide +kernel), l1_turn2_outdoors_favors_nancy⟩

/-! ### b. Turn 2: S1 CommonGround-Adapted Speaker -/

/-! ### Turn 2

With the common ground entering L0, the same utterances convey different
information after the first update. -/
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
    s1Turn2 .nancy .studyHumanity < s1Turn2 .nancy .likeOutdoors :=
  PMF.ofScores_lt _ (by decide +kernel)

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
    s1Turn2 .ina .likeIndoors < s1Turn2 .ina .studyScience :=
  PMF.ofScores_lt _ (by decide +kernel)

/-! ### S2: Endorsement Predictions -/

/-- S2 endorsement: given world Nancy, the pragmatic speaker endorses
"studyHumanity" over "studyScience". S2(u|w) ∝ L1(w|u), and
L1(nancy|studyHumanity) > 0 = L1(nancy|studyScience). -/
theorem s2_nancy_endorses_humanity :
    s2Turn1 .nancy .studyScience < s2Turn1 .nancy .studyHumanity :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- S2 endorsement: given world Nancy, "studyHumanity" and "likeOutdoors"
are equally endorsed (symmetric L1 posteriors). -/
theorem s2_nancy_humanity_eq_outdoors :
    s2Turn1 .nancy .studyHumanity = s2Turn1 .nancy .likeOutdoors :=
  PMF.ofScores_eq_cross _ _ (by decide +kernel)

/-! ### Parametric RSA and Conversation Step -/

/-- One step of the Shared CommonGround conversation loop (Figure 2), with
the CommonGround carried on its ℚ≥0 score face (RSA normalizes, so the
proportional weights determine the distribution `(.ofScores .uniform cg)`).

Given the current CommonGround and an utterance:
1. Build the Figure-4 chain at the current CommonGround (`s1Score`)
2. Compute L1 posteriors: the pragmatic listener's world beliefs (`l1Score`)
3. Update the CommonGround via convex combination with the posteriors

This closes the loop: RSA inference → CommonGround update → new RSA model.
The returned CommonGround serves as the world prior for the next turn's model.

**Renormalisation** is intrinsic: `l1Score` is a `PMF.normalizeScores`
application ([anderson-2021] fn. 3: *"the probabilities are renormalized"*),
so `updateCG` is a genuine convex combination of distributions by
construction. The guard handles the degenerate case of an utterance
contradicting the entire common ground (dead score row, e.g. `studyHumanity`
against a CG concentrated on Ina): the posterior carries no information and
the CommonGround is left unchanged — matching Anderson's null-utterance
"skip the update" behaviour (§7.1). -/
noncomputable def conversationStep
    (cg : MFWorld → ℚ≥0) (u : MFUtterance)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    PMF MFWorld :=
  if 0 < ∑ w, cg w * s1Score cg w u then
    updateCG (.ofScores .uniform cg) (.ofScores .uniform (l1Score cg u)) lr hlr hlr1
  else .ofScores .uniform cg

/-- The conversation step preserves CommonGround non-negativity (free:
the result is a genuine distribution). -/
theorem conversationStep_nonneg (cg : MFWorld → ℚ≥0)
    (u : MFUtterance) (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) (w : MFWorld) :
    0 ≤ (conversationStep cg u lr hlr hlr1).toRealFn w :=
  (conversationStep cg u lr hlr hlr1).toRealFn_nonneg w

/-- With lr = 0, the conversation step leaves the CommonGround unchanged. -/
theorem conversationStep_lr_zero (cg : MFWorld → ℚ≥0) (u : MFUtterance) (w : MFWorld) :
    (conversationStep cg u 0 (le_refl 0) zero_le_one).toRealFn w
      = ((.ofScores .uniform cg) : PMF MFWorld).toRealFn w := by
  unfold conversationStep
  split
  · exact updateCG_lr_zero _ _ w
  · rfl

/-! ### Qualitative information-sharing properties -/

/-- L1 concentrates probability after an informative utterance:
L1(nancy|studyHumanity) > L1(nancy|null). The null utterance gives
uniform L1 (= 1/4), while "studyHumanity" concentrates on the 2
German-studying worlds (= 1/2). -/
theorem l1_concentrates_after_utterance :
    l1Turn1 .null .nancy < l1Turn1 .studyHumanity .nancy :=
  PMF.ofScores_lt_cross _ _ (by decide +kernel)

/-- Informed speakers are informative: S1 assigns higher probability
to a true specific utterance than to null. -/
theorem s1_informed_speaker_is_informative :
    s1Turn1 .nancy .null < s1Turn1 .nancy .studyHumanity :=
  s1_null_suboptimal

/-! ### Bridge to Classical CommonGround Update -/

/-- Anderson's distributional CommonGround update subsumes [stalnaker-2002]'s
set-intersection update **only in the degenerate `lr = 1` limit**: when the
whole prior CommonGround is discarded (`lr = 1`) and the posterior assigns
zero mass to a world, that world drops out of the context set — recovering
classical elimination.

This is the *one* direction of the Stalnaker bridge that survives. The
graded model diverges for every `lr < 1`; see
`graded_update_keeps_false_world`. -/
theorem lr_one_excludes_false_worlds (cg post : PMF MFWorld)
    (w : MFWorld) (h : post.toRealFn w = 0) :
    ¬CommonGround.HasContextSet.toContextSet
      (updateCG cg post 1 zero_le_one (le_refl 1)) w := by
  rw [Discourse.pmf_toContextSet, updateCG_lr_one, h]
  exact lt_irrefl 0

/-- **The divergence the graded model insists on** (Anderson 2021, footnote
7: *"worlds can regain probability"*). For any `lr < 1`, a world the
utterance rules out (`post.toRealFn w = 0`) is **not** excluded from the
context set — the prior CommonGround keeps it alive with mass
`(1 - lr) · cg.toRealFn w`. This is exactly where Anderson's distributional
update parts ways with Stalnaker's monotone set-intersection: graded
interpolation never deletes a world unless it is *already* dead in the prior.
Linglib surfaces the incompatibility rather than papering over it. -/
theorem graded_update_keeps_false_world (cg post : PMF MFWorld)
    (w : MFWorld) (hcg : 0 < cg.toRealFn w) (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr < 1) :
    CommonGround.HasContextSet.toContextSet (updateCG cg post lr h0 h1.le) w := by
  rw [Discourse.pmf_toContextSet, updateCG_eq]
  have : 0 < (1 - lr) * cg.toRealFn w := mul_pos (by linarith) hcg
  have : 0 ≤ lr * post.toRealFn w :=
    mul_nonneg h0 (PMF.toRealFn_nonneg _ _)
  linarith

/-! ### Exact Numerical Predictions (turn 1) -/

/-! ### Exact turn-1 values -/
-- S1(·|nancy): production probabilities given obs = Nancy

theorem s1_nancy_studyHumanity_val :
    s1Turn1 .nancy .studyHumanity = (((2/5 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  s1Turn1_true (by decide) (by decide)

theorem s1_nancy_studyScience_val :
    s1Turn1 .nancy .studyScience = 0 :=
  s1Turn1_false (by decide)

theorem s1_nancy_likeIndoors_val :
    s1Turn1 .nancy .likeIndoors = 0 :=
  s1Turn1_false (by decide)

theorem s1_nancy_likeOutdoors_val :
    s1Turn1 .nancy .likeOutdoors = (((2/5 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  s1Turn1_true (by decide) (by decide)

theorem s1_nancy_null_val :
    s1Turn1 .nancy .null = (((1/5 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  s1Turn1_null .nancy

-- L1(·|studyHumanity): posteriors used in CommonGround update → Figure 5 panel 1A

theorem l1_studyHumanity_nancy_val :
    l1Turn1 .studyHumanity .nancy = (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  l1Turn1_true (by decide) (by decide)

theorem l1_studyHumanity_sally_val :
    l1Turn1 .studyHumanity .sally = (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
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
    l1Turn1 .null w = (((1/4 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  l1Turn1_null w

/-! ### Approximate CommonGround Model (§5.2, Figure 6) -/

/-! ### Approximate common ground

Separate speaker/listener CG representations (Figure 6): the listener's
Pragmatic Listener runs on their own beliefs, so divergence can arise
when those differ from the common ground. -/
/-- State for the Approximate CommonGround model (§5.2, Figure 6). -/
structure ApproxCGState (W : Type*) where
  cgA : PMF W
  cgB : PMF W
  belA : PMF W
  belB : PMF W
  lr : ℝ
  speakerIsA : Bool

noncomputable def ApproxCGState.initial {W : Type*} [Fintype W] [Nonempty W]
    (belA belB : PMF W) (lr : ℝ) : ApproxCGState W where
  cgA := PMF.uniformOfFintype W
  cgB := PMF.uniformOfFintype W
  belA := belA
  belB := belB
  lr := lr
  speakerIsA := true

/-- Approximate comprehension listener ([anderson-2021] Figure 6): L0/S1 run
over the listener's CommonGround approximation `CG_L`, but the Bayesian
inversion uses the listener's private beliefs `B_L` as the prior. -/
noncomputable def approxL1 (cgL belL : MFWorld → ℚ≥0) (u : MFUtterance) : PMF MFWorld :=
  .ofScores .uniform (PMF.normalizeScores fun w => belL w * s1Score cgL w u)

/-- When beliefs equal the CommonGround, the approximate model reduces to the
shared CommonGround model — the split is only meaningful when they diverge. -/
theorem approx_reduces_to_shared (cg : MFWorld → ℚ≥0) (u : MFUtterance) :
    approxL1 cg cg u = .ofScores .uniform (l1Score cg u) := rfl

/-! ### Belief Update Model (§6, Figure 8) -/

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
  cgA : PMF W
  cgB : PMF W
  belA : PMF W
  belB : PMF W
  /-- Learning rate for CommonGround updates. -/
  cgLR : ℝ
  /-- Learning rate for belief updates (may be lower for skeptical agents). -/
  belLR : ℝ
  speakerIsA : Bool

noncomputable def BeliefUpdateState.initial {W : Type*} [Fintype W] [Nonempty W]
    (belA belB : PMF W) (cgLR belLR : ℝ) :
    BeliefUpdateState W where
  cgA := PMF.uniformOfFintype W
  cgB := PMF.uniformOfFintype W
  belA := belA
  belB := belB
  cgLR := cgLR
  belLR := belLR
  speakerIsA := true

/-- Belief update is algebraically identical to CommonGround update — both are
instances of [luce-1959]'s linear learning rule. The only difference
is the learning rate parameter and the interpretation (private vs shared). -/
theorem belief_update_is_linear_learning {W : Type*} [Fintype W]
    (bel post : PMF W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG bel post lr h0 h1).toRealFn w =
    (1 - lr) * bel.toRealFn w + lr * post.toRealFn w :=
  updateCG_eq bel post lr h0 h1 w

/-! ### Noncommittal Speaker Problem (§7.1) -/

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
    weightedSample (PMF.uniformOfFintype MFWorld) w₁ =
    weightedSample (PMF.uniformOfFintype MFWorld) w₂ := by
  simp only [weightedSample, PMF.uniformOfFintype_toRealFn]

/-- Threshold sampling filters out all worlds when beliefs don't exceed
the threshold. Every mass of a distribution is `≤ 1`, so any `θ > 1`
produces zero weight everywhere — the speaker passes (Figure 13). -/
theorem threshold_filters_uniform (θ : ℝ) (hθ : 1 < θ) (w : MFWorld) :
    thresholdedSample (PMF.uniformOfFintype MFWorld) θ w = 0 := by
  have hle : (PMF.uniformOfFintype MFWorld).toRealFn w ≤ 1 :=
    PMF.toRealFn_le_one _ _
  simp only [thresholdedSample]
  rw [if_neg (by linarith)]

/-- Threshold preserves confident worlds: weights above θ pass through. -/
theorem threshold_preserves_confident {W : Type*}
    (bel : PMF W) (θ : ℝ) (w : W) (h : bel.toRealFn w ≥ θ) :
    thresholdedSample bel θ w = bel.toRealFn w := if_pos h

/-! ### Redundancy and Difference Sampling (§7.2) -/

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
    (cg : PMF W) (w : W) :
    differenceSample cg cg w = 0 := by
  simp only [differenceSample, sub_self, max_self]

/-- Difference sampling assigns positive weight when belief exceeds CommonGround —
these worlds carry new information not yet in the common ground. -/
theorem difference_positive_when_exceeds {W : Type*}
    (bel cg : PMF W) (w : W) (h : cg.toRealFn w < bel.toRealFn w) :
    0 < differenceSample bel cg w := by
  simp only [differenceSample]
  exact lt_of_lt_of_le (by linarith : (0 : ℝ) < bel.toRealFn w - cg.toRealFn w) (le_max_right 0 _)

/-- A's initial difference from uniform CommonGround: Nancy has the highest
positive difference (belief 3 vs CommonGround 1), so A's first contribution
should describe Nancy — matching the stochastic trace in Figure 5. -/
theorem a_initial_diff_nancy_highest :
    aDiffFromUniform .nancy > aDiffFromUniform .ina ∧
    aDiffFromUniform .nancy > aDiffFromUniform .katie ∧
    aDiffFromUniform .nancy > aDiffFromUniform .sally := by
  have hn : aDiffFromUniform .nancy = 1 / 4 := by
    simp only [aDiffFromUniform, differenceSample, beliefsA_weight,
      PMF.uniformOfFintype_toRealFn, card_mfworld, if_pos]
    rw [max_eq_right (by norm_num)]; norm_num
  have ho : ∀ w : MFWorld, w ≠ .nancy → aDiffFromUniform w = 0 := by
    intro w hw
    simp only [aDiffFromUniform, differenceSample, beliefsA_weight,
      PMF.uniformOfFintype_toRealFn, card_mfworld, if_neg hw]
    rw [max_eq_left (by norm_num)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [hn]
  · rw [ho .ina (by decide)]; norm_num
  · rw [ho .katie (by decide)]; norm_num
  · rw [ho .sally (by decide)]; norm_num

end Anderson2021

