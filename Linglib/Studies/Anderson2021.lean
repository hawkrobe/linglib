import Linglib.Core.Learning.Luce
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

variable {W : Type*}

/-! ### The common ground as a distribution

Anderson's distributional common ground *is* a `PMF W` ([anderson-2021]
§3.2): graded plausibility summing to one, with `PMF.entropy` — the
success criterion — and `PMF.toRealFn` (the ℝ-valued masses every RSA
consumer reads) already on the carrier. The classical context set is the
support. -/

/-- A distribution projects to [stalnaker-2002]'s context set: the
    positive-mass worlds. -/
instance : HasContextSet (PMF W) W := ⟨fun p w => w ∈ p.support⟩

@[simp] theorem pmf_toContextSet (p : PMF W) (w : W) :
    HasContextSet.toContextSet p w ↔ 0 < p.toRealFn w :=
  (PMF.mem_support_iff p w).trans
    ⟨fun h => ENNReal.toReal_pos h (p.apply_ne_top w),
     fun h => pos_iff_ne_zero.mp (ENNReal.toReal_pos_iff.mp h).1⟩

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

/-- Common-ground update ([anderson-2021] §6, Figure 2): the `lr`-mixture
of the current common ground with the pragmatic-listener posterior —
`PMF.mix` at the learning rate. -/
noncomputable def updateCG {W : Type*} (cg post : PMF W)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) : PMF W :=
  PMF.mix ⟨lr, hlr⟩ (by exact_mod_cast hlr1) cg post

/-- The update in ℝ: `(1 − lr)·CG + lr·posterior`, no rescaling needed. -/
theorem updateCG_eq {W : Type*} (cg post : PMF W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg post lr h0 h1).toRealFn w =
    (1 - lr) * cg.toRealFn w + lr * post.toRealFn w :=
  PMF.toRealFn_mix _ _ cg post w

/-- **Bridge to [luce-1959] linear learning**: the CommonGround update has the same
algebraic form as `LinearLearner.update` with retention rate `1 - lr` and
reinforcement target `posterior`:

    CommonGround'(w) = (1 - lr) · CommonGround(w) + lr · posterior(w)     [Anderson]
    v'(a)  = α · v(a) + (1 - α) · r(a)                [Luce §4.C]

Setting `α = 1 - lr` and `r = posterior` makes the formulas identical.
Multi-turn conversation IS iterated learning over distributions. -/
theorem updateCG_matches_linear_learning {W : Type*}
    (cg post : PMF W)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg post lr h0 h1).toRealFn w =
    ((1 - lr) * cg.toRealFn w + (1 - (1 - lr)) * post.toRealFn w : ℝ) := by
  rw [updateCG_eq]; ring

/-- With learning rate 0, the CommonGround is unchanged (full retention). -/
theorem updateCG_lr_zero {W : Type*} (cg post : PMF W)
    (w : W) :
    (updateCG cg post 0 (le_refl 0) zero_le_one).toRealFn w = cg.toRealFn w := by
  rw [updateCG_eq]; ring

/-- With learning rate 1, the CommonGround is replaced by the posterior. -/
theorem updateCG_lr_one {W : Type*} (cg post : PMF W)
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

/-- Weighted sampling (§7.1): a world sampled in proportion to the
speaker's belief — truthful (zero-probability worlds never sampled) but
flip-flop-prone for noncommittal speakers (Figure 12). -/
noncomputable def weightedSample {W : Type*} (bel : PMF W) : W → ℝ :=
  bel.toRealFn

/-- Thresholded sampling (§7.1.1): worlds below the confidence threshold
are filtered out; with none left the speaker passes with the null
utterance and "all updates are skipped" (Figure 13). -/
noncomputable def thresholdedSample {W : Type*}
    (bel : PMF W) (θ : ℝ) : W → ℝ :=
  λ w => if bel.toRealFn w ≥ θ then bel.toRealFn w else 0

/-- Difference-based sampling (§7.2.1): worlds weighted by "the largest
(positive) difference in probability between the speaker's beliefs and
the Common Ground" — the paper's own truncation at zero (its fn. 14:
probability *reductions* are also informative but assertions can't convey
them). Non-redundancy as Gricean Quantity. -/
noncomputable def differenceSample {W : Type*}
    (bel cg : PMF W) : W → ℝ :=
  λ w => max 0 (bel.toRealFn w - cg.toRealFn w)

theorem differenceSample_nonneg {W : Type*}
    (bel cg : PMF W) (w : W) :
    0 ≤ differenceSample bel cg w :=
  le_max_left 0 _

/-! ### BToM Shared-State Update -/

/-- Linglib bridge (not in the paper): the common-ground update has the
type `BToMModel.sharedUpdate` expects (`Shared → Action → World → Shared`
at `Shared := PMF W`), instantiating BToM's discourse dynamics with a
distributional shared state. The `World` argument is unused — the update
reads the utterance-derived posterior, never the true world. -/
noncomputable def toBToMSharedUpdate {W U : Type*} [Fintype W]
    (posteriorFn : U → PMF W)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    PMF W → U → W → PMF W :=
  fun cg u _w => updateCG cg (posteriorFn u) lr hlr hlr1

/-! ### The Figure-5 beliefs

The §5.1.1 scenario — A thinks the person is Nancy, B thinks Katie — is
qualitative in the paper; the 3:1 peak (renormalised to ½ there, 1/6
elsewhere) is this file's illustrative instantiation. -/

private theorem mfWorld_sum_peak (peak : ℝ) (p : MFWorld) :
    (∑ x : MFWorld, if x = p then peak else 1) = peak + 3 := by
  rw [show (Finset.univ : Finset MFWorld) = {.ina, .katie, .nancy, .sally} from rfl]
  cases p <;>
    simp [Finset.sum_insert, Finset.mem_insert] <;> ring

/-- Beliefs peaked on one world: illustrative 3:1 weights, renormalised. -/
noncomputable def peakedBeliefs (p : MFWorld) : PMF MFWorld :=
  PMF.ofRealWeightFn (fun w => if w = p then 3 else 1)
    (fun w => by split <;> norm_num)
    (by rw [mfWorld_sum_peak]; norm_num)

/-- A believes Nancy; B believes Katie (Figure 5). -/
noncomputable def beliefsA : PMF MFWorld := peakedBeliefs .nancy

/-- See `beliefsA`. -/
noncomputable def beliefsB : PMF MFWorld := peakedBeliefs .katie

theorem peakedBeliefs_weight (p w : MFWorld) :
    (peakedBeliefs p).toRealFn w = (if w = p then 3 else 1) / 6 := by
  rw [peakedBeliefs, PMF.ofRealWeightFn_toRealFn_apply, mfWorld_sum_peak]; norm_num

/-- Peaked beliefs favor their peak over every other world. -/
theorem peakedBeliefs_favors (p w : MFWorld) (hw : w ≠ p) :
    (peakedBeliefs p).toRealFn w < (peakedBeliefs p).toRealFn p := by
  rw [peakedBeliefs_weight, peakedBeliefs_weight, if_neg hw, if_pos rfl]; norm_num

/-! ### The Figure-4 model on ℚ≥0 scores -/

/-! ### The Figure-4 chain

Shared-CG RSA: `L0 ∝ ⟦u⟧·CG`, `S1 ∝ LitList` (α = 1, fn. 3), `L1 ∝
PragSpeak·CG`, with the endorsement speaker `S2 ∝ L1`. -/
/-! ### The score chain -/

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

/-! ### The prior-transparency mechanism

Worlds with the same truth profile get identical speaker columns — the
common-ground factor cancels out of S1's normalization
(`PMF.normalizeScores_mul_left`) — so L1 orders them purely by their
common-ground weights. Every tie and tie-break below is an instance. -/

/-- Same truth profile, same speaker column: the CG weight scales the
whole L0 row and cancels under normalization. -/
theorem s1Score_congr (cg : MFWorld → ℚ≥0) {w₁ w₂ : MFWorld}
    (h₁ : cg w₁ ≠ 0) (h₂ : cg w₂ ≠ 0)
    (hw : ∀ u, mfMeaning u w₁ = mfMeaning u w₂) :
    s1Score cg w₁ = s1Score cg w₂ := by
  have l0_eq : ∀ w : MFWorld, (∀ u, mfMeaning u w = mfMeaning u w₁) →
      (fun u => l0Score cg u w) = fun u => cg w *
        ((if mfMeaning u w₁ then 1 else 0) /
          ∑ w', if mfMeaning u w' then cg w' else 0) := by
    intro w hwp
    funext u
    rw [l0Score, PMF.normalizeScores, ← hwp u]
    split
    · rw [mul_one_div]
    · rw [zero_div, mul_zero]
  rw [s1Score, s1Score, l0_eq w₁ (fun _ => rfl), l0_eq w₂ (fun u => (hw u).symm),
    PMF.normalizeScores_mul_left h₁, PMF.normalizeScores_mul_left h₂]

/-- L1 orders same-profile worlds by their CG weights alone. -/
theorem l1Score_lt_iff (cg : MFWorld → ℚ≥0) {u : MFUtterance} {w₁ w₂ : MFWorld}
    (h₁ : cg w₁ ≠ 0) (h₂ : cg w₂ ≠ 0)
    (hw : ∀ u', mfMeaning u' w₁ = mfMeaning u' w₂)
    (hu : s1Score cg w₁ u ≠ 0) :
    l1Score cg u w₁ < l1Score cg u w₂ ↔ cg w₁ < cg w₂ := by
  have hs := s1Score_congr cg h₁ h₂ hw
  have hZ : (∑ w, cg w * s1Score cg w u) ≠ 0 := by
    intro h
    exact hu (by simpa [h₁] using
      (Finset.sum_eq_zero_iff.mp h w₁ (Finset.mem_univ _)))
  rw [l1Score, PMF.normalizeScores, PMF.normalizeScores,
    div_lt_div_iff_of_pos_right (pos_iff_ne_zero.mpr hZ), ← hs,
    mul_lt_mul_iff_of_pos_right (pos_iff_ne_zero.mpr hu)]

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

/-! ### Turn-1 predictions -/

/-- The turn-1 speaker: true-and-specific beats false or uninformative;
equal literal posteriors tie (`s1Score_congr` at the uniform CG). -/
theorem s1_turn1_informativity :
    (s1Turn1 .nancy .studyScience < s1Turn1 .nancy .studyHumanity) ∧
    (s1Turn1 .nancy .null < s1Turn1 .nancy .studyHumanity) ∧
    (s1Turn1 .nancy .studyHumanity = s1Turn1 .nancy .likeOutdoors) ∧
    ¬(s1Turn1 .nancy .null < s1Turn1 .nancy .studyScience) ∧
    (s1Turn1 .ina .studyHumanity < s1Turn1 .ina .studyScience) ∧
    (s1Turn1 .ina .studyScience = s1Turn1 .ina .likeIndoors) :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel),
   not_lt.mpr (PMF.ofScores_le_cross _ _ (by decide +kernel)),
   PMF.ofScores_lt _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel)⟩

/-- The turn-1 listener: utterances favor the worlds they discriminate and
tie same-profile worlds at the uniform CG (`l1Score_lt_iff`). -/
theorem l1_turn1_inferences :
    (l1Turn1 .studyHumanity .ina < l1Turn1 .studyHumanity .nancy) ∧
    (l1Turn1 .likeOutdoors .sally < l1Turn1 .likeOutdoors .nancy) ∧
    (l1Turn1 .studyHumanity .nancy = l1Turn1 .studyHumanity .sally) ∧
    (l1Turn1 .studyScience .ina = l1Turn1 .studyScience .katie) :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel)⟩

/-- The null utterance conveys nothing: L1 stays uniform. -/
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

/-! ### Turn-2 predictions -/

/-- After the "studyHumanity" update, L1 orders same-profile worlds by
their new CG weights (`l1Score_lt_iff`): the outdoor pair breaks toward
Nancy, the indoor pair toward Sally, equal-weight pairs stay tied. -/
theorem l1_turn2_prior_effects :
    (l1Turn2 .likeOutdoors .katie < l1Turn2 .likeOutdoors .nancy) ∧
    (l1Turn2 .likeIndoors .ina < l1Turn2 .likeIndoors .sally) ∧
    (l1Turn2 .studyScience .ina = l1Turn2 .studyScience .katie) ∧
    (l1Turn2 .studyHumanity .nancy = l1Turn2 .studyHumanity .sally) :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel)⟩

/-- The key multi-turn prediction: turn 1 ties Nancy and Katie under
"likeOutdoors"; the CG update breaks the tie toward Nancy. -/
theorem turn2_breaks_symmetry :
    l1Turn1 .likeOutdoors .nancy = l1Turn1 .likeOutdoors .katie ∧
    l1Turn2 .likeOutdoors .katie < l1Turn2 .likeOutdoors .nancy :=
  ⟨PMF.ofScores_eq_cross _ _ (by decide +kernel), l1_turn2_prior_effects.1⟩

/-! ### The CG-adapted speaker -/

/-- The CG-weighted L0 makes speakers prefer new over redundant
information: after the update, Nancy's speaker switches to "likeOutdoors"
(re-asserting "studyHumanity" is redundant at 3:3 weights) and Ina's to
"studyScience" (Sally now dominates the indoor partition). At turn 1 both
pairs were symmetric (`s1_turn1_informativity`). -/
theorem s1_turn2_cg_adapted :
    (s1Turn2 .nancy .studyHumanity < s1Turn2 .nancy .likeOutdoors) ∧
    (s1Turn2 .ina .likeIndoors < s1Turn2 .ina .studyScience) :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- The endorsement speaker inverts L1: for Nancy, "studyHumanity" beats
the false "studyScience" and ties the symmetric "likeOutdoors". -/
theorem s2_endorsement :
    (s2Turn1 .nancy .studyScience < s2Turn1 .nancy .studyHumanity) ∧
    (s2Turn1 .nancy .studyHumanity = s2Turn1 .nancy .likeOutdoors) :=
  ⟨PMF.ofScores_lt _ (by decide +kernel),
   PMF.ofScores_eq_cross _ _ (by decide +kernel)⟩

/-! ### Parametric RSA and Conversation Step -/

/-- One Figure-2 loop step on the ℚ≥0 face: build the chain at the
current common ground, take the L1 posterior, and mix it in at the
learning rate. A dead score row — an utterance contradicting the whole
common ground — skips the update (§7.1's null behaviour). -/
noncomputable def conversationStep
    (cg : MFWorld → ℚ≥0) (u : MFUtterance)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    PMF MFWorld :=
  if 0 < ∑ w, cg w * s1Score cg w u then
    updateCG (.ofScores .uniform cg) (.ofScores .uniform (l1Score cg u)) lr hlr hlr1
  else .ofScores .uniform cg

/-- With lr = 0, the conversation step leaves the CommonGround unchanged. -/
theorem conversationStep_lr_zero (cg : MFWorld → ℚ≥0) (u : MFUtterance) (w : MFWorld) :
    (conversationStep cg u 0 (le_refl 0) zero_le_one).toRealFn w
      = ((.ofScores .uniform cg) : PMF MFWorld).toRealFn w := by
  unfold conversationStep
  split
  · exact updateCG_lr_zero _ _ w
  · rfl

/-! ### Qualitative information-sharing properties -/

/-- An informative utterance concentrates L1 above the uniform null
baseline (1/2 vs 1/4 on Nancy). -/
theorem l1_concentrates_after_utterance :
    l1Turn1 .null .nancy < l1Turn1 .studyHumanity .nancy :=
  PMF.ofScores_lt_cross _ _ (by decide +kernel)

/-! ### Bridge to Classical CommonGround Update -/

/-- The [stalnaker-2002] set-intersection update survives only at the
lr = 1 limit: with the prior discarded, a zero-posterior world leaves
the context set. -/
theorem lr_one_excludes_false_worlds (cg post : PMF MFWorld)
    (w : MFWorld) (h : post.toRealFn w = 0) :
    ¬CommonGround.HasContextSet.toContextSet
      (updateCG cg post 1 zero_le_one (le_refl 1)) w := by
  rw [Discourse.pmf_toContextSet, updateCG_lr_one, h]
  exact lt_irrefl 0

/-- The graded divergence (fn. 7: "worlds can regain probability"): at
any lr < 1 the prior keeps a ruled-out world alive with mass
`(1 − lr)·cg w` — the update never deletes a world the prior supports. -/
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

end Anderson2021

