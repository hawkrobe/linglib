import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Core.Probability.Posterior
import Linglib.Semantics.Modification.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# [hawkins-gweon-goodman-2021]: the division of labor in communication

A resource-rational extension of RSA for perspective-taking in the
[keysar-etal-2003] director–matcher reference game. Perspective-taking is costly,
so each agent allocates effort via a mixture weight `w ∈ [0,1]`, and the optimal
effort depends on the partner's expected effort.

Two PMF reference games formalize the task, built on the canonical operators
(`RSA.L0OfBoolMeaning`, `RSA.S1Belief`, `PMF.posterior`):
* egocentric (`egoL0`/`egoS1`/`egoL1`) — three visible objects, shape alone
  identifies the target.
* asymmetric (`asymL0`/`asymS1`/`asymL1`) — a hidden object behind an occlusion,
  whose feature-match profile is the latent variable (`latentPrior`), marginalized
  via `RSA.marginalizeKernel`; the speaker hedges with more specific utterances.

The mixture model and resource-rational optimization sit outside the RSA loop, in
ℝ, grounded in the PMF literal listener.

## Main declarations

* `egoL1`, `asymL1` — the two pragmatic-listener posteriors.
* `MontaguGrounding.grounding_ego_meaning` — the literal semantics is intersective
  predicate modification (`Modifier.intersective`).
* `asym_S1_prefers_specificity_when_shape_matches` — under asymmetry, the speaker
  prefers a more specific utterance when the hidden object shares a feature.
* `mixUtility`, `rrUtilityFull` — log-space mixture utility and resource-rational
  utility over the perspective-taking weight.
* `no_cost_prefers_full_pt`, `high_cost_penalizes_full_pt` — full perspective-taking
  is worth its cost only when the cost is low.

## Empirical anchors

Experiment 1 (83 dyads, 2×2 occlusion × distractor): speakers used more words under
occlusion (+1.3 words) and under a same-shape distractor (+0.6 words). Experiment 2
(116 dyads, a [keysar-etal-2003] replication): scripted directors elicited ~51%
critical errors vs. ~20% for naive directors, listeners adapted from 43% to 30%
errors over four critical trials, and informativity predicted accuracy (ρ = −0.81).
The eight critical items are the [keysar-etal-2003] materials (the paper's Table 1).
Effect sizes and model fits: [hawkins-gweon-goodman-2021].
-/

namespace HawkinsGweonGoodman2021

/-! ## The RSA model

The egocentric game (`egoL0`/`egoS1`/`egoL1`) is over three visible objects with
a belief-based `α = 2` speaker. The asymmetric game adds a hidden object whose
feature-match profile is the latent variable, each feature matching the target
independently with probability `1/4`. Utterance semantics are intersective
predicate modification (see `MontaguGrounding`).

### Finite types -/

/-- The 3 visible objects in the example display.

    target: shape=0, color=0, texture=0
    d1:     shape=1, color=0, texture=0 (shares color+texture with target)
    d2:     shape=2, color=1, texture=1 (differs on all features) -/
inductive VisObj where
  | target | d1 | d2
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The 4 objects in the asymmetric display (3 visible + 1 behind occlusion) -/
inductive AsymObj where
  | target | d1 | d2 | hidden
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterance: which features to mention (2³ = 8 possible utterances) -/
inductive Utt where
  | null  -- mention nothing
  | s     -- shape only: "the square"
  | c     -- color only: "the blue one"
  | t     -- texture only: "the checked one"
  | sc    -- shape + color: "the blue square"
  | st    -- shape + texture: "the checked square"
  | ct    -- color + texture: "the blue checked one"
  | sct   -- all three: "the blue checked square"
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty VisObj := ⟨.target⟩
instance : Nonempty AsymObj := ⟨.target⟩
instance : Nonempty Utt := ⟨.null⟩

/-- Utterance cost: number of features mentioned -/
def Utt.cost : Utt → ℕ
  | .null => 0 | .s | .c | .t => 1 | .sc | .st | .ct => 2 | .sct => 3

/-! ### Literal semantics -/

/-- Does utterance apply to an entity with given feature-match profile?
    For each feature the utterance mentions, the entity must match the target. -/
def Utt.applies (u : Utt) (shapeOk colorOk textureOk : Bool) : Bool :=
  let s := match u with | .s | .sc | .st | .sct => shapeOk | _ => true
  let c := match u with | .c | .sc | .ct | .sct => colorOk | _ => true
  let t := match u with | .t | .st | .ct | .sct => textureOk | _ => true
  s && c && t

/-- Egocentric literal meaning: does utterance apply to visible object?
    Target matches on all features. d1 differs only on shape. d2 differs on all. -/
def egoMeaning (u : Utt) (w : VisObj) : Bool :=
  match w with
  | .target => true
  | .d1 => u.applies false true true
  | .d2 => u.applies false false false

/-- Asymmetric literal meaning: includes hidden object behind occlusion.
    The hidden object's match profile is the latent variable `l = (matchShape, matchColor, matchTexture)`.
    Each feature independently matches target with P = 1/4. -/
def asymMeaning (l : Bool × Bool × Bool) (u : Utt) (w : AsymObj) : Bool :=
  match w with
  | .target => true
  | .d1 => u.applies false true true
  | .d2 => u.applies false false false
  | .hidden => u.applies l.1 l.2.1 l.2.2

/-! ### Model

Both configurations use the canonical PMF reference-game operators
(`RSA.L0OfBoolMeaning`, `RSA.S1Belief`, `PMF.posterior`), as in
`Studies/TesslerFranke2020PMF`: `L0` is
uniform on an utterance's extension, `S1` is the belief-based speaker with
`α = 2` and no cost, and `L1` is the Bayesian posterior under a uniform world
prior. The asymmetric model marginalizes the hidden-object profile via
`RSA.marginalizeKernel`. -/

open scoped ENNReal

/-! #### Egocentric model -/

/-- Every utterance applies to the target (it matches on all features), so each
extension is non-empty. -/
theorem egoExtension_nonempty (u : Utt) : (RSA.extensionOf egoMeaning u).Nonempty :=
  ⟨.target, RSA.mem_extensionOf.mpr rfl⟩

/-- Literal listener: uniform on the extension of `egoMeaning u`. -/
noncomputable def egoL0 (u : Utt) : PMF VisObj :=
  RSA.L0OfBoolMeaning egoMeaning u (egoExtension_nonempty u)

theorem egoL0_apply_of_false {u : Utt} {w : VisObj} (h : egoMeaning u w ≠ true) :
    egoL0 u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

theorem egoL0_apply_of_true {u : Utt} {w : VisObj} (h : egoMeaning u w = true) :
    egoL0 u w = ((RSA.extensionOf egoMeaning u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem egoL0_ne_zero_of_applies {u : Utt} {w : VisObj} (h : egoMeaning u w = true) :
    egoL0 u w ≠ 0 := by
  rw [← PMF.mem_support_iff, egoL0, RSA.mem_support_L0OfBoolMeaning_iff]; exact h

theorem egoL0_null_ne_zero (w : VisObj) : egoL0 .null w ≠ 0 :=
  egoL0_ne_zero_of_applies (by cases w <;> rfl)

private theorem egoScore_tsum_ne_zero (w : VisObj) :
    ∑' u, (egoL0 u w : ℝ≥0∞) ^ (2 : ℝ) * (1 : ℝ≥0∞) ≠ 0 := by
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, ?_⟩
  rw [mul_one]
  exact (not_congr (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num))).mpr (egoL0_null_ne_zero w)

private theorem egoScore_tsum_ne_top (w : VisObj) :
    ∑' u, (egoL0 u w : ℝ≥0∞) ^ (2 : ℝ) * (1 : ℝ≥0∞) ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => by
    rw [mul_one]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _)

/-- Belief-based speaker: `S1(u | w) ∝ L0(w | u)^2`, no cost (`α = 2`). -/
noncomputable def egoS1 (w : VisObj) : PMF Utt :=
  RSA.S1Belief egoL0 (fun _ => 1) 2 w (egoScore_tsum_ne_zero w) (egoScore_tsum_ne_top w)

theorem egoS1_eq_zero_of_not_applies {u : Utt} {w : VisObj} (h : egoMeaning u w ≠ true) :
    egoS1 w u = 0 := by
  rw [egoS1, RSA.S1Belief_apply, egoL0_apply_of_false h, ENNReal.zero_rpow_of_pos (by norm_num)]
  simp

theorem egoS1_ne_zero_of_applies {u : Utt} {w : VisObj} (h : egoMeaning u w = true) :
    egoS1 w u ≠ 0 :=
  RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ (egoL0_ne_zero_of_applies h) one_ne_zero

/-- Uniform world prior over the three visible objects. -/
noncomputable def egoWorldPrior : PMF VisObj := PMF.uniformOfFintype VisObj

theorem egoMarginal_ne_zero (u : Utt) : PMF.marginal egoS1 egoWorldPrior u ≠ 0 :=
  PMF.marginal_ne_zero _ _ _
    ((egoWorldPrior.mem_support_iff .target).mp (PMF.mem_support_uniformOfFintype _))
    (egoS1_ne_zero_of_applies rfl)

/-- Pragmatic listener: Bayesian posterior of `egoS1` under the uniform prior. -/
noncomputable def egoL1 (u : Utt) : PMF VisObj :=
  PMF.posterior egoS1 egoWorldPrior u (egoMarginal_ne_zero u)

/-- An utterance applying only to the target makes the listener certain: the
posterior puts full mass on the target. -/
theorem egoL1_eq_one_of_unique {u : Utt}
    (h : ∀ w, w ≠ .target → egoMeaning u w ≠ true) : egoL1 u .target = 1 := by
  rw [egoL1]
  exact PMF.posterior_eq_one_of_singleton_score_support _ _ _ _ _
    (fun w' hne => Or.inr (egoS1_eq_zero_of_not_applies (h w' hne)))

/-! #### Asymmetric model

The hidden object's feature-match profile is the latent variable `Profile`,
with prior weight `1` for a match and `3` for a non-match on each feature (each
feature matches the target with probability `1/4`). The speaker is conditioned
on the latent; the listener marginalizes it via `RSA.marginalizeKernel`. -/

/-- Whether the hidden object matches the target on (shape, color, texture). -/
abbrev Profile := Bool × Bool × Bool

theorem asymExtension_nonempty (l : Profile) (u : Utt) :
    (RSA.extensionOf (asymMeaning l) u).Nonempty :=
  ⟨.target, RSA.mem_extensionOf.mpr rfl⟩

/-- Literal listener under hidden profile `l`. -/
noncomputable def asymL0 (l : Profile) (u : Utt) : PMF AsymObj :=
  RSA.L0OfBoolMeaning (asymMeaning l) u (asymExtension_nonempty l u)

theorem asymL0_apply_of_false {l : Profile} {u : Utt} {w : AsymObj}
    (h : asymMeaning l u w ≠ true) : asymL0 l u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

theorem asymL0_apply_of_true {l : Profile} {u : Utt} {w : AsymObj}
    (h : asymMeaning l u w = true) :
    asymL0 l u w = ((RSA.extensionOf (asymMeaning l) u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem asymL0_ne_zero_of_applies {l : Profile} {u : Utt} {w : AsymObj}
    (h : asymMeaning l u w = true) : asymL0 l u w ≠ 0 := by
  rw [← PMF.mem_support_iff, asymL0, RSA.mem_support_L0OfBoolMeaning_iff]; exact h

theorem asymL0_null_ne_zero (l : Profile) (w : AsymObj) : asymL0 l .null w ≠ 0 :=
  asymL0_ne_zero_of_applies (by cases w <;> rfl)

private theorem asymScore_tsum_ne_zero (l : Profile) (w : AsymObj) :
    ∑' u, (asymL0 l u w : ℝ≥0∞) ^ (2 : ℝ) * (1 : ℝ≥0∞) ≠ 0 := by
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, ?_⟩
  rw [mul_one]
  exact (not_congr (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num))).mpr (asymL0_null_ne_zero l w)

private theorem asymScore_tsum_ne_top (l : Profile) (w : AsymObj) :
    ∑' u, (asymL0 l u w : ℝ≥0∞) ^ (2 : ℝ) * (1 : ℝ≥0∞) ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => by
    rw [mul_one]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _)

/-- Speaker conditioned on the hidden-object profile. -/
noncomputable def asymS1 (l : Profile) (w : AsymObj) : PMF Utt :=
  RSA.S1Belief (asymL0 l) (fun _ => 1) 2 w (asymScore_tsum_ne_zero l w) (asymScore_tsum_ne_top l w)

theorem asymS1_eq_zero_of_not_applies {l : Profile} {u : Utt} {w : AsymObj}
    (h : asymMeaning l u w ≠ true) : asymS1 l w u = 0 := by
  rw [asymS1, RSA.S1Belief_apply, asymL0_apply_of_false h, ENNReal.zero_rpow_of_pos (by norm_num)]
  simp

theorem asymS1_ne_zero_of_applies {l : Profile} {u : Utt} {w : AsymObj}
    (h : asymMeaning l u w = true) : asymS1 l w u ≠ 0 :=
  RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ (asymL0_ne_zero_of_applies h) one_ne_zero

/-- Latent prior weight: `1` per matching feature, `3` per non-match. -/
noncomputable def profileWeight (l : Profile) : ℝ≥0∞ :=
  (if l.1 then 1 else 3) * (if l.2.1 then 1 else 3) * (if l.2.2 then 1 else 3)

theorem profileWeight_ne_zero (l : Profile) : profileWeight l ≠ 0 := by
  unfold profileWeight
  exact mul_ne_zero (mul_ne_zero (by split <;> simp) (by split <;> simp)) (by split <;> simp)

theorem profileWeight_ne_top (l : Profile) : profileWeight l ≠ ∞ := by
  unfold profileWeight
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by split <;> simp) (by split <;> simp))
    (by split <;> simp)

private theorem profileWeight_tsum_ne_zero : ∑' l, profileWeight l ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨(true, true, true), profileWeight_ne_zero _⟩

private theorem profileWeight_tsum_ne_top : ∑' l, profileWeight l ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype profileWeight_ne_top

/-- Prior over hidden-object profiles. -/
noncomputable def latentPrior : PMF Profile :=
  PMF.normalize profileWeight profileWeight_tsum_ne_zero profileWeight_tsum_ne_top

theorem latentPrior_ne_zero (l : Profile) : latentPrior l ≠ 0 := by
  rw [← PMF.mem_support_iff, latentPrior, PMF.mem_support_normalize_iff]
  exact profileWeight_ne_zero l

/-- Listener's marginal speaker: hidden profile integrated out. -/
noncomputable def asymMarginalSpeaker (w : AsymObj) : PMF Utt :=
  RSA.marginalizeKernel latentPrior asymS1 w

theorem asymMarginalSpeaker_eq_zero_of_not_applies {u : Utt} {w : AsymObj}
    (h : ∀ l, asymMeaning l u w ≠ true) : asymMarginalSpeaker w u = 0 := by
  rw [asymMarginalSpeaker, RSA.marginalizeKernel_apply, ENNReal.tsum_eq_zero]
  exact fun l => by rw [asymS1_eq_zero_of_not_applies (h l), mul_zero]

theorem asymMarginalSpeaker_ne_zero_of_applies {l : Profile} {u : Utt} {w : AsymObj}
    (h : asymMeaning l u w = true) : asymMarginalSpeaker w u ≠ 0 := by
  rw [← PMF.mem_support_iff, asymMarginalSpeaker, RSA.mem_support_marginalizeKernel_iff]
  exact ⟨l, latentPrior_ne_zero l, asymS1_ne_zero_of_applies h⟩

/-- Uniform world prior over the four objects (three visible + hidden). -/
noncomputable def asymWorldPrior : PMF AsymObj := PMF.uniformOfFintype AsymObj

theorem asymMarginal_ne_zero (u : Utt) :
    PMF.marginal asymMarginalSpeaker asymWorldPrior u ≠ 0 :=
  PMF.marginal_ne_zero _ _ _
    ((asymWorldPrior.mem_support_iff .target).mp (PMF.mem_support_uniformOfFintype _))
    (asymMarginalSpeaker_ne_zero_of_applies (l := (true, true, true)) rfl)

/-- Pragmatic listener: posterior of the latent-marginalized speaker. -/
noncomputable def asymL1 (u : Utt) : PMF AsymObj :=
  PMF.posterior asymMarginalSpeaker asymWorldPrior u (asymMarginal_ne_zero u)


/-! ## Compositional grounding

The literal semantics is intersective predicate modification [heim-kratzer-1998]:
each mentioned feature is an intersective adjective — `Modifier.intersective`
applied to a feature property — and `grounding_ego_meaning` shows `egoMeaning`
is exactly their iterated conjunction. This grounds the `Bool` RSA meaning in
the project-canonical Prop-valued modifier rather than a local copy. -/

namespace MontaguGrounding

open Modifier (intersective)

/-- Shape adjective: holds of the target (the only shape-0 object). -/
def shapeP (w : VisObj) : Prop := w = .target

/-- Color adjective: holds of the objects sharing the target's color (target, d1). -/
def colorP (w : VisObj) : Prop := w = .target ∨ w = .d1

/-- Texture adjective: holds of the objects sharing the target's texture (target, d1). -/
def textureP (w : VisObj) : Prop := w = .target ∨ w = .d1

/-- Compositional utterance denotation: each mentioned feature is an intersective
adjective (`Modifier.intersective`), composed over the trivial base property. -/
def compositionalMeaning : Utt → VisObj → Prop
  | .null => fun _ => True
  | .s    => intersective shapeP (fun _ => True)
  | .c    => intersective colorP (fun _ => True)
  | .t    => intersective textureP (fun _ => True)
  | .sc   => intersective colorP (intersective shapeP (fun _ => True))
  | .st   => intersective textureP (intersective shapeP (fun _ => True))
  | .ct   => intersective textureP (intersective colorP (fun _ => True))
  | .sct  => intersective textureP (intersective colorP (intersective shapeP (fun _ => True)))

/-- **Grounding**: the RSA literal meaning `egoMeaning` holds exactly when the
intersective predicate modification of the mentioned feature adjectives does. -/
theorem grounding_ego_meaning (u : Utt) (w : VisObj) :
    egoMeaning u w = true ↔ compositionalMeaning u w := by
  cases u <;> cases w <;>
    simp only [compositionalMeaning, Modifier.intersective_apply, shapeP, colorP, textureP] <;>
    decide

end MontaguGrounding


/-! ## Predictions

The egocentric model captures the no-occlusion case; the asymmetric model
captures occlusion. Predictions are structural PMF proofs over the canonical
operators (no interval reflection). -/

/-! ### Egocentric predictions -/

/-- Shape-only uniquely identifies the target among visible objects: it applies
to no other visible object, so the listener concentrates on the target. -/
theorem ego_shape_identifies_target : egoL1 .s .target > egoL1 .s .d1 := by
  rw [gt_iff_lt]
  unfold egoL1 egoWorldPrior
  rw [PMF.posterior_lt_iff_kernel_lt_of_uniform,
      egoS1_eq_zero_of_not_applies (by decide : egoMeaning .s .d1 ≠ true)]
  exact pos_iff_ne_zero.mpr (egoS1_ne_zero_of_applies rfl)

/-- The listener is equally confident about the target whether hearing
shape-only or the full description: both apply only to the target among visible
objects, so each makes the listener certain. -/
theorem ego_shape_as_good_as_full : ¬(egoL1 .sct .target > egoL1 .s .target) := by
  rw [egoL1_eq_one_of_unique (u := .sct) (by decide),
      egoL1_eq_one_of_unique (u := .s) (by decide)]
  exact lt_irrefl 1

/-- The speaker is indifferent between shape-only and full description at the
target: both apply only to the target, so both have `L0 = 1` and equal score. -/
theorem ego_S1_indifferent : ¬(egoS1 .target .sct > egoS1 .target .s) := by
  rw [gt_iff_lt, not_lt, egoS1, RSA.S1Belief_apply_le_iff_score_le]
  have h : egoL0 .sct .target = egoL0 .s .target := by
    rw [egoL0_apply_of_true (by decide : egoMeaning .sct .target = true),
        egoL0_apply_of_true (by decide : egoMeaning .s .target = true),
        show (RSA.extensionOf egoMeaning .sct).card = 1 from by decide,
        show (RSA.extensionOf egoMeaning .s).card = 1 from by decide]
  exact le_of_eq (by rw [h])

/-! ### Asymmetric predictions -/

/-- **Paper prediction**: when the hidden object matches the target's shape but
not its color or texture, the speaker prefers the full description over
shape-only — shape-only fails to distinguish the target from the hidden object
(`L0 = 1/2`), while the full description succeeds (`L0 = 1`). -/
theorem asym_S1_prefers_specificity_when_shape_matches :
    asymS1 (true, false, false) .target .sct > asymS1 (true, false, false) .target .s := by
  rw [gt_iff_lt, asymS1, RSA.S1Belief_apply_lt_iff_score_lt, mul_one, mul_one]
  apply ENNReal.rpow_lt_rpow _ (by norm_num : (0 : ℝ) < 2)
  rw [asymL0_apply_of_true (by decide : asymMeaning (true, false, false) .s .target = true),
      asymL0_apply_of_true (by decide : asymMeaning (true, false, false) .sct .target = true),
      show (RSA.extensionOf (asymMeaning (true, false, false)) .s).card = 2 from by decide,
      show (RSA.extensionOf (asymMeaning (true, false, false)) .sct).card = 1 from by decide]
  norm_num

/-- When the hidden object matches no features, the speaker is indifferent:
both shape-only and the full description apply only to the target (`L0 = 1`). -/
theorem asym_S1_indifferent_when_no_match :
    ¬(asymS1 (false, false, false) .target .sct >
      asymS1 (false, false, false) .target .s) := by
  rw [gt_iff_lt, not_lt, asymS1, RSA.S1Belief_apply_le_iff_score_le]
  have h : asymL0 (false, false, false) .sct .target = asymL0 (false, false, false) .s .target := by
    rw [asymL0_apply_of_true (by decide : asymMeaning (false, false, false) .sct .target = true),
        asymL0_apply_of_true (by decide : asymMeaning (false, false, false) .s .target = true),
        show (RSA.extensionOf (asymMeaning (false, false, false)) .sct).card = 1 from by decide,
        show (RSA.extensionOf (asymMeaning (false, false, false)) .s).card = 1 from by decide]
  exact le_of_eq (by rw [h])

/-- Even under asymmetry, the listener identifies the target over `d1`: `s`
applies to no `d1` profile (it differs in shape), so the speaker never produces
`s` at `d1`, and the marginal speaker puts zero mass there. -/
theorem asym_L1_identifies_target : asymL1 .s .target > asymL1 .s .d1 := by
  rw [gt_iff_lt]
  unfold asymL1 asymWorldPrior
  rw [PMF.posterior_lt_iff_kernel_lt_of_uniform,
      asymMarginalSpeaker_eq_zero_of_not_applies (by decide : ∀ l, asymMeaning l .s .d1 ≠ true)]
  exact pos_iff_ne_zero.mpr
    (asymMarginalSpeaker_ne_zero_of_applies (l := (false, false, false)) rfl)

/-- **Paper prediction**: under asymmetry, the full description yields a higher
listener posterior for the target than shape-only — the hidden object can match
individual features, so a more specific utterance is more reliably informative.

TODO: this compares two *latent-marginalized* posteriors at different
conditioning utterances (`L1 .sct` vs `L1 .s`), with distinct normalizing
constants. It reduces to a finite `ℝ≥0∞` comparison over the eight hidden
profiles but is beyond hand-discharge; it awaits the planned `pmf_score_compare`
tactic (cf. `Studies/TesslerFranke2020PMF`). -/
theorem asym_full_desc_better_reference : asymL1 .sct .target > asymL1 .s .target := by
  sorry

/-- Shape+color also beats shape-only: each additional feature narrows the set
of possible hidden distractors.

TODO: same shape as `asym_full_desc_better_reference` (cross-utterance
latent-marginalized posterior comparison); awaits `pmf_score_compare`. -/
theorem asym_shape_color_beats_shape : asymL1 .sc .target > asymL1 .s .target := by
  sorry


/-! ## Resource-rational extensions

The mixture model and resource-rational optimization sit outside the standard
RSA loop. They are defined in ℝ, grounded in the PMF literal listener (`egoL0`,
`asymL0`, via `.toReal`) and the hidden-profile prior `latentPrior`.

The mixture operates in log-space (over utilities, not probabilities): the
mixture speaker uses a weighted geometric mean of L0 values,
`exp(w_S · E[log L0^asym] + (1 − w_S) · log L0^ego)`. The model uses `α = 2` and
a uniform cost that cancels in the S1 normalization. See
[hawkins-gweon-goodman-2021] for the asymmetric/egocentric speaker utilities,
the mixture, and the resource-rational utility. -/

open scoped BigOperators

/-! ### L0 success rates -/

/-- Egocentric L0 success rate: the literal listener's target probability given
`u`, read off `egoL0`. -/
noncomputable def egoInfR (u : Utt) : ℝ := (egoL0 u .target).toReal

/-- Asymmetric L0 success rate: the literal listener's target probability
averaged over hidden profiles, weighted by `latentPrior`. -/
noncomputable def asymInfR (u : Utt) : ℝ :=
  ∑ l : Profile, (latentPrior l).toReal * (asymL0 l u .target).toReal

/-! ### Log-space mixture utilities -/

/-- Expected log-L0 under the asymmetric model (the asymmetric-utility
component): `E_l[log P_L0(target | u, l)]`. By Jensen's inequality this is
`≤ log (asymInfR u)`. -/
noncomputable def asymLogInfR (u : Utt) : ℝ :=
  ∑ l : Profile, (latentPrior l).toReal * Real.log (asymL0 l u .target).toReal

/-- Mixture speaker utility (Eq. 5):
    U^mix(u; w_S) = w_S · E_h[log P_L0^asym(target|u,h)]
                   + (1−w_S) · log P_L0^ego(target|u)
    Uniform cost (0.03) omitted: it cancels in S1 normalization. -/
noncomputable def mixUtility (u : Utt) (wS : ℝ) : ℝ :=
  wS * asymLogInfR u + (1 - wS) * Real.log (egoInfR u)

/-- Mixture S1 score: P_S1^mix(u | target, w_S) ∝ exp(α · U^mix(u; w_S)).
    Paper Eq. 1 with the mixture utility from Eq. 5. -/
noncomputable def mixS1Score (u : Utt) (wS α : ℝ) : ℝ :=
  Real.exp (α * mixUtility u wS)

/-! ### Full resource-rational model

The full model marginalizes over listener perspective-taking weight w_L.

    The simplified model (Eqs 2–5) treats w_L as fixed at 1. The full model
    (Eqs 7–9) has the speaker consider a range of listener weights, and the
    resource-rational analysis (Eq. 10) measures accuracy averaged over w_L.

    **Mixture L0** (Eq. 8): P_{L_0}^{mix}(target|u, l, w_L) =
      w_L · P_{L_0}^{asym}(target|u, l) + (1−w_L) · P_{L_0}^{ego}(target|u).
    At w_L = 0, the listener ignores hidden objects. At w_L = 1, the listener
    accounts for all potential hidden distractors.

    **Marginalized S1** (Eq. 9): the speaker's utility integrates over w_L,
    discretized to 5 grid points {0, 1/4, 1/2, 3/4, 1} with uniform weight.

    **Accuracy** (Eq. 10): since listener accuracy is linear in w_L,
    E_{uniform w_L}[accuracy] = (egoInfR + asymInfR) / 2. -/

/-- Mixture L0 accuracy: probability the mixture listener at weight w_L
correctly identifies the target, given hidden object profile `l`. -/
noncomputable def mixL0Target (u : Utt) (l : Profile) (wL : ℝ) : ℝ :=
  wL * (asymL0 l u .target).toReal + (1 - wL) * egoInfR u

/-- Asymmetric speaker utility at a specific listener weight:
`U^asym(u; w_L) = Σ_l P(l) · log P_L0^mix(target | u, l, w_L)`. -/
noncomputable def asymUtilityAtWL (u : Utt) (wL : ℝ) : ℝ :=
  ∑ l : Profile, (latentPrior l).toReal * Real.log (mixL0Target u l wL)

/-- Mixed speaker utility at specific (w_S, w_L) (Eq. 8). -/
noncomputable def mixUtilityFull (u : Utt) (wS wL : ℝ) : ℝ :=
  wS * asymUtilityAtWL u wL + (1 - wS) * Real.log (egoInfR u)

/-- W_L-marginalized speaker utility (Eq. 9 inside the exp).
    Discretized: 5 uniform grid points at w_L ∈ {0, 1/4, 1/2, 3/4, 1}. -/
noncomputable def mixUtilityMarg (u : Utt) (wS : ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∑ k : Fin 5, mixUtilityFull u wS (↑k / 4)

/-- Full S1 score with w_L marginalization (Eq. 9). -/
noncomputable def mixS1ScoreFull (u : Utt) (wS α : ℝ) : ℝ :=
  Real.exp (α * mixUtilityMarg u wS)

/-- Listener accuracy averaged over uniform w_L (for Eq. 10).
    Since accuracy(u, w_L) = w_L·asymInfR(u) + (1−w_L)·egoInfR(u) is linear
    in w_L, the expectation under uniform P(w_L) is the midpoint. -/
noncomputable def avgListenerAccuracy (u : Utt) : ℝ :=
  (egoInfR u + asymInfR u) / 2

/-- Full expected accuracy (Eq. 10) with w_L marginalization.
    Uses the w_L-marginalized S1 for speaker production and the
    w_L-averaged listener accuracy for evaluation. -/
noncomputable def expectedAccuracyFull (wS α : ℝ) : ℝ :=
  let Z := ∑ u' : Utt, mixS1ScoreFull u' wS α
  if Z = 0 then 0
  else ∑ u : Utt, (mixS1ScoreFull u wS α / Z) * avgListenerAccuracy u

/-- Full resource-rational utility (Eqs 10–11).
    U_RR(w_S) = ExpAccuracy_full(w_S) − β · w_S -/
noncomputable def rrUtilityFull (wS α β : ℝ) : ℝ :=
  expectedAccuracyFull wS α - β * wS

/-! ### Structural properties -/

/-- At w_S = 0, the simplified mixture utility reduces to egocentric log-L0. -/
theorem mixUtility_at_zero (u : Utt) :
    mixUtility u 0 = Real.log (egoInfR u) := by
  unfold mixUtility; ring

/-- At w_S = 1, the simplified mixture utility reduces to asymmetric expected log-L0. -/
theorem mixUtility_at_one (u : Utt) :
    mixUtility u 1 = asymLogInfR u := by
  unfold mixUtility; ring

/-! ### Resource-rational predictions

These three are transcendental ℝ inequalities over `Real.exp`/`Real.log` of the
L0 success rates. The retired interval-reflection tactic discharged them with its
numeric/interval backend; the PMF migration has no equivalent, so they are
stated with `sorry` per CLAUDE.md "prefer `sorry` over weakening". They reduce
to finite real arithmetic and await real-analysis/interval lemmas (or a
`pmf_score_compare`-style numeric tactic). -/

/-- **Paper prediction (β = 0)**: when perspective-taking is free, full PT
(w_S = 1) achieves higher expected accuracy than no PT (w_S = 0) — the
asymmetric speaker produces more specific utterances, improving listener
accuracy.

TODO: transcendental ℝ inequality (exp/log of L0 rates); awaits numeric tactic. -/
theorem no_cost_prefers_full_pt :
    rrUtilityFull 1 2 0 > rrUtilityFull 0 2 0 := by
  sorry

/-- **Paper prediction (high β)**: when perspective-taking is costly, the cost
term `β · w_S` dominates, making w_S = 0 preferable to w_S = 1.

TODO: transcendental ℝ inequality (exp/log of L0 rates); awaits numeric tactic. -/
theorem high_cost_penalizes_full_pt :
    rrUtilityFull 0 2 (1/2) > rrUtilityFull 1 2 (1/2) := by
  sorry

/-- **Interior-optimum limitation**: the paper's central result is that at
moderate cost (β = 0.2) an intermediate weight `w*_S ≈ 0.36` outperforms both
extremes. This 3+1-object reference game is too simple to produce that effect:
shape alone identifies the target among visible objects (`egoInfR .s = 1`), so
the egocentric baseline accuracy is near-ceiling and the marginal gain from
perspective-taking is far below the β = 0.2 cost. So instead no-PT beats full-PT
for all tested β ≥ 1/50.

TODO: transcendental ℝ inequality (exp/log of L0 rates); awaits numeric tactic. -/
theorem simplified_game_no_interior_optimum :
    rrUtilityFull 0 2 (1/50) > rrUtilityFull 1 2 (1/50) := by
  sorry

/-! ### Listener belief adaptation -/

/-- Listener's belief about speaker's perspective-taking weight.
    Over time, listeners update their expectation of w_S based on
    observed utterance informativity. -/
structure ListenerBeliefs where
  wS_expectation : ℝ   -- E[w_S]
  observations : ℕ      -- Number of observed utterances

/-- Initial uniform belief: E[w_S] = 1/2 -/
noncomputable def initialBeliefs : ListenerBeliefs :=
  { wS_expectation := 1/2, observations := 0 }

/-- Update beliefs after observing utterance informativity.
    Short/uninformative utterances → lower w_S estimate;
    long/informative utterances → higher w_S estimate. -/
noncomputable def updateBeliefs (beliefs : ListenerBeliefs) (shortUtterance : Bool) :
    ListenerBeliefs :=
  let newObs := beliefs.observations + 1
  let update : ℝ := if shortUtterance then -1/10 else 1/10
  let newExpectation := max 0 (min 1 (beliefs.wS_expectation + update / newObs))
  { wS_expectation := newExpectation, observations := newObs }

/-- After seeing short utterances, listener expects lower w_S -/
noncomputable def beliefsAfterShortUtterances : ListenerBeliefs :=
  updateBeliefs (updateBeliefs (updateBeliefs initialBeliefs true) true) true

/-- **Paper prediction** ([hawkins-gweon-goodman-2021] §2.4.1):
    Listeners infer low speaker effort from under-informative utterances. -/
theorem listener_infers_low_wS_from_short_utterances :
    beliefsAfterShortUtterances.wS_expectation < initialBeliefs.wS_expectation := by
  unfold beliefsAfterShortUtterances updateBeliefs initialBeliefs
  simp only [ite_true, min_def, max_def]
  split_ifs <;> linarith

/-- Optimal listener weight: compensate for low speaker effort.
    When the speaker uses low w_S, the listener should increase their own
    perspective-taking to compensate. -/
noncomputable def optimalListenerWeight (speakerWS β : ℝ) : ℝ :=
  min 1 (max 0 (1 - speakerWS + β))

/-- **Paper prediction** ([hawkins-gweon-goodman-2021] §2.4.1):
    Listener increases effort when speaker decreases theirs. -/
theorem listener_compensates_for_low_speaker_effort :
    optimalListenerWeight (3/10) (2/10) > optimalListenerWeight (7/10) (2/10) := by
  unfold optimalListenerWeight
  simp only [min_def, max_def]
  split_ifs <;> linarith

end HawkinsGweonGoodman2021
