import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.Agent.Learning
import Linglib.Core.Semantics.CommonGround

/-!
# Anderson (2021): Conversation Update for RSA

@cite{anderson-2021}

A system for multi-turn conversation update in the Rational Speech Acts
framework. The core contributions:

1. **Common ground as distribution**: the CG is a probability distribution
   over worlds, substituted directly for the RSA world prior
2. **Learning-rate update**: CG evolves via convex combination with
   Pragmatic Listener posteriors
3. **Shared vs. approximate CG**: two models differing in whether
   participants share a single CG representation
4. **Observation sampling**: weighted, thresholded, and difference-based
   strategies for cooperative speaker behavior

## Key Connections

The CG update rule `CG'(w) = (1-lr)·CG(w) + lr·post(w)` is algebraically
identical to @cite{luce-1959}'s linear learning rule with retention rate
`1-lr` and reinforcement target `post`. This connects RSA pragmatics to
learning theory: multi-turn conversation IS iterated learning over
distributions.

The distributional CG refines @cite{stalnaker-2002}'s classical context set:
worlds with zero weight are excluded from the context, recovering
set-intersection update as a special case.

## BToM Connection

Anderson's distributional CG has the type expected by `BToMModel.sharedUpdate`
(`Shared → Action → World → Shared`). Setting `Shared := DistributionalCG W`
instantiates BToM's discourse dynamics for the first time in linglib — the
shared state is a distribution that evolves after each utterance via the
learning-rate update.

## MutualFriends Domain

The paper illustrates predictions using the MutualFriends dataset, where
worlds are individuals characterized by features (major, location) and
utterances describe those features.
-/

namespace Phenomena.Dialogue.Studies.Anderson2021

open Core.CommonGround (ContextSet)

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
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype MFWorld where
  elems := {.ina, .katie, .nancy, .sally}
  complete x := by cases x <;> simp

inductive Major where | astronomy | german
  deriving DecidableEq, Repr, BEq

inductive Location where | indoors | outdoors
  deriving DecidableEq, Repr, BEq

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
  deriving DecidableEq, Repr, BEq, Inhabited

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
-- § 2. Distributional Common Ground
-- ════════════════════════════════════════════════════

/-- A distributional common ground: a non-negative weight function over worlds.

This is the probabilistic counterpart of @cite{stalnaker-2002}'s context set.
Instead of a sharp membership predicate (`W → Prop`), a distributional CG
assigns graded plausibility (`W → ℝ`). -/
structure DistributionalCG (W : Type*) where
  weight : W → ℝ
  weight_nonneg : ∀ w, 0 ≤ weight w

namespace DistributionalCG

variable {W : Type*}

/-- Uniform distributional CG: all worlds equally plausible (empty CG). -/
noncomputable def uniform : DistributionalCG W where
  weight _ := 1
  weight_nonneg _ := le_of_lt one_pos

/-- Bridge to classical context set: a world is "in the context" iff its
weight is positive. This recovers @cite{stalnaker-2002}'s set-membership
view from the distributional representation. -/
def toContextSet (cg : DistributionalCG W) : ContextSet W :=
  λ w => 0 < cg.weight w

/-- Uniform distributional CG maps to the trivial context set. -/
theorem uniform_toContextSet :
    (uniform : DistributionalCG W).toContextSet = ContextSet.trivial := by
  funext w
  simp only [toContextSet, uniform, ContextSet.trivial]
  exact propext ⟨λ _ => True.intro, λ _ => one_pos⟩

/-- A world with zero weight is excluded from the classical context set. -/
theorem zero_weight_excluded (cg : DistributionalCG W) (w : W)
    (h : cg.weight w = 0) : ¬cg.toContextSet w := by
  intro hpos
  simp only [toContextSet] at hpos
  linarith

end DistributionalCG

-- ════════════════════════════════════════════════════
-- § 3. CG Update
-- ════════════════════════════════════════════════════

/-- Convex combination update for distributional common ground:

    CG'(w) = (1 - lr) · CG(w) + lr · posterior(w)

The learning rate `lr ∈ [0,1]` controls how much weight is given to new
information vs. the existing CG. -/
noncomputable def updateCG {W : Type*} (cg : DistributionalCG W)
    (posterior : W → ℝ) (post_nonneg : ∀ w, 0 ≤ posterior w)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    DistributionalCG W where
  weight w := (1 - lr) * cg.weight w + lr * posterior w
  weight_nonneg w := add_nonneg
    (mul_nonneg (by linarith) (cg.weight_nonneg w))
    (mul_nonneg hlr (post_nonneg w))

/-- The CG update formula is a convex combination — definitionally equal
to `(1 - lr) · CG(w) + lr · posterior(w)`. -/
theorem updateCG_eq {W : Type*} (cg : DistributionalCG W)
    (posterior : W → ℝ) (hn : ∀ w, 0 ≤ posterior w)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg posterior hn lr h0 h1).weight w =
    (1 - lr) * cg.weight w + lr * posterior w := rfl

/-- **Bridge to @cite{luce-1959} linear learning**: the CG update has the same
algebraic form as `LinearLearner.update` with retention rate `1 - lr` and
reinforcement target `posterior`:

    CG'(w) = (1 - lr) · CG(w) + lr · posterior(w)     [Anderson]
    v'(a)  = α · v(a) + (1 - α) · r(a)                [Luce §4.C]

Setting `α = 1 - lr` and `r = posterior` makes the formulas identical.
Multi-turn conversation IS iterated learning over distributions. -/
theorem updateCG_matches_linear_learning {W : Type*}
    (cg : DistributionalCG W)
    (posterior : W → ℝ) (hn : ∀ w, 0 ≤ posterior w)
    (lr : ℝ) (h0 : 0 ≤ lr) (h1 : lr ≤ 1) (w : W) :
    (updateCG cg posterior hn lr h0 h1).weight w =
    ((1 - lr) * cg.weight w + (1 - (1 - lr)) * posterior w : ℝ) := by
  simp only [updateCG_eq]; ring

/-- With learning rate 0, the CG is unchanged (full retention). -/
theorem updateCG_lr_zero {W : Type*} (cg : DistributionalCG W)
    (posterior : W → ℝ) (hn : ∀ w, 0 ≤ posterior w) (w : W) :
    (updateCG cg posterior hn 0 (le_refl 0) zero_le_one).weight w =
    cg.weight w := by
  show ((1 - (0 : ℝ)) * cg.weight w + (0 : ℝ) * posterior w : ℝ) = cg.weight w
  ring

/-- With learning rate 1, the CG is replaced by the posterior. -/
theorem updateCG_lr_one {W : Type*} (cg : DistributionalCG W)
    (posterior : W → ℝ) (hn : ∀ w, 0 ≤ posterior w) (w : W) :
    (updateCG cg posterior hn 1 zero_le_one (le_refl 1)).weight w =
    posterior w := by
  show ((1 - (1 : ℝ)) * cg.weight w + (1 : ℝ) * posterior w : ℝ) = posterior w
  ring

-- ════════════════════════════════════════════════════
-- § 4. Conversation State
-- ════════════════════════════════════════════════════

/-- The state of a two-participant conversation.

Tracks the common ground (distributional), each participant's private
beliefs, and the learning rate for updates. In the **shared CG** model,
both participants access the same `cg`. In the **approximate CG** model,
each maintains a separate approximation.

The distributional CG serves as `RSAConfig.worldPrior` — the common ground
IS the world prior in the RSA model. Between turns, the world prior evolves
via `updateCG`, and the RSA model is reconstructed with the updated prior. -/
structure ConversationState (W : Type*) where
  cg : DistributionalCG W
  belA : DistributionalCG W
  belB : DistributionalCG W
  lr : ℝ
  speakerIsA : Bool

/-- Initial conversation state: uniform CG, specified beliefs, A speaks first. -/
noncomputable def ConversationState.initial {W : Type*}
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
def weightedSample {W : Type*} (bel : DistributionalCG W) : W → ℝ :=
  bel.weight

/-- **Thresholded sampling**: filter out worlds below a confidence threshold.
If no world exceeds the threshold, the speaker produces the null utterance
(passes). Prevents noncommittal speakers from making random assertions. -/
noncomputable def thresholdedSample {W : Type*}
    (bel : DistributionalCG W) (θ : ℝ) : W → ℝ :=
  λ w => if bel.weight w ≥ θ then bel.weight w else 0

/-- **Difference-based sampling**: weight worlds by the positive difference
between the speaker's belief and the current CG. Worlds already established
in the CG get downweighted, favoring informative (non-redundant) contributions.

    weight(w) = max(0, Bel(w) - CG(w))

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

/-- Anderson's CG update expressed as a BToM shared-state update.

Given a fixed posterior-computation function (from RSA inference), the CG
update has the type required by `BToMModel.sharedUpdate`:

    Shared → Action → World → Shared

with `Shared := DistributionalCG W` and `Action := U`.

The `World` parameter is unused: the listener doesn't know the true world,
so the CG update depends on the *posterior* (derived from the utterance),
not the true world directly. -/
noncomputable def toBToMSharedUpdate {W U : Type*}
    (posteriorFn : U → W → ℝ)
    (post_nonneg : ∀ u w, 0 ≤ posteriorFn u w)
    (lr : ℝ) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) :
    DistributionalCG W → U → W → DistributionalCG W :=
  fun cg u _w => updateCG cg (posteriorFn u) (post_nonneg u) lr hlr hlr1

-- ════════════════════════════════════════════════════
-- § 7. Example Beliefs
-- ════════════════════════════════════════════════════

/-- A believes the person is Nancy: weight 3 on Nancy, 1 on others. -/
noncomputable def beliefsA : DistributionalCG MFWorld where
  weight
    | .nancy => 3
    | _ => 1
  weight_nonneg w := by cases w <;> norm_num

/-- B believes the person is Katie: weight 3 on Katie, 1 on others. -/
noncomputable def beliefsB : DistributionalCG MFWorld where
  weight
    | .katie => 3
    | _ => 1
  weight_nonneg w := by cases w <;> norm_num

/-- A's beliefs favor Nancy over all other worlds. -/
theorem beliefsA_favors_nancy (w : MFWorld) (hw : w ≠ .nancy) :
    beliefsA.weight w < beliefsA.weight .nancy := by
  cases w <;> simp_all [beliefsA]

/-- B's beliefs favor Katie over all other worlds. -/
theorem beliefsB_favors_katie (w : MFWorld) (hw : w ≠ .katie) :
    beliefsB.weight w < beliefsB.weight .katie := by
  cases w <;> simp_all [beliefsB]

/-- Under difference-based sampling, A initially prioritizes Nancy
(highest positive difference from uniform CG). -/
noncomputable def aDiffFromUniform : MFWorld → ℝ :=
  differenceSample beliefsA DistributionalCG.uniform

theorem a_diff_nancy_positive :
    0 < aDiffFromUniform .nancy := by
  simp only [aDiffFromUniform, differenceSample, beliefsA, DistributionalCG.uniform]
  norm_num

-- ════════════════════════════════════════════════════
-- § 8. RSAConfig: Turn 1 (Uniform Prior)
-- ════════════════════════════════════════════════════

open RSA

/-- RSA model for the MutualFriends domain at turn 1.

The common ground is uniform (no information shared yet), so `worldPrior`
is constant. Boolean literal semantics: L0(w|u) ∝ ⟦u⟧(w).

With `s1Score = identity` and `α = 1`, S1(u|w) ∝ L0(w|u):

    S1(u|w) = L0(w|u) / Σ_{u'} L0(w|u')
    L1(w|u) ∝ Prior(w) · S1(u|w)

This is the standard one-shot RSA model that Anderson applies at each
conversation turn, with `worldPrior` set to the current distributional CG. -/
noncomputable def mfRSA : RSAConfig MFUtterance MFWorld where
  meaning _ _ u w := if mfMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 _ _ w u := l0 u w
  s1Score_nonneg _ _ _ _ _ hl _ := hl _ _
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

-- ════════════════════════════════════════════════════
-- § 9. Turn 1: S1 Predictions
-- ════════════════════════════════════════════════════

/-- A speaker who knows the person is Nancy prefers "studyHumanity" over
"studyScience". Nancy studies German (a humanity), so "studyScience" has
L0(nancy|studyScience) = 0, while "studyHumanity" has L0(nancy|studyHumanity) = 1/2. -/
theorem s1_nancy_prefers_humanity :
    mfRSA.S1 () .nancy .studyHumanity > mfRSA.S1 () .nancy .studyScience := by
  rsa_predict

/-- A speaker who knows it's Nancy prefers "likeOutdoors" over "likeIndoors".
Nancy likes being outdoors. -/
theorem s1_nancy_prefers_outdoors :
    mfRSA.S1 () .nancy .likeOutdoors > mfRSA.S1 () .nancy .likeIndoors := by
  rsa_predict

/-- A speaker who knows it's Ina prefers "studyScience" over "studyHumanity".
Ina studies Astronomy (a science). -/
theorem s1_ina_prefers_science :
    mfRSA.S1 () .ina .studyScience > mfRSA.S1 () .ina .studyHumanity := by
  rsa_predict

/-- A speaker who knows it's Ina is indifferent between "studyScience" and
"likeIndoors": both are true of exactly 2 worlds, giving equal L0 posteriors.
This tests `rsa_predict` on equality goals. -/
theorem s1_ina_science_eq_indoors :
    mfRSA.S1 () .ina .studyScience = mfRSA.S1 () .ina .likeIndoors := by
  rsa_predict

/-- The null utterance is always suboptimal: a speaker who knows it's Nancy
strictly prefers any true specific utterance over saying nothing.
Null is true of all 4 worlds (L0 = 1/4), while "studyHumanity" is true of
only 2 (L0 = 1/2). -/
theorem s1_null_suboptimal :
    mfRSA.S1 () .nancy .studyHumanity > mfRSA.S1 () .nancy .null := by
  rsa_predict

/-- Symmetry: S1(studyHumanity|nancy) = S1(likeOutdoors|nancy).
Both utterances partition the 4 worlds into 2 true + 2 false, so
L0(nancy|studyHumanity) = L0(nancy|likeOutdoors) = 1/2, hence equal S1. -/
theorem s1_nancy_humanity_eq_outdoors :
    mfRSA.S1 () .nancy .studyHumanity = mfRSA.S1 () .nancy .likeOutdoors := by
  rsa_predict

/-- False utterances get zero S1 probability.
"studyScience" is false of Nancy (she studies German), so S1 = 0.
Tests `rsa_predict` on negation of strict inequality. -/
theorem s1_nancy_science_not_gt_null :
    ¬(mfRSA.S1 () .nancy .studyScience > mfRSA.S1 () .nancy .null) := by
  rsa_predict

-- ════════════════════════════════════════════════════
-- § 10. Turn 1: L1 Predictions
-- ════════════════════════════════════════════════════

/-- After hearing "studyHumanity", L1 assigns higher probability to Nancy
than to Ina. Nancy studies a humanity; Ina studies a science. -/
theorem l1_humanity_favors_nancy :
    mfRSA.L1 .studyHumanity .nancy > mfRSA.L1 .studyHumanity .ina := by
  rsa_predict

/-- After hearing "likeOutdoors", L1 favors Nancy over Sally.
Nancy likes outdoors; Sally likes indoors. -/
theorem l1_outdoors_favors_nancy :
    mfRSA.L1 .likeOutdoors .nancy > mfRSA.L1 .likeOutdoors .sally := by
  rsa_predict

/-- After hearing "studyHumanity", L1 assigns equal probability to Nancy
and Sally — both study a humanity, and S1 scores are symmetric. -/
theorem l1_humanity_nancy_eq_sally :
    mfRSA.L1 .studyHumanity .nancy = mfRSA.L1 .studyHumanity .sally := by
  rsa_predict

/-- After hearing "studyScience", L1 assigns equal probability to Ina
and Katie — both study a science. -/
theorem l1_science_ina_eq_katie :
    mfRSA.L1 .studyScience .ina = mfRSA.L1 .studyScience .katie := by
  rsa_predict

/-- The null utterance conveys no information: L1 assigns equal probability
to all worlds. Every world has S1(null|w) = 1/5 by the domain's symmetry
(each world makes exactly 2 non-null utterances true). -/
theorem l1_null_uniform (w₁ w₂ : MFWorld) :
    mfRSA.L1 .null w₁ = mfRSA.L1 .null w₂ := by
  cases w₁ <;> cases w₂ <;> first | rfl | rsa_predict

-- ════════════════════════════════════════════════════
-- § 11. RSAConfig: Turn 2 (Post-Update Prior)
-- ════════════════════════════════════════════════════

/-- RSA model after hearing "studyHumanity" at turn 1.

The distributional CG shifts toward German-studying individuals
(nancy, sally). With learning rate 1/2 from uniform CG (weight 1):

    CG'(nancy) = CG'(sally) = (1-0.5)·1 + 0.5·(1/2 normalized) → weight 3
    CG'(ina)   = CG'(katie) = (1-0.5)·1 + 0.5·0               → weight 1

We use unnormalized weights [1, 1, 3, 3] for [ina, katie, nancy, sally].
This is the core of Anderson's contribution: the CG IS the world prior,
and it evolves between turns via `updateCG`. -/
noncomputable def mfRSA_turn2 : RSAConfig MFUtterance MFWorld where
  meaning _ _ u w := if mfMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 _ _ w u := l0 u w
  s1Score_nonneg _ _ _ _ _ hl _ := hl _ _
  α := 1
  α_pos := one_pos
  worldPrior w := match w with
    | .ina | .katie => 1
    | .nancy | .sally => 3
  worldPrior_nonneg w := by cases w <;> norm_num
  latentPrior_nonneg _ _ := by norm_num

-- ════════════════════════════════════════════════════
-- § 12. Turn 2 Predictions
-- ════════════════════════════════════════════════════

/-- After CG update from "studyHumanity", L1("likeOutdoors") now favors
Nancy over Katie. In turn 1, they were symmetric (both like outdoors).
The updated prior (3 vs 1) breaks the tie — Nancy's higher CG weight
makes her more probable. This is the key multi-turn prediction. -/
theorem l1_turn2_outdoors_favors_nancy :
    mfRSA_turn2.L1 .likeOutdoors .nancy > mfRSA_turn2.L1 .likeOutdoors .katie := by
  rsa_predict

/-- After CG update, "likeIndoors" favors Sally over Ina. Both like
indoors, but Sally has higher prior (3 vs 1) from the CG shift. -/
theorem l1_turn2_indoors_favors_sally :
    mfRSA_turn2.L1 .likeIndoors .sally > mfRSA_turn2.L1 .likeIndoors .ina := by
  rsa_predict

/-- After CG update, "studyScience" still treats Ina and Katie equally:
both study a science and both have equal prior weight (1). -/
theorem l1_turn2_science_ina_eq_katie :
    mfRSA_turn2.L1 .studyScience .ina = mfRSA_turn2.L1 .studyScience .katie := by
  rsa_predict

/-- After CG update, "studyHumanity" still treats Nancy and Sally equally:
both study a humanity and both have equal updated prior (3). -/
theorem l1_turn2_humanity_nancy_eq_sally :
    mfRSA_turn2.L1 .studyHumanity .nancy = mfRSA_turn2.L1 .studyHumanity .sally := by
  rsa_predict

/-- CG update breaks turn-1 symmetry: in turn 1, L1("likeOutdoors")
assigned equal weight to Nancy and Katie. After the CG shift, Nancy
is favored. Multi-turn conversation enriches inference. -/
theorem turn2_breaks_symmetry :
    mfRSA.L1 .likeOutdoors .nancy = mfRSA.L1 .likeOutdoors .katie ∧
    mfRSA_turn2.L1 .likeOutdoors .nancy > mfRSA_turn2.L1 .likeOutdoors .katie := by
  exact ⟨by rsa_predict, l1_turn2_outdoors_favors_nancy⟩

-- ════════════════════════════════════════════════════
-- § 13. S2: Endorsement Predictions
-- ════════════════════════════════════════════════════

/-- S2 endorsement: given world Nancy, the pragmatic speaker endorses
"studyHumanity" over "studyScience". S2(u|w) ∝ L1(w|u), and
L1(nancy|studyHumanity) > 0 = L1(nancy|studyScience). -/
theorem s2_nancy_endorses_humanity :
    mfRSA.S2 .nancy .studyHumanity > mfRSA.S2 .nancy .studyScience := by
  rsa_predict

/-- S2 endorsement: given world Nancy, "studyHumanity" and "likeOutdoors"
are equally endorsed (symmetric L1 posteriors). -/
theorem s2_nancy_humanity_eq_outdoors :
    mfRSA.S2 .nancy .studyHumanity = mfRSA.S2 .nancy .likeOutdoors := by
  rsa_predict

end Phenomena.Dialogue.Studies.Anderson2021
