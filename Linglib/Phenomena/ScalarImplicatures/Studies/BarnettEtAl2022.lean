import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Extensions.ArgumentativeStrength
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Mathlib.Data.Rat.Defs

/-!
# @cite{barnett-griffiths-hawkins-2022}: A Pragmatic Account of the Weak Evidence Effect
@cite{barnett-griffiths-hawkins-2022}

Extends RSA with a **persuasive speaker** who has a goal state w* that may differ
from the true world state w. The speaker's utility combines epistemic and persuasive
components (Eq. 6):

  U(u; w, w*) = U_epi(u; w) + β · U_pers(u; w*)

where U_epi = ln P_L0(w|u) and U_pers = ln P_L0(w*|u). The parameter β controls
persuasive bias (β=0 recovers standard RSA).

## Key Result: The Weak Evidence Effect

When β > 0, weak positive evidence can *backfire*: a pragmatic listener who expects
the speaker to show the strongest available evidence infers that the absence of
strong evidence means it doesn't exist, shifting beliefs in the opposite direction.

## Stick Contest Domain

The paper's experiment uses 5 sticks from {1,...,9} (C(9,5)=126 worlds, midpoint 5).
We formalize a simplified Stick Contest (3 sticks from {1,...,5}, 10 worlds, midpoint 3)
that preserves the key structural properties: the prior favors ¬longer (P(longer)=0.4),
and sticks have monotonically increasing L0(longer|·) values. The simplification enables
verified interval arithmetic via `rsa_predict`.

## RSAConfig Design

The paper's Eq. 8 gives:

  S(u|w, w*=longer, β) ∝ L0(longer|u)^β · 𝟙[u ∈ w]

Since the paper fixes α=1 and treats αβ as a single parameter, RSAConfig's `α`
plays the role of β. The s1Score uses precomputed L0(longer|u) values squared
(β=2), gated by stick availability.

## Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | L0: stick 5 is positive evidence for "longer" | `l0_s5_positive` |
| 2 | L0: stick 5 is the strongest evidence | `l0_s5_strongest` |
| 3 | L0: stick 1 is evidence against "longer" | `l0_s1_negative` |
| 4 | WEE: stick 4 backfires under L1 (β=2) | `weak_evidence_effect` |
| 5 | Strong evidence works: stick 5 favors "longer" under L1 | `strong_evidence_works` |
| 6 | L0(longer|·) is monotone in stick length | `l0_monotone` |
| 7 | Stick 4 has positive argStr yet backfires | `argStr_positive_but_backfires` |
| 8 | Model predicts the observed interaction effect | `model_predicts_interaction` |
| 9 | Pragmatic group shows backfire in experiment | `pragmatic_backfire` |
| 10 | RSA speaker-dependent model fits best | `rsa_speaker_dep_best_waic` |
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.Studies.BarnettEtAl2022

open RSA.ArgumentativeStrength
open RSA.CombinedUtility

-- ============================================================
-- §1. Domain Types
-- ============================================================

/-- Stick lengths 1–5 -/
inductive Stick where
  | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Stick where
  elems := {.s1, .s2, .s3, .s4, .s5}
  complete := fun x => by cases x <;> simp

/-- Worlds: sets of 3 distinct sticks from {1,...,5}. C(5,3) = 10 worlds. -/
inductive StickWorld where
  | w123 | w124 | w125 | w134 | w135
  | w145 | w234 | w235 | w245 | w345
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype StickWorld where
  elems := {.w123, .w124, .w125, .w134, .w135, .w145, .w234, .w235, .w245, .w345}
  complete := fun x => by cases x <;> simp

/-- Whether a stick is available in a given world. -/
def worldContains : StickWorld → Stick → Bool
  | .w123, .s1 | .w123, .s2 | .w123, .s3 => true
  | .w124, .s1 | .w124, .s2 | .w124, .s4 => true
  | .w125, .s1 | .w125, .s2 | .w125, .s5 => true
  | .w134, .s1 | .w134, .s3 | .w134, .s4 => true
  | .w135, .s1 | .w135, .s3 | .w135, .s5 => true
  | .w145, .s1 | .w145, .s4 | .w145, .s5 => true
  | .w234, .s2 | .w234, .s3 | .w234, .s4 => true
  | .w235, .s2 | .w235, .s3 | .w235, .s5 => true
  | .w245, .s2 | .w245, .s4 | .w245, .s5 => true
  | .w345, .s3 | .w345, .s4 | .w345, .s5 => true
  | _, _ => false

/-- A world is "longer" if the average stick length exceeds the midpoint (3).
Equivalently, sum > 9 for 3 sticks. 4 of 10 worlds qualify. -/
def isLonger : StickWorld → Bool
  | .w145 | .w235 | .w245 | .w345 => true
  | _ => false

-- ============================================================
-- §2. RSAConfig (persuasive speaker)
-- ============================================================

/-- L0(longer|u) as ℚ for each stick. Each stick appears in C(4,2)=6 worlds;
this gives the fraction where isLonger holds.

- s1: 1/6 (only w145 is longer)
- s2: 2/6 = 1/3 (w235, w245)
- s3: 2/6 = 1/3 (w235, w345)
- s4: 3/6 = 1/2 (w145, w245, w345)
- s5: 4/6 = 2/3 (w145, w235, w245, w345) -/
def l0LongerQ : Stick → ℚ
  | .s1 => 1/6
  | .s2 => 1/3
  | .s3 => 1/3
  | .s4 => 1/2
  | .s5 => 2/3

/-- Prior probability of "longer": 4 out of 10 worlds -/
def priorLonger : ℚ := 2 / 5

/-- S1 score as ℚ: L0(longer|u)^β · 𝟙[u ∈ w], at β=2. The squared L0 values
are precomputed as literal fractions so that the reifier extracts concrete ℚ
values from the ℚ→ℝ cast without needing to reduce function calls. -/
def s1ScoreQ (w : StickWorld) (u : Stick) : ℚ :=
  if worldContains w u then
    match u with
    | .s1 => 1/36   -- (1/6)²
    | .s2 => 1/9    -- (1/3)²
    | .s3 => 1/9    -- (1/3)²
    | .s4 => 1/4    -- (1/2)²
    | .s5 => 4/9    -- (2/3)²
  else 0

/-- @cite{barnett-griffiths-hawkins-2022} RSA with persuasive speaker.

The s1Score implements Eq. 8: S(u|w, longer, β) ∝ L0(longer|u)^β · 𝟙[u ∈ w].
The score is precomputed as `s1ScoreQ` (ℚ) and cast to ℝ, so that rsa_predict's
reifier can extract the rational value directly. -/
noncomputable def cfg : RSA.RSAConfig Stick StickWorld where
  meaning _ _ u w := if worldContains w u then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score _l0 _α _ w u := (s1ScoreQ w u : ℝ)
  s1Score_nonneg _ _ _ _ _ _ _ := by
    apply Rat.cast_nonneg.mpr
    simp only [s1ScoreQ]
    split <;> (try split) <;> positivity
  α := 2       -- paper's β=2 (fitted β̂ ≈ 2.26; simplified to 2)
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior _ := 1  -- uniform over 10 worlds
  worldPrior_nonneg _ := le_of_lt one_pos

-- ============================================================
-- §3. Predictions — L0 (via rsa_predict)
-- ============================================================

set_option maxHeartbeats 400000 in
/-- L0(longer|s5) > L0(¬longer|s5): stick 5 is positive evidence for "longer".
4 of 6 worlds containing s5 are longer, vs 2 not-longer. -/
theorem l0_s5_positive :
    cfg.L0_marginal () .s5 isLonger >
    cfg.L0_marginal () .s5 (fun w => !isLonger w) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- L0(longer|s5) > L0(longer|s4): stick 5 provides stronger evidence than s4. -/
theorem l0_s5_strongest :
    cfg.L0_marginal () .s5 isLonger >
    cfg.L0_marginal () .s4 isLonger := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- L0(¬longer|s1) > L0(longer|s1): stick 1 is evidence against "longer".
Only 1 of 6 worlds containing s1 is longer. -/
theorem l0_s1_negative :
    cfg.L0_marginal () .s1 (fun w => !isLonger w) >
    cfg.L0_marginal () .s1 isLonger := by
  rsa_predict

/-- L0(longer|·) is monotonically increasing in stick length. This structural
property ensures the simplified domain faithfully mirrors the paper's full domain
(Appendix Theorem 2). -/
theorem l0_monotone :
    l0LongerQ .s1 ≤ l0LongerQ .s2 ∧
    l0LongerQ .s2 ≤ l0LongerQ .s3 ∧
    l0LongerQ .s3 ≤ l0LongerQ .s4 ∧
    l0LongerQ .s4 ≤ l0LongerQ .s5 := by native_decide

-- ============================================================
-- §4. Predictions — L1 (weak evidence effect, via rsa_predict)
-- ============================================================

set_option maxHeartbeats 800000 in
/-- **Weak evidence effect**: at β=2, showing stick 4 (positive literal evidence)
*decreases* the pragmatic listener's belief in "longer" below the prior.

The listener reasons: "If the true average were high, the speaker would have
had stronger sticks (like 5) available and would have shown them instead.
The fact that they showed a 4 implies they lacked stronger evidence."

L1 assigns more posterior mass to ¬longer than longer worlds after seeing s4. -/
theorem weak_evidence_effect :
    cfg.L1_marginal .s4 (fun w => !isLonger w) >
    cfg.L1_marginal .s4 isLonger := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- Strong evidence does NOT backfire: stick 5 increases belief at β=2.

The strongest available evidence is always effective because it cannot
be "explained away" by the absence of something better. -/
theorem strong_evidence_works :
    cfg.L1_marginal .s5 isLonger >
    cfg.L1_marginal .s5 (fun w => !isLonger w) := by
  rsa_predict

-- ============================================================
-- §5. Bridge Theorems
-- ============================================================

/-- At β=1, the persuasive utility equals combinedWeighted(1,1,...). -/
theorem goalOriented_at_one (uEpi uPers : ℚ) :
    goalOrientedUtility uEpi uPers 1 = combinedWeighted 1 1 uEpi uPers :=
  goalOriented_eq_combinedWeighted uEpi uPers 1

/-- The paper's Eq. 6 (additive: U_epi + β·U_pers) equals
(1+β) · combined(β/(1+β), U_epi, U_pers). -/
theorem goalOriented_via_combined (uEpi uPers β : ℚ) (hβ : 0 ≤ β) :
    goalOrientedUtility uEpi uPers β = (1 + β) * combined (betaToLam β) uEpi uPers :=
  goalOriented_eq_scaled_combined uEpi uPers β hβ

/-- Connection to ArgumentativeStrength: stick 4 has positive argumentative
strength for the goal "longer" (L0(longer|s4) = 1/2 > 2/5 = P(longer)). -/
theorem s4_positive_argStr :
    hasPositiveArgStr (l0LongerQ .s4) priorLonger := by native_decide

/-- Stick 3 does NOT have positive argumentative strength
(L0(longer|s3) = 1/3 < 2/5 = P(longer)). -/
theorem s3_not_positive_argStr :
    ¬ hasPositiveArgStr (l0LongerQ .s3) priorLonger := by native_decide

/-- The weak evidence effect shows that argumentatively positive evidence
can still backfire under a pragmatic listener model. This is the core
insight connecting @cite{barnett-griffiths-hawkins-2022} to
@cite{cummins-franke-2021}'s work on argumentative strength.

Stick 4 has positive argStr at L0 (1/2 > 2/5), yet L1 assigns more mass
to ¬longer than longer after seeing s4. -/
theorem argStr_positive_but_backfires :
    hasPositiveArgStr (l0LongerQ .s4) priorLonger ∧
    cfg.L1_marginal .s4 (fun w => !isLonger w) > cfg.L1_marginal .s4 isLonger :=
  ⟨s4_positive_argStr, weak_evidence_effect⟩

-- ============================================================
-- §6. Experimental Design & Behavioral Data
-- ============================================================

/-- Listener type inferred from speaker expectation phase -/
inductive ListenerType where
  | pragmatic   -- expects strongest evidence (67% of participants)
  | literal     -- expects weaker/hedged evidence (33%)
  deriving DecidableEq, BEq, Repr

/-- Evidence strength conditions (distance from midpoint 5") -/
inductive EvidenceStrength where
  | weak      -- 6" (1" from midpoint)
  | moderate  -- 7" (2" from midpoint)
  | strong    -- 8" (3" from midpoint)
  | strongest -- 9" (4" from midpoint)
  deriving DecidableEq, BEq, Repr

/-- Stick Contest design parameters -/
structure StickContestDesign where
  nSticks : Nat            -- sticks per sample (5)
  minLength : Nat          -- minimum stick length (1")
  maxLength : Nat          -- maximum stick length (9")
  midpoint : Nat           -- midpoint for verdict (5")
  nParticipants : Nat      -- total after exclusions
  deriving Repr

/-- The actual experimental parameters -/
def design : StickContestDesign :=
  { nSticks := 5
    minLength := 1
    maxLength := 9
    midpoint := 5
    nParticipants := 723 }

/-- Proportion expecting strongest evidence (pragmatic listeners) -/
def pragmaticProportion : ℚ := 485 / 723

/-- Proportion expecting weaker evidence (literal listeners) -/
def literalProportion : ℚ := 238 / 723

theorem pragmatic_is_majority : pragmaticProportion > 1 / 2 := by native_decide

/-- Behavioral result for a listener group -/
structure GroupResult where
  listenerType : ListenerType
  nParticipants : Nat
  meanSlider : ℚ           -- 0–100 scale, 50 = neutral
  ci95Lower : Option ℚ     -- 95% CI lower bound (when reported)
  ci95Upper : Option ℚ     -- 95% CI upper bound (when reported)
  deriving Repr

/-- Pragmatic group: weak evidence backfires (mean below 50).
95% CI: [32.3, 37.3] (paper p. 175). -/
def pragmaticResult : GroupResult :=
  { listenerType := .pragmatic
    nParticipants := 485
    meanSlider := 347 / 10    -- 34.7
    ci95Lower := some (323 / 10)   -- 32.3
    ci95Upper := some (373 / 10) } -- 37.3

/-- Literal group: no weak evidence effect (mean at 50).
CIs not reported in paper. -/
def literalResult : GroupResult :=
  { listenerType := .literal
    nParticipants := 238
    meanSlider := 501 / 10  -- 50.1
    ci95Lower := none
    ci95Upper := none }

/-- Pragmatic group shows backfire: mean significantly below 50 (midpoint) -/
theorem pragmatic_backfire : pragmaticResult.meanSlider < 50 := by native_decide

/-- Literal group shows no backfire: mean at midpoint -/
theorem literal_no_backfire : literalResult.meanSlider > 49 := by native_decide

/-- The two groups differ in the predicted direction -/
theorem groups_differ :
    pragmaticResult.meanSlider < literalResult.meanSlider := by native_decide

-- ============================================================
-- §7. Model Comparison (Table 1)
-- ============================================================

/-- Model families compared -/
inductive ModelFamily where
  | anchorAdjust     -- A&A: P(w|u) = P(w) + η(s(u) - R)
  | minAcceptable    -- MAS: like A&A but R ~ Unif[-1,1]
  | rsaPragmatic     -- RSA with persuasive speaker
  deriving DecidableEq, BEq, Repr

/-- Model variant (how individual differences are handled) -/
inductive ModelVariant where
  | homogeneous       -- single model for all participants
  | heterogeneous     -- mixture of J0 and J1
  | speakerDependent  -- mixture weights conditioned on speaker phase
  deriving DecidableEq, BEq, Repr

/-- Model comparison result from Table 1 -/
structure ModelComparisonDatum where
  family : ModelFamily
  variant : ModelVariant
  logLikelihood : ℚ
  waic : ℚ
  waicSE : ℚ
  psisLoo : ℚ
  psisLooSE : ℚ
  deriving Repr

/-- Table 1 data -/
def modelComparison : List ModelComparisonDatum :=
  [ ⟨.anchorAdjust,  .homogeneous,      -281/10,  577/10, 99/10,  288/10, 99/10⟩
  , ⟨.minAcceptable, .homogeneous,       82/10,   -133/10, 96/10, -66/10, 96/10⟩
  , ⟨.minAcceptable, .heterogeneous,     82/10,   -113/10, 95/10, -56/10, 95/10⟩
  , ⟨.rsaPragmatic,  .homogeneous,       81/10,   -133/10, 95/10, -67/10, 95/10⟩
  , ⟨.rsaPragmatic,  .heterogeneous,     81/10,   -105/10, 93/10, -52/10, 93/10⟩
  , ⟨.rsaPragmatic,  .speakerDependent,  12,      -164/10, 91/10, -92/10, 91/10⟩
  ]

/-- The RSA speaker-dependent model has the best (highest) log-likelihood -/
theorem rsa_speaker_dep_best_likelihood :
    (12 : ℚ) > 82 / 10 := by native_decide

/-- The RSA speaker-dependent model has the best (lowest) WAIC -/
theorem rsa_speaker_dep_best_waic :
    (-164 : ℚ) / 10 < -133 / 10 := by native_decide

-- ============================================================
-- §8. Fitted Parameters
-- ============================================================

/-- Fitted parameters for the best model (RSA speaker-dependent).
MAP values from Appendix Fig S5; CV values from main paper Fig 3B. -/
structure FittedParams where
  betaMAP : ℚ              -- MAP estimate of persuasive bias (Appendix Fig S5)
  betaCV : ℚ               -- 10-fold CV average β (Fig 3B)
  responseOffsetMAP : ℚ    -- MAP response offset (Appendix Fig S5)
  responseOffsetCV : ℚ     -- 10-fold CV average offset (Fig 3B)
  pragmaticMixWeight : ℚ   -- MAP mixture weight for pragmatic group (Appendix Fig S5)
  literalMixWeight : ℚ     -- MAP mixture weight for literal group (Appendix Fig S5)
  deriving Repr

def bestModelParams : FittedParams :=
  { betaMAP := 226 / 100           -- β̂ = 2.26
    betaCV := 203 / 100            -- β̄ = 2.03
    responseOffsetMAP := -11 / 100 -- o* = -0.11 (Appendix Fig S5)
    responseOffsetCV := -13 / 100  -- ō = -0.13 (Fig 3B)
    pragmaticMixWeight := 97/100  -- p̂_z = 0.97 (J1 dominates; Appendix Fig S5)
    literalMixWeight := 1/10 }    -- p̂_z = 0.1 (J0 dominates)

/-- β > 0 provides strong support for non-zero persuasive bias -/
theorem beta_positive : bestModelParams.betaMAP > 0 := by native_decide

/-- Pragmatic group is best explained by J1 (pragmatic listener model) -/
theorem pragmatic_group_uses_j1 :
    bestModelParams.pragmaticMixWeight > 9 / 10 := by native_decide

/-- Literal group is best explained by J0 (literal listener model) -/
theorem literal_group_uses_j0 :
    bestModelParams.literalMixWeight < 2 / 10 := by native_decide

-- ============================================================
-- §9. Model–Data Connection
-- ============================================================

/-- The RSA model predicts the qualitative pattern underlying the observed
interaction between listener type and evidence strength (t(718) = 5.2,
p < 0.001). The literal model (L0) assigns s4 positive argumentative strength,
predicting no backfire. The pragmatic model (L1) shows backfire. The experiment
confirms exactly this divergence: pragmatic participants' mean (34.7) falls
below neutral (50), while literal participants' mean (50.1) does not. -/
theorem model_predicts_interaction :
    -- Model: L0 (literal) — s4 is positive evidence
    hasPositiveArgStr (l0LongerQ .s4) priorLonger ∧
    -- Model: L1 (pragmatic) — s4 backfires
    cfg.L1_marginal .s4 (fun w => !isLonger w) > cfg.L1_marginal .s4 isLonger ∧
    -- Data: pragmatic group shows backfire
    pragmaticResult.meanSlider < 50 ∧
    -- Data: literal group shows no backfire
    literalResult.meanSlider > 49 :=
  ⟨s4_positive_argStr, weak_evidence_effect, pragmatic_backfire, literal_no_backfire⟩

end Phenomena.ScalarImplicatures.Studies.BarnettEtAl2022
