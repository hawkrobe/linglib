import Mathlib.Data.Rat.Defs

/-!
# Weak Evidence Effect: Empirical Data

Experimental data from Barnett, Griffiths & Hawkins (2022) on how weak positive
evidence can backfire when listeners expect speakers to have persuasive goals.

## The Stick Contest

Two contestants each want to convince a judge that the average of 5 hidden sticks
(1"–9") is longer (or shorter) than the midpoint (5"). Each reveals one stick.
Participants play both the speaker role (expectation phase) and judge role
(listener judgment phase).

## Key Findings

1. 67% of participants expected speakers to show the strongest evidence
2. For this group, weak evidence backfired (m = 34.7 on 0–100 scale, vs 50 midpoint)
3. The speaker-dependent RSA model outperforms anchor-and-adjust alternatives

## References

- Barnett, S. A., Griffiths, T. L., & Hawkins, R. D. (2022). A Pragmatic Account
  of the Weak Evidence Effect. *Open Mind*, 6, 169–182.
-/

namespace Phenomena.WeakEvidenceEffect


-- ============================================================
-- Section 1: Experimental Design
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

/-- Which contestant goes first -/
inductive FirstContestant where
  | longBiased   -- wants judge to say "longer"
  | shortBiased  -- wants judge to say "shorter"
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


-- ============================================================
-- Section 2: Behavioral Results
-- ============================================================

/-- Proportion expecting strongest evidence (pragmatic listeners) -/
def pragmaticProportion : ℚ := 485 / 723

/-- Proportion expecting weaker evidence (literal listeners) -/
def literalProportion : ℚ := 238 / 723

theorem pragmatic_is_majority : pragmaticProportion > 1 / 2 := by native_decide

/-- Key interaction: speaker expectations × evidence strength.
t(718) = 5.2, p < 0.001 -/
structure InteractionEffect where
  tStatistic : ℚ
  df : Nat
  pLessThan : ℚ
  deriving Repr

def interactionEffect : InteractionEffect :=
  { tStatistic := 52 / 10  -- 5.2
    df := 718
    pLessThan := 1 / 1000 }

/-- Behavioral result for a listener group -/
structure GroupResult where
  listenerType : ListenerType
  nParticipants : Nat
  meanSlider : ℚ        -- 0–100 scale, 50 = neutral
  ci95Lower : ℚ
  ci95Upper : ℚ
  deriving Repr

/-- Pragmatic group: weak evidence backfires (mean below 50) -/
def pragmaticResult : GroupResult :=
  { listenerType := .pragmatic
    nParticipants := 485
    meanSlider := 347 / 10  -- 34.7
    ci95Lower := 323 / 10   -- 32.3
    ci95Upper := 373 / 10 } -- 37.3

/-- Literal group: no weak evidence effect (mean at 50) -/
def literalResult : GroupResult :=
  { listenerType := .literal
    nParticipants := 238
    meanSlider := 501 / 10  -- 50.1
    ci95Lower := 501 / 10 - 3
    ci95Upper := 501 / 10 + 3 }

/-- Pragmatic group shows backfire: mean significantly below 50 (midpoint) -/
theorem pragmatic_backfire : pragmaticResult.meanSlider < 50 := by native_decide

/-- Literal group shows no backfire: mean at midpoint -/
theorem literal_no_backfire : literalResult.meanSlider > 49 := by native_decide

/-- The two groups differ in the predicted direction -/
theorem groups_differ :
    pragmaticResult.meanSlider < literalResult.meanSlider := by native_decide


-- ============================================================
-- Section 3: Model Comparison (Table 1)
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
-- Section 4: Fitted Parameters
-- ============================================================

/-- Fitted parameters for the best model (RSA speaker-dependent) -/
structure FittedParams where
  betaMAP : ℚ             -- MAP estimate of persuasive bias
  betaCV : ℚ              -- 10-fold CV average β
  responseOffset : ℚ      -- response offset o
  pragmaticMixWeight : ℚ  -- mixture weight for pragmatic group
  literalMixWeight : ℚ    -- mixture weight for literal group
  deriving Repr

def bestModelParams : FittedParams :=
  { betaMAP := 226 / 100          -- β̂ = 2.26
    betaCV := 203 / 100           -- β̄ = 2.03
    responseOffset := -13 / 100   -- ō = -0.13
    pragmaticMixWeight := 99/100  -- p̂_z = 0.99 (J1 dominates)
    literalMixWeight := 1/10 }    -- p̂_z = 0.1 (J0 dominates)

/-- β > 0 provides strong support for non-zero persuasive bias -/
theorem beta_positive : bestModelParams.betaMAP > 0 := by native_decide

/-- Pragmatic group is best explained by J1 (pragmatic listener model) -/
theorem pragmatic_group_uses_j1 :
    bestModelParams.pragmaticMixWeight > 9 / 10 := by native_decide

/-- Literal group is best explained by J0 (literal listener model) -/
theorem literal_group_uses_j0 :
    bestModelParams.literalMixWeight < 2 / 10 := by native_decide

end Phenomena.WeakEvidenceEffect
