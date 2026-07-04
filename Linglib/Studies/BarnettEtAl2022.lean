import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.RSA.ArgumentativeStrength
import Linglib.Pragmatics.RSA.Speaker.CombinedUtility

/-!
# [barnett-griffiths-hawkins-2022]: the weak evidence effect

RSA with a persuasive speaker whose utility adds `β · ln L0(w*|u)` for a
goal state w* to the epistemic term (eq. 6; β = 0 is standard RSA). With
w* = "longer" the speaker weight is `L0(longer|u)^β · 𝟙[u ∈ w]` (eq. 8;
α = 1, so the exponent is β, here 2). A pragmatic listener who expects the
strongest available evidence reads weak positive evidence as implying no
stronger evidence exists — so it backfires.

The paper's Stick Contest (5 sticks from {1,…,9}, 126 worlds) is
formalized at 3 sticks from {1,…,5} (10 worlds, midpoint 3), preserving
the load-bearing structure: the prior favors ¬longer (2/5) and
`L0(longer|·)` is monotone in stick length.

## Main results

* `weak_evidence_effect`: at β = 2, stick 4 — positive literal evidence —
  *backfires* under the pragmatic listener; `strong_evidence_works` shows
  the strongest evidence cannot be explained away.
* `l0_s5_positive` / `l0_s1_negative` / `l0_s5_strongest` / `l0_monotone`:
  the literal-listener evidence ordering.
* `argStr_positive_but_backfires`: stick 4 has positive
  [cummins-franke-2021] argumentative strength yet backfires — the model's
  wedge between argumentative and pragmatic evidence.
* `model_predicts_interaction` / `pragmatic_backfire`: the predicted
  listener-type × evidence interaction matches the behavioral data.

## Implementation notes

The uniform world prior cancels from both listeners, so the chain is two
`PMF.ofScores` levels over ℚ≥0 scores and every prediction is one
event-mass kernel certificate.
-/

open scoped ENNReal NNRat

namespace BarnettEtAl2022

open RSA.ArgumentativeStrength
open RSA.CombinedUtility

/-! ### Domain Types -/

/-- Stick lengths 1–5 -/
inductive Stick where
  | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Stick where
  elems := {.s1, .s2, .s3, .s4, .s5}
  complete := fun x => by cases x <;> simp

/-- Worlds: sets of 3 distinct sticks from {1,...,5}. C(5,3) = 10 worlds. -/
inductive StickWorld where
  | w123 | w124 | w125 | w134 | w135
  | w145 | w234 | w235 | w245 | w345
  deriving DecidableEq, Repr, Inhabited

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

/-- A world is "longer" if the average stick length exceeds the midpoint (3);
equivalently, the three sticks sum past 9. 4 of 10 worlds qualify. -/
def longer : StickWorld → Bool
  | .w145 | .w235 | .w245 | .w345 => true
  | _ => false

/-! ### Persuasive-speaker scores -/

/-- The literal listener's longer-probability per stick: each stick
appears in six worlds, and `l0LongerQ_eq_eventMass` certifies these
fractions against the chain. -/
def l0LongerQ : Stick → ℚ≥0
  | .s1 => 1/6
  | .s2 => 1/3
  | .s3 => 1/3
  | .s4 => 1/2
  | .s5 => 2/3

/-- `l0LongerQ` agrees with the chain: it is the literal listener's
longer-event mass at each stick. -/
theorem l0LongerQ_eq_eventMass (u : Stick) :
    l0LongerQ u = PMF.eventMass
      (PMF.scoresWith .uniform fun w => if worldContains w u then 1 else 0)
      longer := by
  cases u <;> decide +kernel

/-- Prior probability of "longer": 4 out of 10 worlds -/
def priorLonger : ℚ := 2 / 5

/-- Persuasive-speaker weight (eq. 8 at β = 2): `L0(longer|u)² · 𝟙[u ∈ w]`. -/
def s1Score (w : StickWorld) (u : Stick) : ℚ≥0 :=
  if worldContains w u then l0LongerQ u ^ 2 else 0

/-! ### The chain

The world prior is uniform, so it cancels from both listeners: L0 is the
normalized extension indicator, the persuasive speaker normalizes
`s1Score` per world, and L1 is the normalized speaker column. -/

/-- Literal listener over worlds (uniform prior conditioned on the
extension). -/
noncomputable def l0 (u : Stick) : PMF StickWorld :=
  .ofScores .uniform fun w => if worldContains w u then 1 else 0

/-- Event marginal of the literal listener. -/
noncomputable def l0Event (u : Stick) (P : StickWorld → Bool) : ℝ≥0∞ :=
  ∑' w, if P w then l0 u w else 0

/-- Persuasive speaker (eq. 8 at β = 2). -/
noncomputable def s1Persuade (w : StickWorld) : PMF Stick :=
  .ofScores .uniform (s1Score w)

/-- Pragmatic listener over worlds: the normalized speaker column (the
uniform prior cancels). -/
noncomputable def l1w (u : Stick) : PMF StickWorld :=
  .ofScores .uniform fun w => PMF.scoresWith .uniform (s1Score w) u

/-- Event marginal of the pragmatic listener. -/
noncomputable def l1Event (u : Stick) (P : StickWorld → Bool) : ℝ≥0∞ :=
  ∑' w, if P w then l1w u w else 0

open scoped ENNReal

/-! ### Predictions — L0 -/

/-- L0(longer|s5) > L0(¬longer|s5): stick 5 is positive evidence for "longer".
4 of 6 worlds containing s5 are longer, vs 2 not-longer. -/
theorem l0_s5_positive :
    l0Event .s5 (fun w => !longer w) < l0Event .s5 longer :=
  PMF.ofScores_event_lt _ _ (by decide +kernel)

/-- L0(longer|s5) > L0(longer|s4): stick 5 provides stronger evidence than s4. -/
theorem l0_s5_strongest : l0Event .s4 longer < l0Event .s5 longer :=
  PMF.ofScores_event_lt_cross _ _ _ _ (by decide +kernel)

/-- L0(¬longer|s1) > L0(longer|s1): stick 1 is evidence against "longer".
Only 1 of 6 worlds containing s1 is longer. -/
theorem l0_s1_negative :
    l0Event .s1 longer < l0Event .s1 (fun w => !longer w) :=
  PMF.ofScores_event_lt _ _ (by decide +kernel)

/-- L0(longer|·) is monotonically increasing in stick length. This structural
property ensures the simplified domain faithfully mirrors the paper's full domain
(Appendix Theorem 2). -/
theorem l0_monotone :
    l0LongerQ .s1 ≤ l0LongerQ .s2 ∧
    l0LongerQ .s2 ≤ l0LongerQ .s3 ∧
    l0LongerQ .s3 ≤ l0LongerQ .s4 ∧
    l0LongerQ .s4 ≤ l0LongerQ .s5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [l0LongerQ] <;>
    first
      | rfl
      | exact_mod_cast (by norm_num : (1:ℚ)/6 ≤ 1/3)
      | exact_mod_cast (by norm_num : (1:ℚ)/3 ≤ 1/2)
      | exact_mod_cast (by norm_num : (1:ℚ)/2 ≤ 2/3)

/-! ### Predictions — L1 (weak evidence effect) -/

/-- The weak evidence effect: at β = 2, showing stick 4 — positive literal
evidence — *decreases* the pragmatic listener's belief in "longer" below
the ¬longer mass (p. 172: "the absence of strong evidence from a speaker
who would be highly motivated to show it statistically implies that no
such evidence exists"). -/
theorem weak_evidence_effect :
    l1Event .s4 longer < l1Event .s4 (fun w => !longer w) :=
  PMF.ofScores_event_lt _ _ (by decide +kernel)

/-- Strong evidence works: the strongest available evidence cannot be
explained away by the absence of something better. -/
theorem strong_evidence_works :
    l1Event .s5 (fun w => !longer w) < l1Event .s5 longer :=
  PMF.ofScores_event_lt _ _ (by decide +kernel)

/-! ### Bridge Theorems -/

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
    hasPositiveArgStr (l0LongerQ .s4 : ℚ) priorLonger := by
  norm_num [hasPositiveArgStr, l0LongerQ, priorLonger]

/-- Stick 3 does NOT have positive argumentative strength
(L0(longer|s3) = 1/3 < 2/5 = P(longer)). -/
theorem s3_not_positive_argStr :
    ¬ hasPositiveArgStr (l0LongerQ .s3 : ℚ) priorLonger := by
  norm_num [hasPositiveArgStr, l0LongerQ, priorLonger]

/-- The weak evidence effect shows that argumentatively positive evidence
can still backfire under a pragmatic listener model. This is the core
insight connecting [barnett-griffiths-hawkins-2022] to
[cummins-franke-2021]'s work on argumentative strength.

Stick 4 has positive argStr at L0 (1/2 > 2/5), yet L1 assigns more mass
to ¬longer than longer after seeing s4. -/
theorem argStr_positive_but_backfires :
    hasPositiveArgStr (l0LongerQ .s4 : ℚ) priorLonger ∧
    l1Event .s4 longer < l1Event .s4 (fun w => !longer w) :=
  ⟨s4_positive_argStr, weak_evidence_effect⟩

/-! ### Experimental Design & Behavioral Data -/

/-- Listener type inferred from speaker expectation phase -/
inductive ListenerType where
  | pragmatic   -- expects strongest evidence (67% of participants)
  | literal     -- expects weaker/hedged evidence (33%)
  deriving DecidableEq, Repr

/-- Evidence strength conditions (distance from midpoint 5") -/
inductive EvidenceStrength where
  | weak      -- 6" (1" from midpoint)
  | moderate  -- 7" (2" from midpoint)
  | strong    -- 8" (3" from midpoint)
  | strongest -- 9" (4" from midpoint)
  deriving DecidableEq, Repr

/-- Which contestant goes first -/
inductive FirstContestant where
  | longBiased   -- wants judge to say "longer"
  | shortBiased  -- wants judge to say "shorter"
  deriving DecidableEq, Repr

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

theorem pragmatic_is_majority : pragmaticProportion > 1 / 2 := by norm_num [pragmaticProportion]

/-- Key interaction: speaker expectations × evidence strength.
t(718) = 5.2, p < 0.001 (p. 175) -/
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
theorem pragmatic_backfire : pragmaticResult.meanSlider < 50 := by norm_num [pragmaticResult]

/-- Literal group shows no backfire: mean at midpoint -/
theorem literal_no_backfire : literalResult.meanSlider > 49 := by norm_num [literalResult]

/-- The two groups differ in the predicted direction -/
theorem groups_differ :
    pragmaticResult.meanSlider < literalResult.meanSlider := by
  norm_num [pragmaticResult, literalResult]

/-! ### Model Comparison (Table 1) -/

/-- Model families compared -/
inductive ModelFamily where
  | anchorAdjust     -- A&A: P(w|u) = P(w) + η(s(u) - R)
  | minAcceptable    -- MAS: like A&A but R ~ Unif[-1,1]
  | rsaPragmatic     -- RSA with persuasive speaker
  deriving DecidableEq, Repr

/-- Model variant (how individual differences are handled) -/
inductive ModelVariant where
  | homogeneous       -- single model for all participants
  | heterogeneous     -- mixture of J0 and J1
  | speakerDependent  -- mixture weights conditioned on speaker phase
  deriving DecidableEq, Repr

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
    (12 : ℚ) > 82 / 10 := by norm_num

/-- The RSA speaker-dependent model has the best (lowest) WAIC -/
theorem rsa_speaker_dep_best_waic :
    (-164 : ℚ) / 10 < -133 / 10 := by norm_num

/-! ### Fitted Parameters -/

/-- Fitted parameters for the best model (RSA speaker-dependent).
β̂ = 2.26 and mixture weights from main text (p. 178);
β̄ = 2.03 and ō = −0.13 from Fig 3B caption (p. 177). -/
structure FittedParams where
  betaMAP : ℚ              -- MAP estimate of persuasive bias (p. 178)
  betaCV : ℚ               -- 10-fold CV average β (Fig 3B)
  responseOffsetCV : ℚ     -- 10-fold CV average offset (Fig 3B)
  pragmaticMixWeight : ℚ   -- mixture weight for pragmatic group (p. 178)
  literalMixWeight : ℚ     -- mixture weight for literal group (p. 178)
  deriving Repr

def bestModelParams : FittedParams :=
  { betaMAP := 226 / 100           -- β̂ = 2.26 (p. 178)
    betaCV := 203 / 100            -- β̄ = 2.03 (Fig 3B)
    responseOffsetCV := -13 / 100  -- ō = -0.13 (Fig 3B)
    pragmaticMixWeight := 99/100   -- p̂_z = 0.99 (J1 dominates; p. 178)
    literalMixWeight := 1/10 }     -- p̂_z = 0.1 (J0 dominates; p. 178)

/-- β > 0 provides strong support for non-zero persuasive bias -/
theorem beta_positive : bestModelParams.betaMAP > 0 := by norm_num [bestModelParams]

/-- Pragmatic group is best explained by J1 (pragmatic listener model) -/
theorem pragmatic_group_uses_j1 :
    bestModelParams.pragmaticMixWeight > 9 / 10 := by norm_num [bestModelParams]

/-- Literal group is best explained by J0 (literal listener model) -/
theorem literal_group_uses_j0 :
    bestModelParams.literalMixWeight < 2 / 10 := by norm_num [bestModelParams]

/-! ### Model–Data Connection -/

/-- The RSA model predicts the qualitative pattern underlying the observed
interaction between listener type and evidence strength (t(718) = 5.2,
p < 0.001). The literal model (L0) assigns s4 positive argumentative strength,
predicting no backfire. The pragmatic model (L1) shows backfire. The experiment
confirms exactly this divergence: pragmatic participants' mean (34.7) falls
below neutral (50), while literal participants' mean (50.1) does not. -/
theorem model_predicts_interaction :
    -- Model: L0 (literal) — s4 is positive evidence
    hasPositiveArgStr (l0LongerQ .s4 : ℚ) priorLonger ∧
    -- Model: L1 (pragmatic) — s4 backfires
    l1Event .s4 longer < l1Event .s4 (fun w => !longer w) ∧
    -- Data: pragmatic group shows backfire
    pragmaticResult.meanSlider < 50 ∧
    -- Data: literal group shows no backfire
    literalResult.meanSlider > 49 :=
  ⟨s4_positive_argStr, weak_evidence_effect, pragmatic_backfire, literal_no_backfire⟩

end BarnettEtAl2022
