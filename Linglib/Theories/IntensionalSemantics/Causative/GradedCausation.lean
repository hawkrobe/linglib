/-
# Graded Causative Verb Semantics (Cao, White & Lassiter 2025)

Causative verbs *cause*, *make*, and *force* encode not just sufficiency
or necessity but a **unique blend of three graded measures**:

| Measure | Definition | Source |
|---------|-----------|--------|
| SUF | Probability of sufficiency | Pearl (2019) |
| INT | Degree of intention | Halpern & Kleiman-Weiner (2018) |
| ALT | Number of causee alternatives | Frankfurt (1969) |

## Key Finding

No single measure determines verb choice. Each verb has a unique
**interaction profile** (Table 1):

| Interaction | *caused* | *made* | *forced* |
|---|---|---|---|
| SUF×INT | - | **+** | - |
| SUF×ALT | + | + | + |
| INT×ALT | + | + | + |
| SUF×INT×ALT | - | - | - |

Notably, *make* uniquely has a reliable SUF×INT interaction, which
distinguishes it from both *cause* and *force*.

## Bridges to Existing Infrastructure

1. `causallySufficient` (Nadathur & Lauer) = deterministic limit of SUF
2. `CoerciveImplication.ActionType` = categorical limit of ALT
3. `CausativeBuilder` = binary coarsening of the graded model

## References

- Cao, A., White, A. S. & Lassiter, D. (2025). Cause, make, and force
  as graded causatives. Proceedings of ELM 3, 88-103.
- Pearl, J. (2019). Sufficient causes: On oxygen, matches, and fires.
  Journal of Causal Inference 7(2).
- Halpern, J. Y. & Kleiman-Weiner, M. (2018). Towards formal definitions
  of blameworthiness, intention, and moral responsibility.
- Frankfurt, H. G. (1969). Alternate possibilities and moral responsibility.
-/

import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency
import Linglib.Theories.IntensionalSemantics.Causative.Necessity
import Linglib.Theories.IntensionalSemantics.Causative.CoerciveImplication
import Linglib.Theories.IntensionalSemantics.Causative.Builder

namespace CaoWhiteLassiter2025

open Core.Causation
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity
open NadathurLauer2020.CoerciveImplication (ActionType)
open NadathurLauer2020.Builder (CausativeBuilder)

/-! ## The Three Measures (§2.2-2.4)

All three are defined within structural causal models (Pearl 2009).
In the general case they are continuous ∈ [0,1] (or ℕ for ALT).
Our deterministic `CausalDynamics` yields the boundary cases. -/

/-- The three causal measures that jointly predict causative verb acceptability.

- `suf`: Probability of sufficiency (Pearl 2019). Continuous [0,1].
  In the deterministic limit, collapses to `causallySufficient`.
- `int`: Degree of intention (Halpern & Kleiman-Weiner 2018). Continuous [0,1].
  How much the causer intended the outcome relative to alternatives.
- `alt`: Number of alternative actions available to the causee. ℕ.
  Fewer alternatives → stronger causal influence. -/
structure CausalMeasures where
  suf : ℚ
  int : ℚ
  alt : ℕ
  deriving Repr, DecidableEq, BEq

/-! ## Deterministic SUF

When the causal model is deterministic (as in `CausalDynamics`),
SUF collapses to a binary value matching `causallySufficient`. -/

/-- Compute SUF from a deterministic causal model.

In a deterministic model, SUF is either 0 or 1:
- 1 when the cause guarantees the effect (= `causallySufficient`)
- 0 otherwise -/
def deterministicSuf (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : ℚ :=
  if causallySufficient dyn background cause effect then 1 else 0

/-- Deterministic SUF = 1 iff binary `causallySufficient` holds.

This is the grounding theorem connecting Cao et al.'s probabilistic
SUF to Nadathur & Lauer's structural sufficiency. -/
theorem deterministicSuf_iff_sufficient (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) :
    (deterministicSuf dyn bg c e = 1) ↔ (causallySufficient dyn bg c e = true) := by
  simp only [deterministicSuf]
  constructor
  · intro h; split_ifs at h <;> simp_all
  · intro h; simp [h]

/-- Deterministic SUF = 0 iff binary `causallySufficient` fails. -/
theorem deterministicSuf_zero_iff_not_sufficient (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) :
    (deterministicSuf dyn bg c e = 0) ↔ (causallySufficient dyn bg c e = false) := by
  simp only [deterministicSuf]
  constructor
  · intro h; split_ifs at h <;> simp_all
  · intro h; simp [h]

/-! ## ALT → ActionType Bridge

Cao et al.'s continuous ALT measure generalizes the binary
Volitional/NonVolitional distinction in `CoerciveImplication`. -/

/-- Map ALT count to the categorical ActionType from CoerciveImplication.

- ALT = 0: causee had no choice → NonVolitional (forced action)
- ALT > 0: causee could have done otherwise → Volitional

This connects Cao et al.'s graded ALT to Nadathur & Lauer's
binary volitionality, used in the coercive implication analysis. -/
def altToActionType (alt : ℕ) : ActionType :=
  if alt > 0 then .Volitional else .NonVolitional

theorem alt_zero_nonvolitional : altToActionType 0 = .NonVolitional := rfl

theorem alt_positive_volitional (n : ℕ) (h : n > 0) :
    altToActionType n = .Volitional := by
  simp [altToActionType, h]

/-! ## Interaction Profiles (Table 1)

The core empirical finding: each verb has a unique set of
reliable interaction terms among SUF, INT, and ALT. -/

/-- Two-way and three-way interaction terms from the regression model.

These correspond to the product terms in the Bayesian regression
(Model I, Table 2). An interaction is "reliable" when its 95%
credible interval excludes 0. -/
inductive InteractionTerm where
  | sufInt      -- SUFresidALT × INT
  | sufAlt      -- SUFresidALT × ALT
  | intAlt      -- INT × ALT
  | sufIntAlt   -- SUFresidALT × INT × ALT (three-way)
  deriving DecidableEq, Repr, BEq

/-- A verb's interaction profile: which interaction terms reliably
predict its acceptability.

Each verb has a unique combination, supporting the claim that
causative verb semantics is multidimensional. -/
structure InteractionProfile where
  verb : String
  reliablePositive : List InteractionTerm
  reliableNegative : List InteractionTerm
  deriving Repr

/-- *caused*: SUF×ALT (+), INT×ALT (+), SUF×INT×ALT (-).
No reliable SUF×INT interaction. -/
def causeProfile : InteractionProfile :=
  { verb := "caused"
  , reliablePositive := [.sufAlt, .intAlt]
  , reliableNegative := [.sufIntAlt] }

/-- *made*: SUF×INT (+), SUF×ALT (+), INT×ALT (+), SUF×INT×ALT (-).
Uniquely has the SUF×INT interaction. -/
def makeProfile : InteractionProfile :=
  { verb := "made"
  , reliablePositive := [.sufInt, .sufAlt, .intAlt]
  , reliableNegative := [.sufIntAlt] }

/-- *forced*: SUF×ALT (+), INT×ALT (+), SUF×INT×ALT (-).
Same shape as *caused* but with different main effect intercepts. -/
def forceProfile : InteractionProfile :=
  { verb := "forced"
  , reliablePositive := [.sufAlt, .intAlt]
  , reliableNegative := [.sufIntAlt] }

/-- *make* uniquely has a reliable SUF×INT interaction.

This is the key finding distinguishing *make* from both *cause*
and *force*. It means *make*'s acceptability is sensitive to the
joint contribution of sufficiency and intention in a way the
other verbs are not. -/
theorem make_has_unique_sufInt :
    makeProfile.reliablePositive.contains .sufInt = true ∧
    causeProfile.reliablePositive.contains .sufInt = false ∧
    forceProfile.reliablePositive.contains .sufInt = false ∧
    causeProfile.reliableNegative.contains .sufInt = false ∧
    forceProfile.reliableNegative.contains .sufInt = false := by native_decide

/-- All three verbs share the SUF×ALT and INT×ALT interactions.
This reflects the common causal core. -/
theorem shared_interactions :
    causeProfile.reliablePositive.contains .sufAlt = true ∧
    makeProfile.reliablePositive.contains .sufAlt = true ∧
    forceProfile.reliablePositive.contains .sufAlt = true ∧
    causeProfile.reliablePositive.contains .intAlt = true ∧
    makeProfile.reliablePositive.contains .intAlt = true ∧
    forceProfile.reliablePositive.contains .intAlt = true := by native_decide

/-! ## Bridge to CausativeBuilder

The force-dynamic builder (Wolff 2003 / Talmy 1988) provides a finer
categorization than sufficiency/necessity alone. The graded model
reveals that verbs with different builders (e.g., `.make` and `.force`)
can still differ in their full semantics even when they share the
same N&L truth conditions. -/

/-- *make* and *force* now have different `CausativeBuilder`s (`.make` vs
`.force`) but both assert sufficiency, and have different interaction
profiles.

This demonstrates that the graded model provides information beyond
even the fine-grained force-dynamic builder: *make* has a SUF×INT
sensitivity that *force* lacks. -/
theorem make_force_both_assert_sufficiency_different_profiles :
    -- Both assert sufficiency (derived from builder)
    CausativeBuilder.make.assertsSufficiency = true ∧
    CausativeBuilder.force.assertsSufficiency = true ∧
    -- Different reliable interactions
    (makeProfile.reliablePositive ≠ forceProfile.reliablePositive) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The graded model subsumes the binary model.

In the deterministic limit (SUF ∈ {0,1}, no probabilistic INT),
the graded verb selection reduces to the binary
sufficiency/necessity distinction of `CausativeBuilder`. -/
theorem graded_subsumes_binary (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) :
    -- When deterministic SUF = 1, the builder's `makeSem` agrees
    deterministicSuf dyn bg c e = 1 →
    CausativeBuilder.make.toSemantics dyn bg c e = true := by
  intro h
  rw [deterministicSuf_iff_sufficient] at h
  simp [CausativeBuilder.toSemantics, makeSem, h]

/-! ## Main Effects (Model I, Table 2)

The regression coefficients for the main effects, showing the
direction and relative magnitude of each measure's contribution. -/

/-- Main effect coefficients from Model I (Table 2).

All three main effects are reliable (95% CI excludes 0):
- SUFresidALT: +1.19 (more sufficiency → more acceptable)
- INT: +0.54 (more intention → more acceptable)
- ALT: -0.82 (more alternatives → less acceptable)

Note the sign of ALT: more alternatives for the causee means
weaker causal influence, hence lower acceptability for all verbs. -/
structure MainEffects where
  sufResidAlt : ℚ  -- Residualized sufficiency
  int : ℚ          -- Intention
  alt : ℚ          -- Alternatives (negative = fewer alternatives → more acceptable)
  deriving Repr

def modelIMainEffects : MainEffects :=
  { sufResidAlt := 119/100  -- +1.19
  , int := 54/100           -- +0.54
  , alt := -82/100 }        -- -0.82

/-- SUF has the largest main effect, consistent with Nadathur & Lauer's
emphasis on sufficiency as the core semantic content. -/
theorem suf_largest_main_effect :
    modelIMainEffects.sufResidAlt > modelIMainEffects.int ∧
    modelIMainEffects.sufResidAlt > -modelIMainEffects.alt := by
  simp [modelIMainEffects]; norm_num

/-- ALT is negative: more alternatives → less acceptable.
This is expected since fewer alternatives = stronger causal influence. -/
theorem alt_negative_effect :
    modelIMainEffects.alt < 0 := by
  simp [modelIMainEffects]; norm_num

end CaoWhiteLassiter2025
