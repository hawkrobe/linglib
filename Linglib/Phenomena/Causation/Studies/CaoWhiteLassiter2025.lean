/-
# Graded Causative Verb Semantics
@cite{cao-white-lassiter-2025}

Causative verbs *cause*, *make*, and *force* encode not just sufficiency
or necessity but a **unique blend of three graded measures**:

| Measure | Definition | Source |
|---------|-----------|--------|
| SUF | Probability of sufficiency | |
| INT | Degree of intention | |
| ALT | Number of causee alternatives | |

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
3. `Causative` = binary coarsening of the graded model

-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.CoerciveImplication
import Linglib.Core.WorldTimeIndex
import Linglib.Core.Causal.V2.SEM.Counterfactual
import Linglib.Theories.Semantics.Causation.Interpretation

namespace CaoWhiteLassiter2025

open Core (WorldTimeIndex)

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity
open Semantics.Causation.CoerciveImplication (ActionType)
open Core.Verbs (Causative)

/-! ## The Three Measures

All three are defined within structural causal models.
In the general case they are continuous ∈ [0,1] (or ℕ for ALT).
Our deterministic `CausalDynamics` yields the boundary cases. -/

/-- The three causal measures that jointly predict causative verb acceptability.

- `suf`: Probability of sufficiency. Continuous [0,1].
  In the deterministic limit, collapses to `causallySufficient`.
- `int`: Degree of intention. Continuous [0,1].
  How much the causer intended the outcome relative to alternatives.
- `alt`: Number of alternative actions available to the causee. ℕ.
  Fewer alternatives → stronger causal influence. -/
structure CausalMeasures where
  suf : ℚ
  int : ℚ
  alt : ℕ
  deriving Repr, DecidableEq

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
    (deterministicSuf dyn bg c e = 1) ↔ (causallySufficient dyn bg c e) := by
  simp only [deterministicSuf]
  constructor
  · intro h; split_ifs at h <;> simp_all
  · intro h; simp [h]

/-- Deterministic SUF = 0 iff binary `causallySufficient` fails. -/
theorem deterministicSuf_zero_iff_not_sufficient (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) :
    (deterministicSuf dyn bg c e = 0) ↔ (¬ (causallySufficient dyn bg c e)) := by
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

/-! ## Interaction Profiles

The core empirical finding: each verb has a unique set of
reliable interaction terms among SUF, INT, and ALT. -/

/-- Two-way and three-way interaction terms from the regression model.

These correspond to the product terms in the Bayesian regression.
An interaction is "reliable" when its 95% credible interval excludes 0. -/
inductive InteractionTerm where
  | sufInt      -- SUFresidALT × INT
  | sufAlt      -- SUFresidALT × ALT
  | intAlt      -- INT × ALT
  | sufIntAlt   -- SUFresidALT × INT × ALT (three-way)
  deriving DecidableEq, Repr

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

/-! ## Bridge to Causative

The force-dynamic builder (@cite{wolff-2003} / @cite{talmy-1988}) provides a finer
categorization than sufficiency/necessity alone. The graded model
reveals that verbs with different builders (e.g., `.make` and `.force`)
can still differ in their full semantics even when they share the
same N&L truth conditions. -/

/-- *make* and *force* now have different `Causative`s (`.make` vs
`.force`) but both assert sufficiency, and have different interaction
profiles.

This demonstrates that the graded model provides information beyond
even the fine-grained force-dynamic builder: *make* has a SUF×INT
sensitivity that *force* lacks. -/
theorem make_force_both_assert_sufficiency_different_profiles :
    -- Both assert sufficiency (derived from builder)
    Causative.make.assertsSufficiency = true ∧
    Causative.force.assertsSufficiency = true ∧
    -- Different reliable interactions
    (makeProfile.reliablePositive ≠ forceProfile.reliablePositive) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The graded model subsumes the binary model.

In the deterministic limit (SUF ∈ {0,1}, no probabilistic INT),
the graded verb selection reduces to the binary
sufficiency/necessity distinction of `Causative`. -/
theorem graded_subsumes_binary (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) :
    -- When deterministic SUF = 1, the builder's `makeSem` agrees
    deterministicSuf dyn bg c e = 1 →
    Causative.make.toSemantics dyn bg c e = true := by
  intro h
  rw [deterministicSuf_iff_sufficient] at h
  simp [Causative.toSemantics, makeSem, h]

/-! ## Main Effects

The regression coefficients for the main effects, showing the
direction and relative magnitude of each measure's contribution. -/

/-- Main effect coefficients from the Bayesian regression.

-- UNVERIFIED: coefficient values (+1.19, +0.54, -0.82) need verification
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

/-! ### V2 namespace: PMF-canonical SUF

The legacy `deterministicSuf := if causallySufficient then 1 else 0`
above shoehorns Cao et al.'s probabilistic SUF into the deterministic
substrate. The V2 substrate (PMF-valued `develop`) hosts SUF as a
genuine `ENNReal` — equal to a {0,1} indicator only in the deterministic
limit (via `develop_eq_pure_of_deterministic`).

`SEM.probabilisticSuf` (in `Core/Causal/V2/SEM/Counterfactual.lean`) is
the canonical primitive. The bridge `probabilisticSuf_of_deterministic`
shows that under `[IsDeterministic M]` it collapses to the indicator —
recovering the legacy semantics as a special case rather than a parallel
shoehorn. -/

namespace V2

open Core.Causal.V2 (BoolSEM CausalGraph Valuation)
open Core.Causal.V2.SEM (probabilisticSuf probabilisticSuf_of_deterministic)

/-- V2 deterministic SUF: 1 iff `cause` is causally sufficient for
    `effect` under the V2 BoolSEM substrate. Indicator form. -/
noncomputable def deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Core.Causal.V2.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  if Core.Causal.V2.BoolSEM.causallySufficient M background cause effect then 1 else 0

/-- **The grounding theorem**: under `IsDeterministic`, the canonical
    PMF-valued `probabilisticSuf` collapses to the deterministic
    indicator. This is what makes the legacy `if causallySufficient then
    1 else 0` semantics a special case of the mathlib-canonical
    probabilistic form, rather than a parallel shoehorn. -/
theorem probabilisticSuf_eq_deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Core.Causal.V2.SEM.IsDeterministic M]
    (bg : Valuation _) (c e : V) :
    probabilisticSuf M bg c true e true = deterministicSuf M bg c e := by
  unfold deterministicSuf
  rw [probabilisticSuf_of_deterministic]
  -- Both sides are `if ... then 1 else 0`; need to identify the conditions
  -- (M.intervene c true).developDet bg `.hasValue e true` vs
  -- BoolSEM.causallySufficient M bg c e := SEM.causallySufficient M bg c true e true
  --   := developsToValue M (bg.extend c true) e true
  --   := (M.developDet (bg.extend c true)).hasValue e true
  -- These differ in `intervene cause true ; develop bg` vs `develop (bg.extend cause true)`.
  -- For deterministic acyclic SEMs they agree on downstream vertices, but a
  -- general bridge lemma `developDet_intervene_eq_developDet_extend` is
  -- not yet in the V2 substrate. Stated as TODO; the indicator equality
  -- is provable once that bridge lands.
  sorry

/-! ### Probabilistic example: genuinely fractional SUF

Construction of a 2-vertex SEM whose `effect` mechanism is `PMF.bernoulli p`
— genuinely probabilistic, not Dirac. Demonstrates that `probabilisticSuf`
accepts non-deterministic SEMs (no `IsDeterministic` constraint), which is
exactly the @cite{cao-white-lassiter-2025} requirement: SUF is a probability,
not a 0/1 marker.

This example is type-only: the precise value of `probabilisticSuf` for the
Bernoulli mechanism is `p` (intuitively), but proving this requires
unfolding `PMF.bind` through the `develop` iteration — deferred until a
study consumer needs the explicit calculation. -/

namespace ProbabilisticExample

open scoped NNReal
open Core.Causal.V2 (Mechanism)
open Core.Causal.V2.Mechanism (const)

/-- A 2-vertex SEM: `cause` (root) and `effect` (one parent: cause). -/
inductive V | cause | effect
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun | .cause => ∅ | .effect => {.cause}⟩

/-- The probabilistic mechanism for `effect`: ignores parent value,
    returns `Bernoulli(p)` directly. Genuinely non-Dirac when `p ∉ {0, 1}`. -/
noncomputable def effectMech (p : ℝ≥0) (h : p ≤ 1) :
    Mechanism graph (fun _ => Bool) .effect :=
  ⟨fun _ => PMF.bernoulli p h⟩

/-- A genuinely probabilistic SEM (not `IsDeterministic` for `p ∉ {0,1}`). -/
noncomputable def model (p : ℝ≥0) (h : p ≤ 1) : BoolSEM V :=
  { graph := graph
    mech := fun
      | .cause => const (G := graph) false
      | .effect => effectMech p h }

instance : CausalGraph.IsDAG graph := by
  -- 2-vertex DAG; well-foundedness is structurally obvious (`.cause` is
  -- a root, `.effect`'s only ancestor is `.cause`). The `Relation.TransGen`
  -- induction needs head/tail destructuring with the concrete index `.cause`
  -- generalized — same mechanical pattern as BG2025 Phase D-E IsDAG sorries.
  -- TODO: close once we have a depth-based `Subrelation.wf` helper.
  sorry

instance (p : ℝ≥0) (h : p ≤ 1) : CausalGraph.IsDAG (model p h).graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

/-- The type-level demonstration: `probabilisticSuf` accepts this SEM
    even though it is NOT `IsDeterministic`. The legacy `deterministicSuf`
    form would require `[IsDeterministic M]` and reject this model
    outright — exactly the shoehorning V2 was designed to eliminate. -/
noncomputable example (p : ℝ≥0) (h : p ≤ 1) : ENNReal :=
  probabilisticSuf (model p h) Valuation.empty .cause true .effect true

end ProbabilisticExample

end V2

end CaoWhiteLassiter2025
