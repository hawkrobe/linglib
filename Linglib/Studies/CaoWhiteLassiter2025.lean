/-
# Graded Causative Verb Semantics
[cao-white-lassiter-2025]

Causative verbs *cause*, *make*, and *force* encode not just sufficiency
or necessity but a **unique blend of three graded measures**:

| Measure | Definition | Source |
|---------|-----------|--------|
| SUF | Probability of sufficiency | [pearl-2019] |
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

## SUF as Pearl's probability of sufficiency

SUF is Pearl's **probability of sufficiency** ([pearl-2019]): the
*counterfactual* probability that intervening to set the cause would
produce the effect, evaluated against a factual context in which the
cause took some other value and the effect did not already obtain. It is
a genuine probability (`ENNReal`-valued), not a 0/1 indicator.

Following [pearl-2019]'s three-step abduction–action–prediction, `SUF`
(`probSufficiency`) is built on the substrate's `counterfactualSimulate`
(`develop` of `cfSeed`): abduction preserves causally-independent
observations and regenerates descendants (the high-stability reduction,
[lassiter-2017-probabilistic-language], [lucas-kemp-2015]); action sets
the cause; prediction reads off the effect's probability via the canonical
`PMF.probOfSet`. This distinguishes SUF from plain interventional
probability `P(effect | do(cause))`: causally-independent parents of the
effect that were observed are *preserved* rather than re-sampled from
their priors — the oxygen-vs-match contrast [pearl-2019] uses to motivate
the measure.

In the deterministic limit `SUF` collapses to a {0,1} indicator
(`probSufficiency_of_deterministic`); at the vacuous (empty) context,
where abduction is trivial, it reduces to the [nadathur-lauer-2020]
Def-23 sufficiency predicate `causallySufficient`
(`probSufficiency_empty_eq_deterministicSuf`).

-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Linglib.Core.Probability.Finite
import Linglib.Semantics.Causation.CoerciveImplication
import Linglib.Semantics.Intensional.WorldTimeIndex
import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Semantics.Causation.Interpretation

namespace CaoWhiteLassiter2025

open Intensional (WorldTimeIndex)
open Causation (BoolSEM CausalGraph Valuation Mechanism SEM DecidableValuation)
open Causation.Mechanism (const)
open Causation.SEM (counterfactualSimulate counterfactualSimulate_eq_pure_of_deterministic cfSeed)
open Causation.CoerciveImplication (ActionType)
open Features (Causative)
open Features

/-! ## The Three Measures

All three are defined within structural causal models.
SUF is continuous ∈ [0,1], INT is continuous ∈ [0,1], ALT is ℕ. -/

/-- The three causal measures that jointly predict causative verb acceptability.

- `suf`: Probability of sufficiency ([pearl-2019]). Continuous [0,1].
  Computed via `probSufficiency` over a (possibly probabilistic) `SEM V α`.
- `int`: Degree of intention. Continuous [0,1].
  How much the causer intended the outcome relative to alternatives.
- `alt`: Number of alternative actions available to the causee. ℕ.
  Fewer alternatives → stronger causal influence. -/
structure CausalMeasures where
  suf : ℚ
  int : ℚ
  alt : ℕ
  deriving Repr, DecidableEq

/-! ## SUF: Pearl's probability of sufficiency

[pearl-2019]'s probability of sufficiency — the counterfactual probability
that intervening to set `cause := xC` produces `effect = xE`, against a
factual context `observed` (cause took some other value, effect did not
obtain). Built on the substrate's `counterfactualSimulate`
(Pearl 3-step abduction–action–prediction, via the high-stability
reduction in `cfSeed`) and the canonical `PMF.probOfSet`. -/

section PearlSufficiency

variable {V : Type*} {α : V → Type*}
  [Fintype V] [DecidableEq V] [DecidableValuation α]

/-- **Probability of sufficiency** ([pearl-2019]), the SUF measure of
    [cao-white-lassiter-2025]: the counterfactual probability that
    intervening `cause := xC` yields `effect = xE`, evaluated against the
    factual context `observed`.

    Pearl's three-step abduction–action–prediction, expressed via the
    substrate's `counterfactualSimulate` (`develop` of `cfSeed`): abduction
    preserves causally-independent observations and regenerates descendants
    (the high-stability reduction, [lassiter-2017-probabilistic-language],
    [lucas-kemp-2015]); action sets `cause := xC`; prediction reads off the
    probability of `effect = xE` via `PMF.probOfSet`.

    Distinct from plain interventional probability `P(effect | do(cause))`:
    causally-independent parents of `effect` recorded in `observed` are
    *preserved* rather than re-sampled — the oxygen-vs-match contrast
    [pearl-2019] uses to motivate the measure. -/
noncomputable def probSufficiency
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) : ENNReal :=
  (counterfactualSimulate M observed cause xC).probOfSet {v | v.hasValue effect xE}

/-- Under `IsDeterministic`, `probSufficiency` collapses to the {0,1}
    indicator of whether the counterfactual development hits `effect = xE`.
    Follows from `counterfactualSimulate_eq_pure_of_deterministic` plus
    `PMF.toOuterMeasure_pure_apply`. -/
theorem probSufficiency_of_deterministic
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [Causation.SEM.IsDeterministic M]
    (observed : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) :
    probSufficiency M observed cause xC effect xE =
      if (M.developDet (cfSeed M observed cause xC)).hasValue effect xE then 1 else 0 := by
  unfold probSufficiency
  rw [counterfactualSimulate_eq_pure_of_deterministic]
  simp only [PMF.probOfSet, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
  congr 1

omit [Fintype V] [DecidableValuation α] in
/-- At the empty (vacuous-abduction) context, `cfSeed` reduces to a plain
    `extend`: with nothing observed, abduction preserves nothing and the
    counterfactual seed merely sets the cause. -/
theorem cfSeed_empty (M : SEM V α) (cause : V) (xC : α cause) :
    cfSeed M Valuation.empty cause xC = (Valuation.empty (α := α)).extend cause xC := by
  funext v
  by_cases h : v = cause
  · subst h; simp [cfSeed, Valuation.extend]
  · simp [cfSeed, Valuation.extend, Valuation.empty, h]

end PearlSufficiency

/-! ## Deterministic limit

In the deterministic limit (every mechanism a Dirac), SUF collapses to a
{0,1} indicator. At the vacuous (empty) context this is exactly the
[nadathur-lauer-2020] Def-23 sufficiency predicate `causallySufficient` —
with nothing observed, Pearl's counterfactual degenerates to the bare
interventional development of `cause := true`. -/

/-- Deterministic SUF as a {0,1} indicator over a `BoolSEM`: the
    [nadathur-lauer-2020] Def-23 sufficiency predicate `causallySufficient`. -/
noncomputable def deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Causation.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  if Causation.BoolSEM.causallySufficient M background cause effect then 1 else 0

/-- **Grounding theorem**: at the empty context (vacuous abduction), the
    counterfactual `probSufficiency` reduces to the deterministic {0,1}
    indicator `deterministicSuf` — i.e. to [nadathur-lauer-2020]'s Def-23
    sufficiency. Makes "interventional = counterfactual at a vacuous
    context" a theorem rather than a conflation. -/
theorem probSufficiency_empty_eq_deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Causation.SEM.IsDeterministic M] (c e : V) :
    probSufficiency M Valuation.empty c true e true
      = deterministicSuf M Valuation.empty c e := by
  rw [probSufficiency_of_deterministic, cfSeed_empty]
  unfold deterministicSuf Causation.BoolSEM.causallySufficient
    Causation.SEM.causallySufficient Causation.SEM.developsToValue
  by_cases h : (M.developDet ((Valuation.empty (α := fun _ : V => Bool)).extend c true)).hasValue e true <;>
    simp [h]

/-! ## ALT → ActionType Bridge

Cao et al.'s continuous ALT measure generalizes the binary
Volitional/NonVolitional distinction in `CoerciveImplication`. -/

/-- Map ALT count to the categorical ActionType from CoerciveImplication.

- ALT = 0: causee had no choice → NonVolitional (forced action)
- ALT > 0: causee could have done otherwise → Volitional -/
def altToActionType (alt : ℕ) : ActionType :=
  if alt > 0 then .Volitional else .NonVolitional

theorem alt_zero_nonvolitional : altToActionType 0 = .NonVolitional := rfl

theorem alt_positive_volitional (n : ℕ) (h : n > 0) :
    altToActionType n = .Volitional := by
  simp [altToActionType, h]

/-! ## Interaction Profiles

The core empirical finding: each verb has a unique set of
reliable interaction terms among SUF, INT, and ALT. -/

/-- Two-way and three-way interaction terms from the regression model. -/
inductive InteractionTerm where
  | sufInt
  | sufAlt
  | intAlt
  | sufIntAlt
  deriving DecidableEq, Repr

/-- A verb's interaction profile: which interaction terms reliably
predict its acceptability. -/
structure InteractionProfile where
  verb : String
  reliablePositive : List InteractionTerm
  reliableNegative : List InteractionTerm
  deriving Repr

def causeProfile : InteractionProfile :=
  { verb := "caused"
  , reliablePositive := [.sufAlt, .intAlt]
  , reliableNegative := [.sufIntAlt] }

def makeProfile : InteractionProfile :=
  { verb := "made"
  , reliablePositive := [.sufInt, .sufAlt, .intAlt]
  , reliableNegative := [.sufIntAlt] }

def forceProfile : InteractionProfile :=
  { verb := "forced"
  , reliablePositive := [.sufAlt, .intAlt]
  , reliableNegative := [.sufIntAlt] }

/-- *make* uniquely has a reliable SUF×INT interaction. -/
theorem make_has_unique_sufInt :
    makeProfile.reliablePositive.contains .sufInt = true ∧
    causeProfile.reliablePositive.contains .sufInt = false ∧
    forceProfile.reliablePositive.contains .sufInt = false ∧
    causeProfile.reliableNegative.contains .sufInt = false ∧
    forceProfile.reliableNegative.contains .sufInt = false := by decide

/-- All three verbs share the SUF×ALT and INT×ALT interactions. -/
theorem shared_interactions :
    causeProfile.reliablePositive.contains .sufAlt = true ∧
    makeProfile.reliablePositive.contains .sufAlt = true ∧
    forceProfile.reliablePositive.contains .sufAlt = true ∧
    causeProfile.reliablePositive.contains .intAlt = true ∧
    makeProfile.reliablePositive.contains .intAlt = true ∧
    forceProfile.reliablePositive.contains .intAlt = true := by decide

/-- *make* and *force* both assert sufficiency at the enum level but have
    different interaction profiles. -/
theorem make_force_both_assert_sufficiency_different_profiles :
    Causative.make.assertsSufficiency = true ∧
    Causative.force.assertsSufficiency = true ∧
    (makeProfile.reliablePositive ≠ forceProfile.reliablePositive) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-! ## Main Effects

The regression coefficients for the main effects, showing the
direction and relative magnitude of each measure's contribution. -/

/-- Main effect coefficients from the Bayesian regression.

-- UNVERIFIED: coefficient values (+1.19, +0.54, -0.82) need verification -/
structure MainEffects where
  sufResidAlt : ℚ
  int : ℚ
  alt : ℚ
  deriving Repr

def modelIMainEffects : MainEffects :=
  { sufResidAlt := 119/100
  , int := 54/100
  , alt := -82/100 }

theorem suf_largest_main_effect :
    modelIMainEffects.sufResidAlt > modelIMainEffects.int ∧
    modelIMainEffects.sufResidAlt > -modelIMainEffects.alt := by
  simp [modelIMainEffects]; norm_num

theorem alt_negative_effect :
    modelIMainEffects.alt < 0 := by
  simp [modelIMainEffects]; norm_num

/-! ## Probabilistic example: genuinely fractional SUF

A 2-vertex SEM whose `effect` mechanism is `PMF.bernoulli p` —
genuinely probabilistic, not Dirac. Demonstrates that `probSufficiency`
accepts non-deterministic SEMs (no `IsDeterministic` constraint). -/

namespace ProbabilisticExample

open scoped NNReal

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

/-- Depth function for `V`: `cause` is a root, `effect` has depth 1. -/
def vDepth : V → ℕ
  | .cause => 0
  | .effect => 1

instance : CausalGraph.IsDAG graph :=
  CausalGraph.IsDAG.of_depth graph vDepth (by
    intro u v h
    cases v <;> simp [graph, CausalGraph.parents] at h <;>
      subst h <;> decide)

instance (p : ℝ≥0) (h : p ≤ 1) : CausalGraph.IsDAG (model p h).graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

/-- `probSufficiency` accepts this SEM despite it NOT being
    `IsDeterministic` — exactly the [cao-white-lassiter-2025]
    requirement that SUF be a real probability. -/
noncomputable example (p : ℝ≥0) (h : p ≤ 1) : ENNReal :=
  probSufficiency (model p h) Valuation.empty .cause true .effect true

end ProbabilisticExample

end CaoWhiteLassiter2025
