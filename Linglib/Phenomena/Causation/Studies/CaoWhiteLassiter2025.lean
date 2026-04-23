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

## SUF as a probability

The motivation for the V2 PMF substrate. SUF is a **probability** that
the cause is sufficient — `ENNReal`-valued via `SEM.probabilisticSuf`,
not a 0/1 indicator. The deterministic case is a special case via
`develop_eq_pure_of_deterministic`.

-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Linglib.Theories.Semantics.Causation.CoerciveImplication
import Linglib.Core.WorldTimeIndex
import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Theories.Semantics.Causation.Interpretation

namespace CaoWhiteLassiter2025

open Core (WorldTimeIndex)
open Core.Causal (BoolSEM CausalGraph Valuation Mechanism)
open Core.Causal.Mechanism (const)
open Core.Causal.SEM (probabilisticSuf probabilisticSuf_of_deterministic)
open Semantics.Causation.CoerciveImplication (ActionType)
open Core.Verbs (Causative)

/-! ## The Three Measures

All three are defined within structural causal models.
SUF is continuous ∈ [0,1], INT is continuous ∈ [0,1], ALT is ℕ. -/

/-- The three causal measures that jointly predict causative verb acceptability.

- `suf`: Probability of sufficiency. Continuous [0,1].
  Computed via `SEM.probabilisticSuf` over a (possibly probabilistic) `SEM V α`.
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

In the deterministic limit (every mechanism a Dirac), SUF collapses to
a {0,1} indicator. `probabilisticSuf_of_deterministic` is the bridge
that recovers this special case from the canonical PMF form. -/

/-- Deterministic SUF as a {0,1} indicator over a `BoolSEM` with
    `IsDeterministic`. -/
noncomputable def deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Core.Causal.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  if Core.Causal.BoolSEM.causallySufficient M background cause effect then 1 else 0

/-- **Grounding theorem**: under `IsDeterministic`, the canonical PMF-valued
    `probabilisticSuf` collapses to the deterministic {0,1} indicator.
    Recovers the legacy "shoehorned" SUF as a special case rather than
    a parallel definition. -/
theorem probabilisticSuf_eq_deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Core.Causal.SEM.IsDeterministic M]
    (bg : Valuation (fun _ : V => Bool)) (c e : V)
    (hc : bg.get c = none) :
    probabilisticSuf M bg c true e true = deterministicSuf M bg c e := by
  unfold deterministicSuf
  rw [probabilisticSuf_of_deterministic]
  rw [Core.Causal.SEM.developDet_intervene_eq_developDet_extend M bg c true hc]
  congr 1

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
genuinely probabilistic, not Dirac. Demonstrates that `probabilisticSuf`
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

/-- `probabilisticSuf` accepts this SEM despite it NOT being
    `IsDeterministic` — exactly the @cite{cao-white-lassiter-2025}
    requirement that SUF be a real probability. -/
noncomputable example (p : ℝ≥0) (h : p ≤ 1) : ENNReal :=
  probabilisticSuf (model p h) Valuation.empty .cause true .effect true

end ProbabilisticExample

end CaoWhiteLassiter2025
