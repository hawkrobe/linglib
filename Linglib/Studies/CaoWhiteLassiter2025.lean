import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Linglib.Semantics.Causation.Interpretation
import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Cao, White & Lassiter 2025: graded causative verb semantics
[cao-white-lassiter-2025]

*Cause*, *make*, and *force* are graded causatives: acceptability tracks
three causal-model measures rather than a categorical sufficiency or
necessity condition — SUF, Pearl's probability of sufficiency
([pearl-2019], `Causation.SEM.probSufficiency`); INT, the causer's degree
of intention (after [halpern-kleiman-weiner-2018], normalized to [0,1]);
and ALT, the number of alternative actions available to the causee.

## Main results

- `interactionProfile`: the reliable interaction terms of each verb's
  per-verb regression model. Each tested verb's profile is distinct
  (`profiles_pairwise_distinct` — the paper's headline), and the three-way
  SUF×INT×ALT term is reliably negative for all three
  (`shared_negative_sufIntAlt`).
- `probSufficiency_empty_eq_deterministicSuf`: at the empty context,
  Pearl's counterfactual SUF collapses to [nadathur-lauer-2020]'s
  categorical sufficiency (their definition (23), `deterministicSuf`) —
  "interventional = counterfactual at a vacuous context" as a theorem.
- `make_force_same_semantics_different_profiles`: the force-dynamic
  dispatch (`Causative.toSemantics`) assigns *make* and *force* literally
  identical truth conditions, yet their graded interaction profiles
  differ — the graded data cut where the categorical semantics cannot.
- `ProbabilisticExample`: a Bernoulli-mechanism SEM witnessing that
  `probSufficiency` requires no determinism.

In the full regression (model I) *made* uniquely carries a reliable
positive SUF×INT interaction (0.45, CI [0.02, 0.87]); no verb's SUF×INT
is reliable in the per-verb models. Main effects (model I): SUF
residualized on ALT +1.19, INT +0.54, ALT −0.82 (SUF and ALT
anticorrelate at −0.81, hence the residualization).
-/

namespace CaoWhiteLassiter2025

open Causation (BoolSEM CausalGraph Valuation Mechanism SEM DecidableValuation)
open Causation.Mechanism (const)
open Causation.SEM (probSufficiency probSufficiency_eq_indicator_of_deterministic cfSeed
  cfSeed_empty)
open Features

/-! ### Deterministic limit

In the deterministic limit, SUF collapses to a {0,1} indicator
(`Causation.SEM.probSufficiency_eq_indicator_of_deterministic`). At the
vacuous (empty) context this is exactly [nadathur-lauer-2020]'s causal
sufficiency (their definition (23)): with nothing observed, Pearl's
counterfactual degenerates to the bare interventional development of
`cause := true`. -/

/-- Deterministic SUF as a {0,1} indicator over a `BoolSEM`:
    [nadathur-lauer-2020]'s causal sufficiency (their definition (23)),
    `causallySufficient`. -/
noncomputable def deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Causation.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  if Causation.BoolSEM.causallySufficient M background cause effect then 1 else 0

/-- **Grounding theorem**: at the empty context (vacuous abduction), the
    counterfactual `probSufficiency` reduces to the deterministic {0,1}
    indicator `deterministicSuf` — i.e. to [nadathur-lauer-2020]'s causal
    sufficiency. Makes "interventional = counterfactual at a vacuous
    context" a theorem rather than a conflation. -/
theorem probSufficiency_empty_eq_deterministicSuf {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [Causation.SEM.IsDeterministic M] (c e : V) :
    probSufficiency M Valuation.empty c true e true
      = deterministicSuf M Valuation.empty c e := by
  rw [probSufficiency_eq_indicator_of_deterministic, cfSeed_empty]
  unfold deterministicSuf Causation.BoolSEM.causallySufficient
    Causation.SEM.causallySufficient Causation.SEM.developsToValue
  by_cases h :
      (M.developDet ((Valuation.empty (α := fun _ : V => Bool)).extend c true)).hasValue e true <;>
    simp [h]

/-! ### Interaction profiles

The core empirical finding: no single measure determines verb choice, and
each verb has a unique set of reliable interaction terms among SUF, INT,
and ALT in its per-verb regression model. Only the reliable terms
(credible interval excluding 0) are encoded; the paper's summary table
also reports unreliable trends, which are not data. -/

/-- Two-way and three-way interaction terms among the SUF, INT, and ALT
    predictors. -/
inductive InteractionTerm where
  | sufInt
  | sufAlt
  | intAlt
  | sufIntAlt
  deriving DecidableEq, Repr

/-- A verb's interaction profile: the interaction terms that reliably
    predict its acceptability, by sign. -/
structure InteractionProfile where
  /-- Terms with a reliably positive coefficient. -/
  reliablePositive : Finset InteractionTerm
  /-- Terms with a reliably negative coefficient. -/
  reliableNegative : Finset InteractionTerm
  deriving DecidableEq

/-- Reliable interaction terms of each verb's per-verb model
    ([cao-white-lassiter-2025] models V–VII); `none` for causatives the
    paper did not test. -/
def interactionProfile : Causative → Option InteractionProfile
  | .cause => some ⟨{.sufAlt, .intAlt}, {.sufIntAlt}⟩
  | .make => some ⟨{.sufAlt}, {.sufIntAlt}⟩
  | .force => some ⟨∅, {.sufIntAlt}⟩
  | .enable | .prevent => none

/-- The three-way SUF×INT×ALT interaction is reliably negative for every
    verb tested: high values on all three measures together *depress*
    acceptability. -/
theorem shared_negative_sufIntAlt :
    ∀ v ∈ [Causative.cause, .make, .force], ∀ p ∈ interactionProfile v,
      InteractionTerm.sufIntAlt ∈ p.reliableNegative := by decide

/-- Each tested verb has a distinct interaction profile — the paper's
    headline finding that no single measure (nor shared measure blend)
    determines causative verb choice. -/
theorem profiles_pairwise_distinct :
    interactionProfile .cause ≠ interactionProfile .make ∧
    interactionProfile .cause ≠ interactionProfile .force ∧
    interactionProfile .make ≠ interactionProfile .force := by decide

/-- The force-dynamic dispatch collapses *make* and *force* to literally
    identical truth conditions ([nadathur-lauer-2020] via
    `Causative.toSemantics`), but their graded interaction profiles
    differ — the graded measures cut where the categorical semantics
    cannot. -/
theorem make_force_same_semantics_different_profiles
    {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V] [DecidableValuation α]
    [∀ v, Fintype (α v)] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [Causation.SEM.IsDeterministic M] :
    Causative.toSemantics M .make = Causative.toSemantics M .force ∧
    interactionProfile .make ≠ interactionProfile .force :=
  ⟨rfl, by decide⟩

/-! ### Probabilistic example: genuinely fractional SUF

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
    cases v <;> simp [graph] at h
    subst h
    decide)

instance (p : ℝ≥0) (h : p ≤ 1) : CausalGraph.IsDAG (model p h).graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

/-- `probSufficiency` accepts this SEM despite it NOT being
    `IsDeterministic` — exactly the [cao-white-lassiter-2025]
    requirement that SUF be a real probability. -/
noncomputable example (p : ℝ≥0) (h : p ≤ 1) : ENNReal :=
  probSufficiency (model p h) Valuation.empty .cause true .effect true

end ProbabilisticExample

end CaoWhiteLassiter2025
