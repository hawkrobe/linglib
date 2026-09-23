module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Linglib.Semantics.Causation.SEM.Basic
public import Linglib.Semantics.Causation.SEM.Bool
public import Linglib.Semantics.Causation.SEM.Deterministic

/-!
# Counterfactuals in structural equation models

The interventionist predicates over the eager development of a `SEM V α`, with `BoolSEM` forms
for binary models. The strict development and the causal entailment and necessity of
[nadathur-2023-implicatives] are in `SEM/Entailment.lean`.

- **`causallySufficient M s cause xC effect xE`**: setting `cause` to `xC` in `s` develops
  `effect` to `xE`, the bare sufficiency clause of [nadathur-lauer-2020]'s Definition 23.
- **`manipulates`**: Woodward's criterion, the cause's value makes a difference to the effect's.
- **`cfSeed`, `counterfactual`**: the rewind–revise–regenerate counterfactual of
  [lassiter-2017-probabilistic-language].
- **`WhetherCause`**: [beller-gerstenberg-2025]'s whether-causation, deterministic case.
- **`probSufficiency`**: [pearl-2019]'s probability of sufficiency, over a measure on
  background outcomes.

In a finite model each predicate is decided through the fuel form of the development
(`developDet_eq_fuel`).

## References

* [nadathur-lauer-2020]
* [lassiter-2017-probabilistic-language]
* [beller-gerstenberg-2025]
* [pearl-2019]
* [cao-white-lassiter-2025]
-/

@[expose] public section

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}
variable [Fintype V] [DecidableEq V] [DecidableValuation α]

/-! ### Polymorphic counterfactual predicates -/

/-- **Causal sufficiency**: setting `cause` to `xC` makes the eager-total development give
`effect` the value `xE`. This is the bare sufficiency clause of [nadathur-lauer-2020]'s
Definition 23; `Sufficiency.makeSem` states the whole definition, with its non-inevitability
clause, over the strict development. -/
def causallySufficient (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) : Prop :=
  (M.developDet (s.extend cause xC)).hasValue effect xE

instance (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallySufficient M s cause xC effect xE) :=
  inferInstanceAs (Decidable ((M.developDet _).hasValue _ _))

/-! ### Basic API lemmas (polymorphic) -/

omit [Fintype V] [DecidableValuation α] in
/-- `causallySufficient` unfolds to the development of the extended valuation. -/
theorem causallySufficient_iff (M : SEM V α)
    [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    causallySufficient M s cause xC effect xE ↔
      (M.developDet (s.extend cause xC)).hasValue effect xE := Iff.rfl

/-- **Interventionist manipulation** (Woodward's criterion): cause's value
    affects effect's value under `developDet`. Defined via `extend` rather
    than `intervene`: on an undetermined cause they agree
    (`developDet_intervene_eq_developDet_extend`). -/
def manipulates (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) : Prop :=
  (M.developDet (s.extend cause xC1)).get effect ≠
  (M.developDet (s.extend cause xC2)).get effect

instance (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) :
    Decidable (manipulates M s cause xC1 xC2 effect) :=
  decidable_of_iff
    (developDetVtxFuel M ((s.extend cause xC1).or M.rootDefaults) (Fintype.card V) effect ≠
      developDetVtxFuel M ((s.extend cause xC2).or M.rootDefaults) (Fintype.card V) effect)
    (by rw [manipulates, developDet_eq_fuel, developDet_eq_fuel]; rfl)

/-! ### Counterfactuals

A counterfactual is computed by the rewind–revise–regenerate procedure of
[lassiter-2017-probabilistic-language]: the antecedent is set, its descendants are left
undetermined to be regenerated, and the observed values of every causally independent vertex are
kept (`cfSeed`). With deterministic equations the counterfactual outcome is the development of
this seed (`counterfactual`). Morgenbesser's coin (bet → win ← heads, observed a losing bet on
heads) comes out as it should: the seed keeps heads and drops win, so had the bet been placed, it
would have won.

Uncertainty about the background enters as in Pearl's structural models, as a probability on
exogenous settings, here a measure `μ` on outcomes `ω` each of which settles a background
valuation `u ω` that fills in what the seed leaves open (`probSufficiency`). -/

omit [DecidableValuation α] in
/-- **Counterfactual seed** ([lassiter-2017-probabilistic-language]): `antecedent := xAnt`, the
descendants of the antecedent undetermined, and every other vertex as observed. -/
def cfSeed (M : SEM V α) (observed : Valuation α) (antecedent : V) (xAnt : α antecedent) :
    Valuation α := fun v =>
  if h : v = antecedent then some (h ▸ xAnt)
  else if M.graph.IsStrictAncestor antecedent v then none
  else observed.get v

omit [DecidableValuation α] in
/-- With nothing observed, the counterfactual seed only sets the antecedent. -/
theorem cfSeed_empty (M : SEM V α) (antecedent : V) (xAnt : α antecedent) :
    cfSeed M Valuation.empty antecedent xAnt =
      (Valuation.empty (α := α)).extend antecedent xAnt := by
  funext v
  by_cases h : v = antecedent
  · subst h; simp [cfSeed, Valuation.extend]
  · simp [cfSeed, Valuation.extend, Valuation.empty, h]

omit [DecidableValuation α] in
/-- The counterfactual outcome: the development of the counterfactual seed. -/
noncomputable def counterfactual (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAnt : α antecedent) : Valuation α :=
  M.developDet (cfSeed M observed antecedent xAnt)

omit [DecidableValuation α] in
/-- **Whether-causation** in a deterministic model, the {0,1} case of [beller-gerstenberg-2025]'s
W (their equation 1): had the antecedent been `xAlt`, the effect would not have had its actual
value `xE`. Their sufficient-causation S (equation 3) is whether-causation evaluated at the
valuation with the alternative causes removed. -/
def WhetherCause (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAlt : α antecedent)
    (effect : V) (xE : α effect) : Prop :=
  ¬ (counterfactual M observed antecedent xAlt).hasValue effect xE

instance (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAlt : α antecedent) (effect : V) (xE : α effect) :
    Decidable (WhetherCause M observed antecedent xAlt effect xE) :=
  inferInstanceAs (Decidable (¬ (M.developDet _).hasValue _ _))

omit [DecidableValuation α] in
/-- **Probability of sufficiency** ([pearl-2019]), the SUF measure of [cao-white-lassiter-2025]:
the probability, over outcomes `ω` of the background, that intervening `cause := xC` against the
factual context `observed` yields `effect = xE`. The background valuation `u ω` settles what the
counterfactual seed leaves open; observed vertices causally independent of the cause are kept
rather than resampled, the oxygen-versus-match contrast [pearl-2019] uses to motivate the
measure. -/
noncomputable def probSufficiency {Ω : Type*} [MeasurableSpace Ω] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] (μ : MeasureTheory.Measure Ω)
    (u : Ω → Valuation α) (observed : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) : ENNReal :=
  μ {ω | (M.developDet ((cfSeed M observed cause xC).or (u ω))).hasValue effect xE}

/-- With a certain background the probability of sufficiency is the {0,1} indicator of the
counterfactual outcome. -/
theorem probSufficiency_dirac {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] (ω : Ω)
    (u : Ω → Valuation α) (observed : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) :
    probSufficiency M (MeasureTheory.Measure.dirac ω) u observed cause xC effect xE =
      if (M.developDet ((cfSeed M observed cause xC).or (u ω))).hasValue effect xE then 1
        else 0 := by
  classical
  simp [probSufficiency, MeasureTheory.Measure.dirac_apply, Set.indicator_apply]

end Causation.SEM

/-! ### BoolSEM specializations (legacy SBH-style binary semantics) -/

namespace Causation.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Causation (SEM Valuation BoolSEM)
open Causation.SEM (causallySufficient)

/-- `BoolSEM`-flavored `causallySufficient`: setting `cause = true` develops
    `effect = true`. Matches old `Causation.causallySufficient` semantics. -/
abbrev causallySufficient (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.causallySufficient M s cause true effect true

/-- `BoolSEM`-flavored `manipulates`: cause's value (true vs false) flips
    effect's value under `developDet`. -/
abbrev manipulates (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.manipulates M s cause true false effect

/-- `BoolSEM`-flavored `probSufficiency`: the probability that intervening `cause := true`
    yields `effect = true`. -/
noncomputable abbrev probSufficiency {Ω : Type*} [MeasurableSpace Ω] (M : BoolSEM V)
    [CausalGraph.IsDAG M.graph] (μ : MeasureTheory.Measure Ω)
    (u : Ω → Valuation (fun _ : V => Bool)) (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  SEM.probSufficiency M μ u s cause true effect true

/-- **Direct causal connection**: `cause` is a parent of `effect` in
    the SEM's graph. Pure structural predicate (no `developDet`); fully
    decidable structurally via `Finset.decidableMem`. -/
def hasDirectLaw (M : BoolSEM V) (cause effect : V) : Prop :=
  cause ∈ M.graph.parents effect

instance (M : BoolSEM V) (cause effect : V) :
    Decidable (hasDirectLaw M cause effect) :=
  inferInstanceAs (Decidable (cause ∈ M.graph.parents effect))

end Causation.BoolSEM
