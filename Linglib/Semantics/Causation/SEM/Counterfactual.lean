import Linglib.Core.Probability.Finite
import Linglib.Semantics.Causation.SEM.Basic
import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Deterministic

/-!
# SEM: Causal Counterfactual Predicates

Polymorphic counterfactual predicates over a `SEM V α`, plus `BoolSEM`-flavored
aliases for legacy SBH-style binary semantics.

- **`developsToValue M s v x`**: after developing `s`, vertex `v` has value `x`.
  Replaces the old `developsToTrue` (Bool-specialized) with a polymorphic version.

- **`causallySufficient M s cause xC effect xE`**: extending `s` with `xC` at
  `cause` then eager-totally developing produces `xE` at `effect` — the bare
  sufficiency clause over `developDetVtx`, kept for consumers that want plain
  development entailment (Glass, SBH, INUS, CC-selection).

- **`causallyEntails M s v x`**: [nadathur-2023-implicatives] Definition 5 —
  the strict T_D fixed point (`developDetVtx?`) assigns `x` to `v`. The
  paper-faithful predicates below are stated over this notion.

- **`isConsistentSuper M base s'`**: Definition 9b, "not the opposite" form.

- **`causallyNecessary M s cause xC effect xE`**: Definition 10b —
  preamble + achievability + no-alternative, with supersituations quantified
  over exogenous settlements (see `IsExogenousSettlement` for why the literal
  quantification is unfaithful to the paper's own verdicts).

`BoolSEM`-namespace aliases specialize the polymorphic predicates to
`α := fun _ => Bool` with `xC = true`, `xE = true` (legacy SBH semantics).

## Computability

The canonical predicates are noncomputable (`WellFounded.fix`); `Decidable`
instances on them are `Classical.dec` and do **not** support `decide`.
Concrete claims go through the fuel bridge instead: `causallyEntails_iff_fuel`
and `causallyNecessary_iff_fuel` rewrite to the kernel-reducible
`developDetVtxFuel` / `causallyNecessaryFuel` forms given a per-model
`CausalGraph.Ranking` (the same certificate that yields `IsDAG` via
`Ranking.isDAG`), after
which `decide` evaluates them — including the Def 10b supersituation
quantifiers, which range over the finite valuation space. Study idiom:

`theorem foo : makeSem M bg c true e true :=`
`  ⟨fun h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩`

with `entails_iff` a one-line per-model instantiation of
`causallyEntails_iff_fuel`.
-/

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}
variable [Fintype V] [DecidableEq V] [DecidableValuation α]

/-! ### Polymorphic counterfactual predicates -/

/-- After developing the SEM against `s`, vertex `v` has the value `x`.

    Polymorphic generalization of the old `developsToTrue` (which fixed
    `α := fun _ => Bool` and `x := true`). -/
def developsToValue (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) : Prop :=
  (M.developDet s).hasValue v x

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) :
    Decidable (developsToValue M s v x) :=
  Classical.dec _

/-- **Causal sufficiency**: forcing `cause` to `xC` makes `effect` developDet to `xE`.

    Polymorphic generalization of [nadathur-lauer-2020] Definition 23's
    sufficiency clause (the development of `s + (cause = xC)` fixes the
    effect); Def 23's non-inevitability precondition (clause a) is not
    yet represented — see the module TODO.
    The Bool case (`BoolSEM.causallySufficient`) recovers the legacy semantics
    "`cause = true` produces `effect = true`". -/
def causallySufficient (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) : Prop :=
  developsToValue M (s.extend cause xC) effect xE

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallySufficient M s cause xC effect xE) :=
  Classical.dec _

/-! ### Basic API lemmas (polymorphic) -/

omit [Fintype V] [DecidableEq V] [DecidableValuation α] in
/-- `developsToValue` unfolds to `(developDet M s).hasValue v x`. -/
theorem developsToValue_iff (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) :
    developsToValue M s v x ↔ (M.developDet s).hasValue v x := Iff.rfl

omit [Fintype V] [DecidableValuation α] in
/-- `causallySufficient` unfolds to `developsToValue` of the extended valuation. -/
theorem causallySufficient_iff (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    causallySufficient M s cause xC effect xE ↔
      developsToValue M (s.extend cause xC) effect xE := Iff.rfl

/-- **Interventionist manipulation** (Woodward's criterion): cause's value
    affects effect's value under `developDet`. Defined via `extend` rather
    than `intervene` because for deterministic acyclic SEMs they agree
    and `extend` doesn't require re-establishing `IsDeterministic` on the
    intervened SEM. -/
def manipulates (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) : Prop :=
  (M.developDet (s.extend cause xC1)).get effect ≠
  (M.developDet (s.extend cause xC2)).get effect

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) :
    Decidable (manipulates M s cause xC1 xC2 effect) :=
  Classical.dec _

/-! ### Unified counterfactual primitive (PMF-canonical) -/

/-! Pearl-style counterfactual simulation via Lassiter's RRR heuristic
    ([lassiter-2017-probabilistic-language]): "Rewind to the
    antecedent's causal layer, Revise the antecedent, selectively
    Regenerate descendants while preserving causally-independent
    observations." Subsumes:
    - [lewis-1973-causation] / [nadathur-lauer-2020] deterministic
      counterfactuals (Dirac specialization)
    - [beller-gerstenberg-2025] W/H/S aspects (graded probability)
    - [lassiter-2017-probabilistic-language] probabilistic counterfactuals
      with overt probability operators

    Key insight: under the high-stability assumption ([lucas-kemp-2015]),
    Pearl 3-step abduction reduces to "preserve causally-independent
    observations, regenerate descendants" — no explicit exogenous noise
    types needed. The existing `develop` PMF naturally produces the right
    distribution when fed the counterfactual seed valuation.

    Morgenbesser's coin example (discussed in
    [lassiter-2017-probabilistic-language]): bet → win ←
    heads. Observed `{bet:=false, win:=false, heads:=true}`. Counterfactual
    `bet := true`. Then `cfSeed = {bet:=true, heads:=true, win:=none}`
    (heads is causally independent so preserved; win is descendant of bet
    so regenerated). `develop` computes `win := bet ∧ heads = true`. The
    counterfactual probability of winning is 1, matching Lassiter's
    prediction (and contradicting "Rewind, Revise, Re-run" without
    selective regeneration). -/

omit [Fintype V] [DecidableValuation α] in
/-- **Counterfactual seed** ([lassiter-2017-probabilistic-language] RRR): the partial valuation that
    `counterfactualSimulate` feeds to `develop`. Sets `antecedent := xAnt`,
    leaves descendants of antecedent undetermined (to be regenerated),
    preserves `observed` values for causally-independent vertices. -/
noncomputable def cfSeed
    (M : SEM V α) (observed : Valuation α)
    (antecedent : V) (xAnt : α antecedent) : Valuation α := fun v =>
  if h : v = antecedent then some (h ▸ xAnt)
  else
    haveI : Decidable (M.graph.IsStrictAncestor antecedent v) := Classical.dec _
    if M.graph.IsStrictAncestor antecedent v then none
    else observed.get v

omit [Fintype V] [DecidableValuation α] in
/-- At the empty context, `cfSeed` reduces to a plain `extend`: with nothing
    observed, abduction preserves nothing and the counterfactual seed merely
    sets the antecedent. -/
theorem cfSeed_empty (M : SEM V α) (antecedent : V) (xAnt : α antecedent) :
    cfSeed M Valuation.empty antecedent xAnt =
      (Valuation.empty (α := α)).extend antecedent xAnt := by
  funext v
  by_cases h : v = antecedent
  · subst h; simp [cfSeed, Valuation.extend]
  · simp [cfSeed, Valuation.extend, Valuation.empty, h]

/-- **Pearl 3-step counterfactual via Lassiter RRR**, PMF-valued. Given
    actually-observed `observed` and a counterfactual intervention
    `antecedent := xAnt`, returns the probability distribution over
    counterfactual valuations.

    For deterministic SEMs, collapses to a Dirac at `developDet M (cfSeed ...)`
    (see `counterfactualSimulate_eq_pure_of_deterministic` below).

    Subsumes (with appropriate derived predicates):
    - `whetherCause` ([beller-gerstenberg-2025] Eq 1, graded)
    - `sufficientCause` ([beller-gerstenberg-2025] Eq 3, graded)
    - `probSufficiency` — Pearl's probability of sufficiency ([pearl-2019]),
      the SUF measure of [cao-white-lassiter-2025] (graded)
    - Lassiter probabilistic counterfactuals with overt probability operators -/
noncomputable def counterfactualSimulate
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAnt : α antecedent) :
    PMF (Valuation α) :=
  develop M (cfSeed M observed antecedent xAnt)

/-! ### Derived graded predicates (B&G 2025 W/H/S, etc.) -/

/-- **Whether-causation** ([beller-gerstenberg-2025] Eq 1):
    `W(A → e) = P(e' ≠ e | s, remove(A))`. Probability that the counterfactual
    outcome differs from the actual outcome `xEff_actual` if the antecedent
    were `xAnt_alt` instead of its actual value — the canonical `PMF.probOfSet`
    of the complement event `{v | ¬ v.hasValue effect xEff_actual}` under the
    counterfactual distribution.

    For deterministic SEMs, collapses to a {0,1} indicator (see
    `whetherCause_eq_indicator_of_deterministic`). -/
noncomputable def whetherCause
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAnt_alt : α antecedent)
    (effect : V) (xEff_actual : α effect) : ENNReal :=
  (counterfactualSimulate M observed antecedent xAnt_alt).probOfSet
    {v | ¬ v.hasValue effect xEff_actual}

/-- **Sufficient-causation** ([beller-gerstenberg-2025] Eq 3):
    `S(A → e) = P(W(A → e') | s, remove(\A))`. Probability that A would
    have been a whether-cause if all alternative causes had been removed.
    Definitionally `whetherCause` at the alternatives-removed background —
    the removal operation itself is the caller's responsibility (below).

    The caller supplies `alternativesRemoved : Valuation α` — the
    supersituation of `s` where alternative causes are set to their absent
    values. In the typical case this is `s` with the causally-independent
    siblings of `antecedent` set to their absent values. The substrate
    doesn't currently provide a `removeAlternatives` constructor; callers
    build it explicitly via `s.extend altᵢ xAbsentᵢ` chains. -/
noncomputable def sufficientCause
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (alternativesRemoved : Valuation α) (antecedent : V) (xAnt_alt : α antecedent)
    (effect : V) (xEff_actual : α effect) : ENNReal :=
  whetherCause M alternativesRemoved antecedent xAnt_alt effect xEff_actual

omit [Fintype V] [DecidableEq V] [DecidableValuation α] in
/-- The single-vertex marginal of a distribution over valuations: the
    probability that vertex `v` carries value `x`. -/
noncomputable def probOfValue (d : PMF (Valuation α)) (v : V) (x : α v) : ENNReal :=
  d.probOfSet {s | s.hasValue v x}

/-- **Probability of sufficiency** ([pearl-2019]), the SUF measure of
    [cao-white-lassiter-2025]: the counterfactual probability that
    intervening `cause := xC` yields `effect = xE`, evaluated against the
    factual context `observed` — the `effect = xE` marginal of Pearl's
    three-step abduction–action–prediction, via `counterfactualSimulate`.

    Distinct from plain interventional probability `P(effect | do(cause))`:
    causally-independent parents of `effect` recorded in `observed` are
    *preserved* rather than re-sampled — the oxygen-vs-match contrast
    [pearl-2019] uses to motivate the measure. -/
noncomputable def probSufficiency
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) : ENNReal :=
  probOfValue (counterfactualSimulate M observed cause xC) effect xE

/-! ### Bridge theorems: deterministic collapse -/

/-- Bridge: under `IsDeterministic`, `counterfactualSimulate` is the Dirac
    of the per-vertex counterfactual valuation `developDet M (cfSeed ...)`.
    Follows immediately from `develop_eq_pure_of_deterministic` (Basic.lean). -/
theorem counterfactualSimulate_eq_pure_of_deterministic
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (observed : Valuation α) (antecedent : V) (xAnt : α antecedent) :
    counterfactualSimulate M observed antecedent xAnt =
      PMF.pure (M.developDet (cfSeed M observed antecedent xAnt)) := by
  unfold counterfactualSimulate
  rw [develop_eq_pure_of_deterministic]

/-- Bridge: under `IsDeterministic`, `whetherCause` is the {0,1} indicator
    of whether the counterfactual outcome differs from `xEff_actual`. The
    graded B&G W collapses to the discrete Lewis-style "would the effect
    have been different?" — exactly the collapse [lassiter-2017-probabilistic-language] and [lucas-kemp-2015]
    predict for high-stability deterministic systems. -/
theorem whetherCause_eq_indicator_of_deterministic
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (observed : Valuation α) (antecedent : V) (xAnt_alt : α antecedent)
    (effect : V) (xEff_actual : α effect) :
    whetherCause M observed antecedent xAnt_alt effect xEff_actual =
      if (M.developDet (cfSeed M observed antecedent xAnt_alt)).hasValue effect xEff_actual
        then 0 else 1 := by
  unfold whetherCause
  rw [counterfactualSimulate_eq_pure_of_deterministic]
  simp only [PMF.probOfSet, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
  by_cases h : (M.developDet (cfSeed M observed antecedent xAnt_alt)).hasValue effect xEff_actual <;>
    simp [h]

/-- Bridge: under `IsDeterministic`, `probSufficiency` collapses to the {0,1}
    indicator of whether the counterfactual development hits `effect = xE` —
    the deterministic limit in which [cao-white-lassiter-2025]'s graded SUF
    recovers a categorical sufficiency judgment. -/
theorem probSufficiency_eq_indicator_of_deterministic
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (observed : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) :
    probSufficiency M observed cause xC effect xE =
      if (M.developDet (cfSeed M observed cause xC)).hasValue effect xE then 1 else 0 := by
  unfold probSufficiency probOfValue
  rw [counterfactualSimulate_eq_pure_of_deterministic]
  simp only [PMF.probOfSet, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
  by_cases h : (M.developDet (cfSeed M observed cause xC)).hasValue effect xE <;> simp [h]

end Causation.SEM

/-! ### BoolSEM specializations (legacy SBH-style binary semantics) -/

namespace Causation.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Causation (SEM Valuation BoolSEM)
open Causation.SEM (developsToValue causallySufficient)

/-- `BoolSEM`-flavored `causallySufficient`: setting `cause = true` develops
    `effect = true`. Matches old `Causation.causallySufficient` semantics. -/
abbrev causallySufficient (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.causallySufficient M s cause true effect true

/-- `BoolSEM`-flavored `manipulates`: cause's value (true vs false) flips
    effect's value under `developDet`. -/
abbrev manipulates (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.manipulates M s cause true false effect

/-- `BoolSEM`-flavored `probSufficiency`: the counterfactual probability
    that intervening `cause := true` yields `effect = true`. -/
noncomputable abbrev probSufficiency (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation (fun _ : V => Bool)) (cause effect : V) : ENNReal :=
  SEM.probSufficiency M s cause true effect true

/-- **Direct causal connection**: `cause` is a parent of `effect` in
    the SEM's graph. Pure structural predicate (no `developDet`); fully
    decidable structurally via `Finset.decidableMem`. -/
def hasDirectLaw (M : BoolSEM V) (cause effect : V) : Prop :=
  cause ∈ M.graph.parents effect

instance (M : BoolSEM V) (cause effect : V) :
    Decidable (hasDirectLaw M cause effect) :=
  inferInstanceAs (Decidable (cause ∈ M.graph.parents effect))

/-! Statement-level predicates are the canonical `developDet`-based forms
above (`causallySufficient`, `CCSelection.completesForEffect`); concrete
proofs compute a `developDetOn` iteration with `decide` and lift through
the soundness bridge (`developDet_hasValue_of_developDetOn_hasValue`) or
the `CCSelection.*_of_developDetOn` helpers. The former `(vs, n)`-indexed
statement forms (`causallySufficientOn`/`completesForEffectOn`) were
removed: they leaked the vertex list and fuel into theorem statements, and
their negations asserted facts about an iteration trace rather than the
causal notion. -/

/-! ### Bridges: manipulates from developDetOn computation -/

omit [Fintype V] in
/-- **Positive `manipulates` bridge**: if `developDetOn` produces different
    explicit values `y1 ≠ y2` for cause=true vs cause=false, then
    `manipulates` holds.

    `y1`, `y2` are explicit (not implicit) so consumers can write
    `exact manipulates_of_developDetOn_ne M (vs := …) (n := …) true false (by decide) (by decide) (by decide)`
    without `(by decide)` running into metavariable inference issues. -/
theorem manipulates_of_developDetOn_ne (M : BoolSEM V)
    [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    {s : Valuation (fun _ : V => Bool)} (vs : List V) (n : ℕ)
    {cause effect : V} (y1 y2 : Bool)
    (h1 : (SEM.developDetOn M vs n (s.extend cause true)).hasValue effect y1)
    (h2 : (SEM.developDetOn M vs n (s.extend cause false)).hasValue effect y2)
    (hne : y1 ≠ y2) :
    manipulates M s cause effect := by
  unfold manipulates SEM.manipulates
  have h1' := SEM.developDet_hasValue_of_developDetOn_hasValue h1
  have h2' := SEM.developDet_hasValue_of_developDetOn_hasValue h2
  unfold Valuation.hasValue at h1' h2'
  rw [h1', h2']
  exact fun heq => hne (Option.some.inj heq)

omit [Fintype V] in
/-- **Negative `manipulates` bridge**: if `developDetOn` produces the same
    explicit value `y` for cause=true and cause=false, then `manipulates`
    is false.

    `y` is explicit (not implicit) so consumers can write
    `exact not_manipulates_of_developDetOn_eq M (vs := …) (n := …) true (by decide) (by decide)`
    without metavariable issues. -/
theorem not_manipulates_of_developDetOn_eq (M : BoolSEM V)
    [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    {s : Valuation (fun _ : V => Bool)} (vs : List V) (n : ℕ)
    {cause effect : V} (y : Bool)
    (h1 : (SEM.developDetOn M vs n (s.extend cause true)).hasValue effect y)
    (h2 : (SEM.developDetOn M vs n (s.extend cause false)).hasValue effect y) :
    ¬ manipulates M s cause effect := by
  unfold manipulates SEM.manipulates
  have h1' := SEM.developDet_hasValue_of_developDetOn_hasValue h1
  have h2' := SEM.developDet_hasValue_of_developDetOn_hasValue h2
  unfold Valuation.hasValue at h1' h2'
  rw [h1', h2']
  exact fun h => h rfl

end Causation.BoolSEM

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}

/-- **Causal entailment** ([nadathur-2023-implicatives] Def 5): the strict
    T_D fixed point relative to `s` assigns `x` to `v` ("s ⊨_D ⟨v, x⟩").
    Stated over the partial `developDetVtx?` — an undetermined exogenous
    vertex entails nothing, and an inner vertex entails nothing while any
    parent is u-valued. Contrast the eager-total `developsToValue` above. -/
def causallyEntails [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [IsDeterministic M] (s : Valuation α) (v : V) (x : α v) : Prop :=
  developDetVtx? M s v = some x

noncomputable instance [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [IsDeterministic M] (s : Valuation α) (v : V) (x : α v) :
    Decidable (causallyEntails M s v x) := Classical.dec _

/-- Transfer a fuel-mirror computation to `causallyEntails` (both
    polarities, via the fuel bridge). The study idiom for concrete claims:
    `(causallyEntails_iff_fuel M rank @hrank hn s v x).mpr (by decide)`. -/
theorem causallyEntails_iff_fuel [DecidableEq V] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (r : CausalGraph.Ranking M.graph)
    {n : ℕ} {v : V} (hn : r.rank v < n) (s : Valuation α) (x : α v) :
    causallyEntails M s v x ↔ developDetVtxFuel M s n v = some x := by
  rw [causallyEntails, ← developDetVtxFuel_eq_developDetVtx? M r s hn]

/-- Strict causal entailment of the extended background implies the bare
    eager-total sufficiency predicate (`causallySufficient`): the partial
    development refines the total one wherever it resolves. -/
theorem causallySufficient_of_causallyEntails [Fintype V] [DecidableEq V]
    [DecidableValuation α] {M : SEM V α} [CausalGraph.IsDAG M.graph]
    [IsDeterministic M] {s : Valuation α} {cause : V} {xC : α cause}
    {effect : V} {xE : α effect}
    (h : causallyEntails M (s.extend cause xC) effect xE) :
    causallySufficient M s cause xC effect xE :=
  (developDet_hasValue_iff M (s.extend cause xC) effect xE).mpr
    (developDetVtx_eq_of_developDetVtx?_eq_some M h)

/-- Causal entailment is functional: a vertex entails at most one value. -/
theorem causallyEntails_unique [DecidableEq V] {M : SEM V α}
    [CausalGraph.IsDAG M.graph] [IsDeterministic M] {s : Valuation α}
    {v : V} {x y : α v}
    (hx : causallyEntails M s v x) (hy : causallyEntails M s v y) : x = y :=
  Option.some.inj ((hx.symm.trans hy))

/-- **Consistent supersituation** ([nadathur-2023-implicatives] Def 9b),
    faithful "not the opposite" form: `s'` extends `base`, and for every
    vertex `s'` newly fixes, `base` does not causally entail a *different*
    value there. Def 9b restricts the condition to inner variables; that
    restriction is automatic here, since `developDetVtx?` is `none` at
    undetermined exogenous vertices. -/
def isConsistentSuper [DecidableEq V] [DecidableValuation α] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (base s' : Valuation α) : Prop :=
  base ≤ s' ∧
  ∀ (x : V) (xv : α x), base.get x = none → s'.get x = some xv →
    ∀ yv : α x, yv ≠ xv → ¬ causallyEntails M base x yv

noncomputable instance [DecidableEq V] [DecidableValuation α] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M] (base s' : Valuation α) :
    Decidable (isConsistentSuper M base s') := Classical.dec _

/-- Every valuation is a consistent supersituation of itself. -/
theorem isConsistentSuper_self [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) : isConsistentSuper M s s :=
  ⟨fun _ _ h => h, fun _ _ hn hs => by simp [hn] at hs⟩

/-- **Determinations cannot be undone** ([nadathur-2023-implicatives]
    Def 2 prose): causal entailment is monotone under consistent
    supersituations — whatever `s` causally entails, any Def-9b-consistent
    extension of `s` still causally entails. -/
theorem causallyEntails_mono [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s s' : Valuation α} (hcons : isConsistentSuper M s s')
    {v : V} {x : α v} (h : causallyEntails M s v x) :
    causallyEntails M s' v x := by
  induction v using (CausalGraph.IsDAG.wf (G := M.graph)).induction with
  | _ v ih =>
    cases hs'v : s'.get v with
    | some z =>
        -- s' fixes v at z; show z = x, then v is determined.
        have hzx : z = x := by
          cases hsv : s.get v with
          | some w =>
              -- determined in s: w = x (from h) and s'.get v = some w (le).
              have hw : developDetVtx? M s v = some w :=
                developDetVtx?_determined M hsv
              have hxw : w = x := Option.some.inj (hw.symm.trans h)
              have := hcons.1 v w hsv
              rw [Valuation.hasValue, hs'v] at this
              exact (Option.some.inj this).trans hxw
          | none =>
              -- newly fixed: consistency forbids s entailing any value ≠ z.
              by_contra hne
              exact hcons.2 v z hsv hs'v x (fun hxz => hne hxz.symm) h
        rw [causallyEntails, developDetVtx?_determined M hs'v, hzx]
    | none =>
        -- v undetermined in s' hence in s; h forces the inner case.
        have hsv : s.get v = none := by
          cases hsv : s.get v with
          | none => rfl
          | some w =>
              have := hcons.1 v w hsv
              rw [Valuation.hasValue, hs'v] at this
              exact absurd this (by simp)
        rw [causallyEntails, developDetVtx?_unfold] at h
        simp only [hsv] at h
        by_cases hPar : M.graph.parents v = ∅
        · simp [hPar] at h
        · simp only [hPar, if_false] at h
          by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
          · rw [dif_pos hAll] at h
            refine developDetVtx?_inner M hs'v hPar
              (fun u => (developDetVtx? M s u.val).get (hAll u)) (fun u => ?_) |>.trans ?_
            · exact ih u.val (Relation.TransGen.single u.property)
                (Option.some_get (hAll u)).symm
            · exact h
          · rw [dif_neg hAll] at h
            exact absurd h (by simp)

/-- **Exogenous settlement**: `s'` extends `base` by fixing only
    exogenous (parentless) vertices.

    Project-canonical restriction on Def 10b's supersituation
    quantifiers. Quantifying over *all* consistent supersituations (the
    literal Def 9b/10b reading) falsifies the paper's own §6.1.1
    verdicts: relative to the Dreyfus background, fixing the undetermined
    inner vertex MSG (plus LST, ¬BRK) is Def-9b-consistent and reaches
    COM without entailing NRV, contradicting the claim that ⟨NRV,1⟩ is
    causally necessary for ⟨COM,1⟩. The paper's worked example (21b)
    considers only background settlements ("the only such available");
    this definition makes that reading explicit. -/
def IsExogenousSettlement [DecidableValuation α] (M : SEM V α)
    (base s' : Valuation α) : Prop :=
  base ≤ s' ∧
  ∀ v : V, base.get v = none → (s'.get v).isSome → M.graph.parents v = ∅

/-- Information order, executable characterization. -/
theorem Valuation.le_iff_forall [DecidableValuation α] {s₁ s₂ : Valuation α} :
    s₁ ≤ s₂ ↔ ∀ v : V, (s₁.get v).isSome → s₁.get v = s₂.get v := by
  constructor
  · intro h v hv
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hv
    rw [hx]; exact (h v x hx).symm
  · intro h v x hx
    have := h v (by rw [hx]; rfl)
    rw [hx] at this; exact this.symm

instance [DecidableEq V] [Fintype V] [DecidableValuation α] (s₁ s₂ : Valuation α) :
    Decidable (s₁ ≤ s₂) :=
  decidable_of_iff _ Valuation.le_iff_forall.symm

instance [DecidableEq V] [Fintype V] [DecidableValuation α] (M : SEM V α)
    (base s' : Valuation α) : Decidable (IsExogenousSettlement M base s') :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An exogenous settlement of an extension at a fresh exogenous vertex
    is an exogenous settlement of the base. -/
theorem IsExogenousSettlement.of_extend [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} {s s' : Valuation α} {p : V} {xP : α p}
    (hexo : M.graph.parents p = ∅) (hp : s.get p = none)
    (h : IsExogenousSettlement M (s.extend p xP) s') :
    IsExogenousSettlement M s s' := by
  refine ⟨(Valuation.le_extend xP hp).trans h.1, fun v hv hsv => ?_⟩
  by_cases hvp : v = p
  · subst hvp; exact hexo
  · exact h.2 v (by rw [Valuation.extend_get_ne hvp]; exact hv) hsv

/-- Exogenous settlements are automatically Def-9b-consistent: a newly
    fixed vertex is parentless and undetermined in `base`, so `base`
    causally entails nothing about it. -/
theorem IsExogenousSettlement.isConsistentSuper [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {base s' : Valuation α} (h : IsExogenousSettlement M base s') :
    isConsistentSuper M base s' := by
  refine ⟨h.1, fun x xv hn hs yv _ hent => ?_⟩
  have hExo : M.graph.parents x = ∅ := h.2 x hn (by rw [hs]; rfl)
  rw [causallyEntails, developDetVtx?_exogenous M hn hExo] at hent
  simp at hent

namespace causallyNecessary

/-- **Preamble of Definition 10** ([nadathur-2023-implicatives], with
    footnote 8's rationale): the background entails neither the cause
    fact nor the effect fact. Shared by Def 10a (sufficiency, see
    `Implicative.manageSem`) and Def 10b (necessity, below). -/
def precondition [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ¬ causallyEntails M s cause xC ∧ ¬ causallyEntails M s effect xE

noncomputable instance [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (precondition M s cause xC effect xE) := Classical.dec _

/-- **Achievability**, clause (i) of Def 10b: some consistent
    supersituation `s'` of `s + (cause = xC)` with `effect ∉ dom(s')`
    causally entails `effect = xE`. Quantified over exogenous settlements
    (see `IsExogenousSettlement`); Def 9b consistency is then automatic
    (`IsExogenousSettlement.isConsistentSuper`). -/
def achievable [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∃ s' : Valuation α, IsExogenousSettlement M (s.extend cause xC) s' ∧
    s'.get effect = none ∧ causallyEntails M s' effect xE

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (achievable M s cause xC effect xE) := Classical.dec _

/-- **No-alternative**, clause (ii) of Def 10b in positive-implication
    form: every consistent supersituation of `s` (exogenous settlement,
    `effect ∉ dom(s')`) that causally entails `effect = xE` also causally
    entails `cause = xC` — every consistent path to the effect goes
    through the cause. The paper's exclusion `s' ⊭ ⟨X,x⟩` is the
    *developed* entailment, not the syntactic `s'.get cause ≠ some xC`. -/
def noAlternative [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∀ s' : Valuation α, IsExogenousSettlement M s s' → s'.get effect = none →
    causallyEntails M s' effect xE → causallyEntails M s' cause xC

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (noAlternative M s cause xC effect xE) := Classical.dec _

end causallyNecessary

/-- **Causal Necessity** ([nadathur-2023-implicatives] Definition 10b)
    over the strict T_D development, polymorphic over value types:

    - **Preamble**: `s` entails neither `cause = xC` nor `effect = xE`.
    - **(i) Achievability**: some consistent supersituation of
      `s + (cause = xC)` not fixing the effect entails `effect = xE`.
    - **(ii) No-alternative**: every consistent supersituation of `s` not
      fixing the effect that entails `effect = xE` entails `cause = xC`.

    Supersituations are quantified over exogenous settlements — see
    `IsExogenousSettlement` for why the literal Def 9b/10b quantification
    is unfaithful to the paper's own verdicts. -/
def causallyNecessary [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  causallyNecessary.precondition M s cause xC effect xE ∧
  causallyNecessary.achievable M s cause xC effect xE ∧
  causallyNecessary.noAlternative M s cause xC effect xE

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallyNecessary M s cause xC effect xE) := Classical.dec _

/-! ### Executable Def 10b (fuel form) and decidability -/

/-- Executable mirror of `causallyNecessary` at fuel `n`: every
    `causallyEntails` clause replaced by its `developDetVtxFuel` form.
    Genuinely decidable (the supersituation quantifiers range over the
    Pi-`Fintype` of valuations). Connected to the canonical predicate by
    `causallyNecessary_iff_fuel`. -/
def causallyNecessaryFuel [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (n : ℕ)
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  (¬ developDetVtxFuel M s n cause = some xC ∧
   ¬ developDetVtxFuel M s n effect = some xE) ∧
  (∃ s' : Valuation α, IsExogenousSettlement M (s.extend cause xC) s' ∧
    s'.get effect = none ∧ developDetVtxFuel M s' n effect = some xE) ∧
  (∀ s' : Valuation α, IsExogenousSettlement M s s' → s'.get effect = none →
    developDetVtxFuel M s' n effect = some xE →
    developDetVtxFuel M s' n cause = some xC)

instance [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [IsDeterministic M] (n : ℕ)
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallyNecessaryFuel M n s cause xC effect xE) := by
  unfold causallyNecessaryFuel
  infer_instance

/-- The canonical Def 10b coincides with its fuel form once the fuel
    exceeds a rank function for the graph. Study idiom:
    `(causallyNecessary_iff_fuel M rank @hrank hn s …).mpr (by decide)`. -/
theorem causallyNecessary_iff_fuel [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (r : CausalGraph.Ranking M.graph)
    {n : ℕ} (hn : ∀ v : V, r.rank v < n)
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    causallyNecessary M s cause xC effect xE ↔
      causallyNecessaryFuel M n s cause xC effect xE := by
  have hpt : ∀ (t : Valuation α) (v : V) (x : α v),
      causallyEntails M t v x ↔ developDetVtxFuel M t n v = some x :=
    fun t v x => causallyEntails_iff_fuel M r (hn v) t x
  unfold causallyNecessary causallyNecessary.precondition
    causallyNecessary.achievable causallyNecessary.noAlternative
    causallyNecessaryFuel
  exact and_congr
    (and_congr (not_congr (hpt s cause xC)) (not_congr (hpt s effect xE)))
    (and_congr
      (exists_congr fun s' => and_congr_right fun _ =>
        and_congr_right fun _ => hpt s' effect xE)
      (forall_congr' fun s' => imp_congr_right fun _ => imp_congr_right fun _ =>
        imp_congr (hpt s' effect xE) (hpt s' cause xC)))

end Causation.SEM

namespace Causation.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Causation (SEM Valuation BoolSEM)

/-- `BoolSEM`-flavored `causallyNecessary`: setting `cause = true` is
    necessary (Def 10b) for `effect = true`. -/
abbrev causallyNecessary (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  SEM.causallyNecessary M s cause true effect true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (causallyNecessary M s cause effect) := Classical.dec _

end Causation.BoolSEM
