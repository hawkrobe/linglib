module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Linglib.Semantics.Causation.SEM.Basic
public import Linglib.Semantics.Causation.SEM.Bool
public import Linglib.Semantics.Causation.SEM.Deterministic

/-!
# SEM: Causal Counterfactual Predicates

Polymorphic counterfactual predicates over a `SEM V α`, plus `BoolSEM`-flavored
aliases for legacy SBH-style binary semantics.

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

- **`cfSeed`, `counterfactual`**: the rewind–revise–regenerate counterfactual of
  [lassiter-2017-probabilistic-language].

- **`WhetherCause`**: [beller-gerstenberg-2025]'s whether-causation, deterministic case.

- **`probSufficiency`**: [pearl-2019]'s probability of sufficiency, over a measure on
  background outcomes.

`BoolSEM`-namespace aliases specialize the polymorphic predicates to
`α := fun _ ↦ Bool` with `xC = true`, `xE = true` (legacy SBH semantics).

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

## References

* [nadathur-2023-implicatives]
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

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallySufficient M s cause xC effect xE) :=
  Classical.dec _

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

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) :
    Decidable (manipulates M s cause xC1 xC2 effect) :=
  Classical.dec _

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

omit [DecidableValuation α] in
noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAlt : α antecedent) (effect : V) (xE : α effect) :
    Decidable (WhetherCause M observed antecedent xAlt effect xE) :=
  Classical.dec _

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
    [CausalGraph.IsDAG M.graph]
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
    [CausalGraph.IsDAG M.graph]
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
    parent is u-valued. Contrast the eager-total `causallySufficient` above. -/
def causallyEntails [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) (x : α v) : Prop :=
  developDetVtx? M s v = some x

noncomputable instance [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) (x : α v) :
    Decidable (causallyEntails M s v x) := Classical.dec _

/-- Transfer a fuel-mirror computation to `causallyEntails` (both
    polarities, via the fuel bridge). The study idiom for concrete claims:
    `(causallyEntails_iff_fuel M rank @hrank hn s v x).mpr (by decide)`. -/
theorem causallyEntails_iff_fuel [DecidableEq V] (M : SEM V α)
    [CausalGraph.IsDAG M.graph]
    (r : CausalGraph.Ranking M.graph)
    {n : ℕ} {v : V} (hn : r v < n) (s : Valuation α) (x : α v) :
    causallyEntails M s v x ↔ developDetVtxFuel M s n v = some x := by
  rw [causallyEntails, ← developDetVtxFuel_eq_developDetVtx? M r s hn]

/-- Strict causal entailment of the extended background implies the bare
    eager-total sufficiency predicate (`causallySufficient`): the partial
    development refines the total one wherever it resolves. -/
theorem causallySufficient_of_causallyEntails [Fintype V] [DecidableEq V]
    [DecidableValuation α] {M : SEM V α} [CausalGraph.IsDAG M.graph]
    {s : Valuation α} {cause : V} {xC : α cause}
    {effect : V} {xE : α effect}
    (h : causallyEntails M (s.extend cause xC) effect xE) :
    causallySufficient M s cause xC effect xE :=
  (developDet_hasValue_iff M (s.extend cause xC) effect xE).mpr
    (developDetVtx_eq_of_developDetVtx?_eq_some M h)

/-- Causal entailment is functional: a vertex entails at most one value. -/
theorem causallyEntails_unique [DecidableEq V] {M : SEM V α}
    [CausalGraph.IsDAG M.graph] {s : Valuation α}
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
    [CausalGraph.IsDAG M.graph]
    (base s' : Valuation α) : Prop :=
  base ≤ s' ∧
  ∀ (x : V) (xv : α x), base.get x = none → s'.get x = some xv →
    ∀ yv : α x, yv ≠ xv → ¬ causallyEntails M base x yv

noncomputable instance [DecidableEq V] [DecidableValuation α] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] (base s' : Valuation α) :
    Decidable (isConsistentSuper M base s') := Classical.dec _

/-- Every valuation is a consistent supersituation of itself. -/
theorem isConsistentSuper_self [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) : isConsistentSuper M s s :=
  ⟨le_rfl, fun _ _ hn hs => by simp [hn] at hs⟩

/-- **Determinations cannot be undone** ([nadathur-2023-implicatives]
    Def 2 prose): causal entailment is monotone under consistent
    supersituations — whatever `s` causally entails, any Def-9b-consistent
    extension of `s` still causally entails. -/
theorem causallyEntails_mono [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph]
    {s s' : Valuation α} (hcons : isConsistentSuper M s s')
    {v : V} {x : α v} (h : causallyEntails M s v x) :
    causallyEntails M s' v x := by
  induction v using (inferInstance : M.graph.IsDAG).induction with
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
              have := Valuation.le_def.1 hcons.1 v w hsv
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
              have := Valuation.le_def.1 hcons.1 v w hsv
              rw [Valuation.hasValue, hs'v] at this
              exact absurd this (by simp)
        rw [causallyEntails, developDetVtx?_unfold] at h
        simp only [hsv] at h
        by_cases hPar : M.graph.parents v = ∅
        · simp [hPar] at h
        · simp only [hPar, ite_false] at h
          by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
          · rw [dite_eq_left hAll] at h
            refine developDetVtx?_inner M hs'v hPar
              (fun u => (developDetVtx? M s u.val).get (hAll u)) (fun u => ?_) |>.trans ?_
            · exact ih u.val (Relation.TransGen.single u.property)
                (Option.some_get (hAll u)).symm
            · exact h
          · rw [dite_eq_right hAll] at h
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
    {M : SEM V α} [CausalGraph.IsDAG M.graph]
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
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ¬ causallyEntails M s cause xC ∧ ¬ causallyEntails M s effect xE

noncomputable instance [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (precondition M s cause xC effect xE) := Classical.dec _

/-- **Achievability**, clause (i) of Def 10b: some consistent
    supersituation `s'` of `s + (cause = xC)` with `effect ∉ dom(s')`
    causally entails `effect = xE`. Quantified over exogenous settlements
    (see `IsExogenousSettlement`); Def 9b consistency is then automatic
    (`IsExogenousSettlement.isConsistentSuper`). -/
def achievable [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∃ s' : Valuation α, IsExogenousSettlement M (s.extend cause xC) s' ∧
    s'.get effect = none ∧ causallyEntails M s' effect xE

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (achievable M s cause xC effect xE) := Classical.dec _

/-- **No-alternative**, clause (ii) of Def 10b in positive-implication
    form: every consistent supersituation of `s` (exogenous settlement,
    `effect ∉ dom(s')`) that causally entails `effect = xE` also causally
    entails `cause = xC` — every consistent path to the effect goes
    through the cause. The paper's exclusion `s' ⊭ ⟨X,x⟩` is the
    *developed* entailment, not the syntactic `s'.get cause ≠ some xC`. -/
def noAlternative [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∀ s' : Valuation α, IsExogenousSettlement M s s' → s'.get effect = none →
    causallyEntails M s' effect xE → causallyEntails M s' cause xC

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
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
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  causallyNecessary.precondition M s cause xC effect xE ∧
  causallyNecessary.achievable M s cause xC effect xE ∧
  causallyNecessary.noAlternative M s cause xC effect xE

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallyNecessary M s cause xC effect xE) := Classical.dec _

/-! ### Executable Def 10b (fuel form) and decidability -/

/-- Executable mirror of `causallyNecessary` at fuel `n`: every
    `causallyEntails` clause replaced by its `developDetVtxFuel` form.
    Genuinely decidable (the supersituation quantifiers range over the
    Pi-`Fintype` of valuations). Connected to the canonical predicate by
    `causallyNecessary_iff_fuel`. -/
def causallyNecessaryFuel [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) (n : ℕ)
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
    (M : SEM V α) (n : ℕ)
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallyNecessaryFuel M n s cause xC effect xE) := by
  letI := Valuation.fintype (α := α)
  unfold causallyNecessaryFuel
  infer_instance

/-- The canonical Def 10b coincides with its fuel form once the fuel
    exceeds a rank function for the graph. Study idiom:
    `(causallyNecessary_iff_fuel M rank @hrank hn s …).mpr (by decide)`. -/
theorem causallyNecessary_iff_fuel [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (r : CausalGraph.Ranking M.graph)
    {n : ℕ} (hn : ∀ v : V, r v < n)
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
      (exists_congr fun s' => and_congr_right fun _ ↦
        and_congr_right fun _ ↦ hpt s' effect xE)
      (forall_congr' fun s' => imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
        imp_congr (hpt s' effect xE) (hpt s' cause xC)))

end Causation.SEM

namespace Causation.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Causation (SEM Valuation BoolSEM)

/-- `BoolSEM`-flavored `causallyNecessary`: setting `cause = true` is
    necessary (Def 10b) for `effect = true`. -/
abbrev causallyNecessary (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  SEM.causallyNecessary M s cause true effect true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation _) (cause effect : V) :
    Decidable (causallyNecessary M s cause effect) := Classical.dec _

end Causation.BoolSEM
