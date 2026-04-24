import Linglib.Core.Causal.SEM.Basic
import Linglib.Core.Causal.SEM.Bool
import Linglib.Core.Causal.SEM.Deterministic

/-!
# SEM: Causal Counterfactual Predicates (V2)

Polymorphic counterfactual predicates over a `SEM V α`, plus `BoolSEM`-flavored
aliases for legacy SBH-style binary semantics.

- **`developsToValue M s v x`**: after developing `s`, vertex `v` has value `x`.
  Replaces the old `developsToTrue` (Bool-specialized) with a polymorphic version.

- **`causallySufficient M s cause xC effect xE`**: extending `s` with `xC` at
  `cause` then developing produces `xE` at `effect`. Polymorphic generalization
  of @cite{nadathur-lauer-2020} Definition 23.

- **`causallyNecessary M s cause xC effect xE`**: @cite{nadathur-2024}
  Definition 10b — precondition + achievability + but-for clauses.
  Refactored to use abstract quantification over `Valuation α` (see "Refactor"
  below); the previous `allExtensions`/`freeExtensions` enumeration was
  noncomputable and opaque to structural reduction.

`BoolSEM`-namespace aliases specialize the polymorphic predicates to
`α := fun _ => Bool` with `xC = true`, `xE = true` (legacy SBH semantics).

## Refactor (post-`Deterministic.lean`)

Internally these predicates call `developDetVtx M s v = x` (per-vertex,
structurally reducible via `WellFounded.fix_eq`) instead of the old opaque
`(M.developDet s).hasValue v x`. The `(M.developDet s).hasValue v x` API
shape still works via `developDet_hasValue_iff` — same call sites, cleanly
reducible internals.

`causallyNecessary`'s achievability/but-for clauses are now stated as abstract
quantifications over `Valuation α` (`∃ s', s.le s' ∧ ...` / `∀ s', s.le s' → ...`)
rather than enumeration over a noncomputable `allExtensions` list. Concrete
proofs supply existential witnesses directly and discharge universals by case
analysis on which free vertices `s'` fixes (the `isConsistentSuper` clause
constrains `s'`'s values to agree with `developDetVtx M s`). Same paper
content; structurally provable.

## Computability

`developDet` is noncomputable (cascading from `WellFounded.fix`). Predicates
here are noncomputable. `Decidable` instances via `Classical.dec`. Concrete
proofs reduce structurally via `developDetVtx_unfold` + `rfl` rather than
through `Fintype.elems.toList` opacity (which blocked the previous substrate).
Matches the mathlib `Polynomial.eval` precedent: noncomputable canonical
definition, structurally reducible per-vertex unfolding lemmas.
-/

namespace Core.Causal.SEM

variable {V : Type*} {α : V → Type*}
variable [Fintype V] [DecidableEq V] [DecidableValuation α]

-- ════════════════════════════════════════════════════
-- § Polymorphic counterfactual predicates
-- ════════════════════════════════════════════════════

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

    Polymorphic generalization of @cite{nadathur-lauer-2020} Definition 23.
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

-- ════════════════════════════════════════════════════
-- § Basic API lemmas (polymorphic)
-- ════════════════════════════════════════════════════

/-- `developsToValue` unfolds to `(developDet M s).hasValue v x`. -/
@[simp] theorem developsToValue_iff (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) :
    developsToValue M s v x ↔ (M.developDet s).hasValue v x := Iff.rfl

/-- `causallySufficient` unfolds to `developsToValue` of the extended valuation. -/
@[simp] theorem causallySufficient_iff (M : SEM V α)
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

-- ════════════════════════════════════════════════════
-- § Unified counterfactual primitive (PMF-canonical)
-- ════════════════════════════════════════════════════

/-! Pearl-style counterfactual simulation via Lassiter's RRR heuristic
    (@cite{lassiter-2017-probabilistic-language} §3): "Rewind to the
    antecedent's causal layer, Revise the antecedent, selectively
    Regenerate descendants while preserving causally-independent
    observations." Subsumes:
    - @cite{lewis-1973-causation} / @cite{nadathur-lauer-2020} deterministic
      counterfactuals (Dirac specialization)
    - @cite{beller-gerstenberg-2025} W/H/S aspects (graded probability)
    - @cite{lassiter-2017-probabilistic-language} probabilistic counterfactuals
      with overt probability operators

    Key insight: under the high-stability assumption (Lucas & Kemp 2015
    ESM), Pearl 3-step abduction reduces to "preserve causally-independent
    observations, regenerate descendants" — no explicit exogenous noise
    types needed. The existing `develop` PMF naturally produces the right
    distribution when fed the counterfactual seed valuation.

    Morgenbesser's coin example (Barker 1998, Lassiter §1): bet → win ←
    heads. Observed `{bet:=false, win:=false, heads:=true}`. Counterfactual
    `bet := true`. Then `cfSeed = {bet:=true, heads:=true, win:=none}`
    (heads is causally independent so preserved; win is descendant of bet
    so regenerated). `develop` computes `win := bet ∧ heads = true`. The
    counterfactual probability of winning is 1, matching Lassiter's
    prediction (and contradicting "Rewind, Revise, Re-run" without
    selective regeneration). -/

/-- **Counterfactual seed** (Lassiter §3 RRR): the partial valuation that
    `counterfactualSimulate` feeds to `develop`. Sets `antecedent := xAnt`,
    leaves descendants of antecedent undetermined (to be regenerated),
    preserves `observed` values for causally-independent vertices. -/
noncomputable def cfSeed [DecidableEq V]
    (M : SEM V α) (observed : Valuation α)
    (antecedent : V) (xAnt : α antecedent) : Valuation α := fun v =>
  if h : v = antecedent then some (h ▸ xAnt)
  else
    haveI : Decidable (M.graph.IsStrictAncestor antecedent v) := Classical.dec _
    if M.graph.IsStrictAncestor antecedent v then none
    else observed.get v

/-- **Pearl 3-step counterfactual via Lassiter RRR**, PMF-valued. Given
    actually-observed `observed` and a counterfactual intervention
    `antecedent := xAnt`, returns the probability distribution over
    counterfactual valuations.

    For deterministic SEMs, collapses to a Dirac at `developDet M (cfSeed ...)`
    (see `counterfactualSimulate_eq_pure_of_deterministic` below).

    Subsumes (with appropriate derived predicates):
    - `causallyNecessary` (@cite{nadathur-2024} Def 10b, discrete)
    - `whetherCause` (@cite{beller-gerstenberg-2025} Eq 1, graded)
    - `sufficientCause` (@cite{beller-gerstenberg-2025} Eq 3, graded)
    - Lassiter probabilistic counterfactuals with overt probability operators

    `probabilisticSuf` (@cite{cao-white-lassiter-2025}) is **not** a special
    case — it's interventional probability without observation conditioning;
    lives in `Interventional.lean`. -/
noncomputable def counterfactualSimulate [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAnt : α antecedent) :
    PMF (Valuation α) :=
  develop M (cfSeed M observed antecedent xAnt)

-- ════════════════════════════════════════════════════
-- § Derived graded predicates (B&G 2025 W/H/S, etc.)
-- ════════════════════════════════════════════════════

/-- **Whether-causation** (@cite{beller-gerstenberg-2025} Eq 1):
    `W(A → e) = P(e' ≠ e | s, remove(A))`. Probability that the counterfactual
    outcome differs from the actual outcome `xEff_actual` if the antecedent
    were `xAnt_alt` instead of its actual value.

    For deterministic SEMs, collapses to a {0,1} indicator (see
    `whetherCause_eq_indicator_of_deterministic`). -/
noncomputable def whetherCause [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (observed : Valuation α) (antecedent : V) (xAnt_alt : α antecedent)
    (effect : V) (xEff_actual : α effect) : ENNReal :=
  ∑' v : Valuation α, if v.hasValue effect xEff_actual
                      then 0
                      else (counterfactualSimulate M observed antecedent xAnt_alt) v

/-- **Sufficient-causation** (@cite{beller-gerstenberg-2025} Eq 3):
    `S(A → e) = P(W(A → e') | s, remove(\A))`. Probability that A would
    have been a whether-cause if all alternative causes had been removed.

    The caller supplies `alternativesRemoved : Valuation α` — the
    supersituation of `s` where alternative causes are set to their absent
    values. In the typical case this is `s` with the causally-independent
    siblings of `antecedent` set to their absent values. The substrate
    doesn't currently provide a `removeAlternatives` constructor; callers
    build it explicitly via `s.extend altᵢ xAbsentᵢ` chains. -/
noncomputable def sufficientCause [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (alternativesRemoved : Valuation α) (antecedent : V) (xAnt_alt : α antecedent)
    (effect : V) (xEff_actual : α effect) : ENNReal :=
  whetherCause M alternativesRemoved antecedent xAnt_alt effect xEff_actual

-- ════════════════════════════════════════════════════
-- § Bridge theorems: deterministic collapse
-- ════════════════════════════════════════════════════

/-- Bridge: under `IsDeterministic`, `counterfactualSimulate` is the Dirac
    of the per-vertex counterfactual valuation `developDet M (cfSeed ...)`.
    Follows immediately from `develop_eq_pure_of_deterministic` (Basic.lean,
    currently sorry'd pending the per-vertex `developDet` proof — same
    chain as before the refactor, no new sorrys introduced). -/
theorem counterfactualSimulate_eq_pure_of_deterministic
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (observed : Valuation α) (antecedent : V) (xAnt : α antecedent) :
    counterfactualSimulate M observed antecedent xAnt =
      PMF.pure (M.developDet (cfSeed M observed antecedent xAnt)) := by
  unfold counterfactualSimulate
  rw [develop_eq_pure_of_deterministic]

/-- Bridge: under `IsDeterministic`, `whetherCause` is the {0,1} indicator
    of whether the counterfactual outcome differs from `xEff_actual`. The
    graded B&G W collapses to the discrete Lewis-style "would the effect
    have been different?" — exactly the collapse Lassiter §3 / Lucas-Kemp
    predict for high-stability deterministic systems. -/
theorem whetherCause_eq_indicator_of_deterministic
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (observed : Valuation α) (antecedent : V) (xAnt_alt : α antecedent)
    (effect : V) (xEff_actual : α effect) :
    whetherCause M observed antecedent xAnt_alt effect xEff_actual =
      if (M.developDet (cfSeed M observed antecedent xAnt_alt)).hasValue effect xEff_actual
        then 0 else 1 := by
  unfold whetherCause
  rw [counterfactualSimulate_eq_pure_of_deterministic]
  rw [tsum_eq_single (M.developDet (cfSeed M observed antecedent xAnt_alt))
      (fun v hv => by
        rw [PMF.pure_apply_of_ne _ _ hv]; simp)]
  by_cases h : (M.developDet (cfSeed M observed antecedent xAnt_alt)).hasValue effect xEff_actual
  · simp [h]
  · simp [h, PMF.pure_apply_self]

-- ════════════════════════════════════════════════════
-- § Nadathur 2024 Def 10b: causallyNecessary (BoolSEM only)
-- ════════════════════════════════════════════════════

/-! Port of @cite{nadathur-2024} Definition 10b to V2. Specialized to
    `BoolSEM` (the binary substrate the original definition was given on);
    polymorphic generalization to multi-valued α can come if a consumer
    needs it. -/

end Core.Causal.SEM

-- ════════════════════════════════════════════════════
-- § BoolSEM specializations (legacy SBH-style binary semantics)
-- ════════════════════════════════════════════════════

namespace Core.Causal.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Core.Causal (SEM Valuation BoolSEM)
open Core.Causal.SEM (developsToValue causallySufficient)

/-- `BoolSEM`-flavored `developsToValue`: vertex `v` develops to `true`. -/
abbrev developsToTrue (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (v : V) : Prop :=
  developsToValue M s v true

/-- `BoolSEM`-flavored `causallySufficient`: setting `cause = true` develops
    `effect = true`. Matches old `Core.Causal.causallySufficient` semantics. -/
abbrev causallySufficient (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.causallySufficient M s cause true effect true

/-- `BoolSEM`-flavored `manipulates`: cause's value (true vs false) flips
    effect's value under `developDet`. -/
abbrev manipulates (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.manipulates M s cause true false effect

/-- **Direct causal connection**: `cause` is a parent of `effect` in
    the SEM's graph. Pure structural predicate (no `developDet`); fully
    decidable structurally via `Finset.decidableMem`. -/
def hasDirectLaw (M : BoolSEM V) (cause effect : V) : Prop :=
  cause ∈ M.graph.parents effect

instance (M : BoolSEM V) (cause effect : V) :
    Decidable (hasDirectLaw M cause effect) :=
  inferInstanceAs (Decidable (cause ∈ M.graph.parents effect))

/-! ### `developDetOn`-flavored variants

The `causallySufficient` and `completesForEffect` predicates above use the
canonical `developDet` (per-vertex `WellFounded.fix`), which reduces only
through `developDetVtx_unfold` lemmas. Paper-replication study files with
concrete inductive vertex types prefer the `developDetOn`-based variants
below, which iterate a `stepOnceDetOn` on an explicit vertex list and
reduce structurally by `rfl` after `unfold`.

Choose:
- `causallySufficient` / `completesForEffect` — polymorphic, downstream-derivable;
- `causallySufficientOn` / `completesForEffectOn` — concrete, kernel-`rfl`-reducible. -/

/-- `developDetOn`-flavored sufficiency: with `cause = true` under `bg`,
    iterating `stepOnceDetOn` on `vs` `n` times produces `effect = true`. -/
noncomputable def causallySufficientOn (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (bg : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) : Prop :=
  (SEM.developDetOn M vs n (bg.extend cause true)).hasValue effect true

/-- `developDetOn`-flavored completion: sufficiency + but-for. The
    `developDetOn` analogue of `Semantics.Causation.CCSelection.completesForEffect`. -/
noncomputable def completesForEffectOn (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (bg : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) : Prop :=
  causallySufficientOn M vs bg n cause effect ∧
  ¬ (SEM.developDetOn M vs n (bg.extend cause false)).hasValue effect true

noncomputable instance (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (bg : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) :
    Decidable (causallySufficientOn M vs bg n cause effect) := Classical.dec _

noncomputable instance (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (bg : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) :
    Decidable (completesForEffectOn M vs bg n cause effect) := Classical.dec _

-- ════════════════════════════════════════════════════
-- § Nadathur 2024 Def 10b: causallyNecessary (polymorphic)
-- ════════════════════════════════════════════════════

end Core.Causal.BoolSEM

namespace Core.Causal.SEM

variable {V : Type*} {α : V → Type*}

/-- **Consistent supersituation** check (@cite{nadathur-2024} Def 9b):
    `s'` is consistent with `base` under `M` iff every value `s'` fixes
    on a vertex undetermined in `base` agrees with what per-vertex
    development of `base` would produce.

    Refactored from the previous `∀ yv ≠ xv, ¬ hasValue` form: in the
    deterministic case the vertex's value is unique, so the condition
    simplifies to "the s'-fixed value equals the developed value." -/
def isConsistentSuper (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (base s' : Valuation α) : Prop :=
  ∀ (x : V) (xv : α x),
    base.get x = none → s'.get x = some xv → developDetVtx M base x = xv

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (base s' : Valuation α) :
    Decidable (isConsistentSuper M base s') := Classical.dec _

namespace causallyNecessary

/-- **Precondition** (@cite{nadathur-2024} Def 10b): neither
    `cause = xC` nor `effect = xE` is already entailed by `s` under `M`.
    Stated directly via `developDetVtx`. -/
def precondition (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  developDetVtx M s cause ≠ xC ∧ developDetVtx M s effect ≠ xE

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (precondition M s cause xC effect xE) := Classical.dec _

/-- **Achievability** clause (i) of @cite{nadathur-2024} Def 10b.
    Abstract quantification over `Valuation α`: there exists a
    supersituation of `s.extend cause xC` (consistent with the per-vertex
    development) under which `effect` develops to `xE`.

    Concrete proofs supply the existential witness directly (typically
    just the extended valuation itself, or a minimal further extension). -/
def achievable [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  let sCause := s.extend cause xC
  ∃ s' : Valuation α,
    sCause.le s' ∧ isConsistentSuper M sCause s' ∧ developDetVtx M s' effect = xE

noncomputable instance [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (achievable M s cause xC effect xE) := Classical.dec _

/-- **But-for** clause (ii) of @cite{nadathur-2024} Def 10b. Abstract
    quantification: every consistent supersituation of `s` that doesn't
    fix `cause = xC` must fail to develop `effect = xE`.

    Concrete proofs case-analyze on which free vertices `s'` fixes; the
    `isConsistentSuper` clause forces those values to agree with
    `developDetVtx M s`, narrowing the cases to a finite enumeration. -/
def noAlternative [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∀ s' : Valuation α, s.le s' → s'.get cause ≠ some xC →
    isConsistentSuper M s s' → developDetVtx M s' effect ≠ xE

noncomputable instance [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (noAlternative M s cause xC effect xE) := Classical.dec _

end causallyNecessary

/-- **Causal Necessity** (@cite{nadathur-2024} Definition 10b),
    polymorphic over value types.

    ⟨cause, xC⟩ is causally necessary for ⟨effect, xE⟩ relative to `s`
    under `M` iff:
    - **Precondition**: `s` does not develop `cause` to `xC` nor `effect` to `xE`.
    - **(i) Achievability**: some consistent supersituation of `s.extend cause xC`
      develops `effect` to `xE`.
    - **(ii) But-for**: no consistent supersituation of `s` lacking
      `cause = xC` develops `effect` to `xE`.

    Supersedes the simple but-for test from @cite{nadathur-lauer-2020}
    Definition 24. Refactored from the previous `allExtensions`/`freeExtensions`
    enumeration to abstract `Valuation α` quantification — see
    `Counterfactual.lean` module docstring. -/
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

end Core.Causal.SEM

namespace Core.Causal.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Core.Causal (SEM Valuation BoolSEM)

/-- `BoolSEM`-flavored `causallyNecessary`: setting `cause = true` is
    necessary (Def 10b) for `effect = true`. -/
abbrev causallyNecessary (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  SEM.causallyNecessary M s cause true effect true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (causallyNecessary M s cause effect) := Classical.dec _

end Core.Causal.BoolSEM
