import Linglib.Core.Causal.V2.SEM.Basic
import Linglib.Core.Causal.V2.SEM.Bool

/-!
# SEM: Causal Counterfactual Predicates (V2)

Polymorphic counterfactual predicates over a `SEM V α`, plus `BoolSEM`-flavored
aliases for legacy SBH-style binary semantics.

- **`developsToValue M s v x`**: after developing `s`, vertex `v` has value `x`.
  Replaces the old `developsToTrue` (Bool-specialized) with a polymorphic version.

- **`causallySufficient M s cause xC effect xE`**: extending `s` with `xC` at
  `cause` then developing produces `xE` at `effect`. Polymorphic generalization
  of @cite{nadathur-lauer-2020} Definition 23.

**Necessity** is *not* exposed as a Core primitive. The 2026 canonical
literature on causal-verb semantics (@cite{nadathur-2024} Def 10b,
@cite{cao-white-lassiter-2025} graded ALT, @cite{beller-gerstenberg-2025}
counterfactual simulation) has moved past simple Lewis but-for. Each
necessity flavor is theory-specific:
- Lewis-style but-for: `¬ causallySufficient M s cause xC_alt effect xE`
  (one-liner — define in `Phenomena/Causation/Studies/Lewis1973.lean`)
- Nadathur 2024 Def 10b: precondition + achievable + supersituation
  (port lazily alongside `Theories/Semantics/Causation/Necessity.lean` migration)
- CWL graded: not a discrete predicate (graded ALT measure)

`BoolSEM`-namespace aliases specialize the polymorphic predicates to
`α := fun _ => Bool` with `xC = true`, `xE = true` (legacy SBH semantics).

## Computability

`developDet` is `noncomputable` (cascading from `PMF.pure` and `Finset.toList`),
so all predicates here are `noncomputable`. `Decidable` instances are provided
via `Classical.dec`; consumers wanting `decide` to reduce concretely on small
SEMs should use `native_decide` or supply structural proofs. Matches the
mathlib idiom for probability-flavored predicates (`Mathlib/Probability/`).
-/

namespace Core.Causal.V2.SEM

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
-- § Probabilistic sufficiency (PMF-canonical)
-- ════════════════════════════════════════════════════

/-! Mathlib-canonical probabilistic SUF: probability that `effect` takes
value `xE` under `do(cause := xC)` — the @cite{cao-white-lassiter-2025}
graded measure. PMF-valued via `develop`; deterministic SEMs collapse to
{0,1} via `develop_eq_pure_of_deterministic`. -/

/-- **Probabilistic sufficiency** (@cite{cao-white-lassiter-2025}):
    probability that `effect` takes value `xE` after Pearl-intervening
    to set `cause := xC`. Defined via the canonical PMF-valued
    `develop`; reduces to a {0,1} indicator under `IsDeterministic` via
    `probabilisticSuf_of_deterministic`. -/
noncomputable def probabilisticSuf [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) : ENNReal :=
  ∑' v : Valuation α, if v.hasValue effect xE
                      then ((M.intervene cause xC).develop s) v
                      else 0

/-- Bridge: under `IsDeterministic`, `probabilisticSuf` is the {0,1}
    indicator of whether the deterministic intervened development hits
    `effect = xE`. -/
theorem probabilisticSuf_of_deterministic
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    probabilisticSuf M s cause xC effect xE =
      if ((M.intervene cause xC).developDet s).hasValue effect xE then 1 else 0 := by
  unfold probabilisticSuf
  rw [develop_eq_pure_of_deterministic]
  -- Goal: ∑' v, if v.hasValue effect xE then PMF.pure (developDet ...) v else 0 = if ...
  -- PMF.pure x assigns 1 to x and 0 elsewhere
  rw [tsum_eq_single ((M.intervene cause xC).developDet s)
      (fun v hv => by
        rw [PMF.pure_apply_of_ne _ _ hv]; simp)]
  by_cases h : ((M.intervene cause xC).developDet s).hasValue effect xE
  · simp [h, PMF.pure_apply_self]
  · simp [h]

-- ════════════════════════════════════════════════════
-- § Nadathur 2024 Def 10b: causallyNecessary (BoolSEM only)
-- ════════════════════════════════════════════════════

/-! Port of @cite{nadathur-2024} Definition 10b to V2. Specialized to
    `BoolSEM` (the binary substrate the original definition was given on);
    polymorphic generalization to multi-valued α can come if a consumer
    needs it. -/

end Core.Causal.V2.SEM

-- ════════════════════════════════════════════════════
-- § BoolSEM specializations (legacy SBH-style binary semantics)
-- ════════════════════════════════════════════════════

namespace Core.Causal.V2.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Core.Causal.V2 (SEM Valuation BoolSEM)
open Core.Causal.V2.SEM (developsToValue causallySufficient)

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

-- ════════════════════════════════════════════════════
-- § Nadathur 2024 Def 10b: causallyNecessary (polymorphic)
-- ════════════════════════════════════════════════════

end Core.Causal.V2.BoolSEM

namespace Core.Causal.V2.SEM

variable {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V]

/-- All `α`-extensions of a valuation over a list of vertices. Each
    vertex can be left undetermined, or set to any value of `α v`.
    Polymorphic generalization of the Bool-specific `allExtensionsBool`. -/
noncomputable def allExtensions [∀ v, Fintype (α v)]
    (s : Valuation α) : List V → List (Valuation α)
  | [] => [s]
  | v :: vs =>
    let rest := allExtensions s vs
    rest ++ ((Fintype.elems : Finset (α v)).toList.flatMap
              fun x => rest.map (·.extend v x))

/-- Free-extension list: vertices to range over in supersituation
    quantification. Excludes `effect` and any vertex already determined
    in `base`. Noncomputable because of `Finset.toList`. -/
noncomputable def freeExtensions [DecidableValuation α]
    (base : Valuation α) (effect : V) : List V :=
  (Fintype.elems : Finset V).toList.filter fun v =>
    decide (v ≠ effect ∧ (base.get v).isNone)

/-- **Consistent supersituation** check (@cite{nadathur-2024} Def 9b),
    polymorphic over value types: `s'` is a consistent supersituation
    of `base` iff for each vertex `x` undetermined in `base` whose value
    `s'` sets, that value agrees with what `developDet` would produce
    from `base` alone. -/
noncomputable def isConsistentSuper [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (base s' : Valuation α) : Prop :=
  ∀ (x : V) (xv : α x),
    base.get x = none → s'.get x = some xv →
      ∀ (yv : α x), yv ≠ xv → ¬ (M.developDet base).hasValue x yv

noncomputable instance [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (base s' : Valuation α) :
    Decidable (isConsistentSuper M base s') := Classical.dec _

namespace causallyNecessary

/-- **Precondition** (@cite{nadathur-2024} Def 10b): neither
    `cause = xC` nor `effect = xE` is already entailed by `s` under `M`. -/
noncomputable def precondition [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ¬ (M.developDet s).hasValue cause xC ∧
  ¬ (M.developDet s).hasValue effect xE

noncomputable instance [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (precondition M s cause xC effect xE) := Classical.dec _

/-- **Achievability** clause (i) of @cite{nadathur-2024} Def 10b. -/
noncomputable def achievable [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  let sCause := s.extend cause xC
  ∃ s' ∈ allExtensions sCause (freeExtensions sCause effect),
    isConsistentSuper M sCause s' ∧
    (M.developDet s').hasValue effect xE

noncomputable instance [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (achievable M s cause xC effect xE) := Classical.dec _

/-- **But-for** clause (ii) of @cite{nadathur-2024} Def 10b. -/
noncomputable def noAlternative [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∀ s' ∈ allExtensions s (freeExtensions s effect),
    isConsistentSuper M s s' →
    (M.developDet s').hasValue effect xE →
    (M.developDet s').hasValue cause xC

noncomputable instance [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (noAlternative M s cause xC effect xE) := Classical.dec _

end causallyNecessary

/-- **Causal Necessity** (@cite{nadathur-2024} Definition 10b),
    polymorphic over value types.

    ⟨cause, xC⟩ is causally necessary for ⟨effect, xE⟩ relative to `s`
    under `M` iff:
    - **Precondition**: `s ⊭ cause = xC` and `s ⊭ effect = xE`
    - **(i) Achievability**: `s.extend cause xC` has a consistent
      supersituation achieving `effect = xE`
    - **(ii) But-for**: no consistent supersituation of `s` achieves
      `effect = xE` without `cause = xC`

    Supersedes the simple but-for test from @cite{nadathur-lauer-2020}
    Definition 24. -/
noncomputable def causallyNecessary [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  causallyNecessary.precondition M s cause xC effect xE ∧
  causallyNecessary.achievable M s cause xC effect xE ∧
  causallyNecessary.noAlternative M s cause xC effect xE

noncomputable instance [∀ v, Fintype (α v)] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallyNecessary M s cause xC effect xE) := Classical.dec _

end Core.Causal.V2.SEM

namespace Core.Causal.V2.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Core.Causal.V2 (SEM Valuation BoolSEM)

/-- `BoolSEM`-flavored `causallyNecessary`: setting `cause = true` is
    necessary (Def 10b) for `effect = true`. -/
abbrev causallyNecessary (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  SEM.causallyNecessary M s cause true effect true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (causallyNecessary M s cause effect) := Classical.dec _

end Core.Causal.V2.BoolSEM
